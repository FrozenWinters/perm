#lang racket

; As a bonus implementation, here is the calculation of the n-simplex types for (Sing X) where:

; Sing : (X : Type) → SST
; Z (Sing X) = X
; S (Sing X) A = Singᵈ X (λ B → Path X A B) 

(struct XVar (level) #:transparent)
(struct αVar (level) #:transparent)
(struct ΓVar (index) #:transparent)
(struct iVar (index) #:transparent)

(struct Lam (body) #:transparent)
(struct Line (body) #:transparent)
(struct App (fun arg) #:transparent)
(struct iApp (fun arg) #:transparent)
(struct Path (space lhs rhs) #:transparent)
(struct PathP (line lhs rhs) #:transparent)

(define (weaken-ren ρ)
  (λ (n) (if (zero? n) 0 (add1 (ρ (sub1 n))))))

(define (rename expr ρC ρI)
  (match expr
    [(? symbol?) expr]
    [(XVar n) (XVar n)]
    [(αVar n) (αVar n)]
    [(ΓVar n) (ΓVar (ρC n))]
    [(iVar n) (iVar (ρI n))]
    [(Lam t) (Lam (rename t (weaken-ren ρC) ρI))]
    [(Line t) (Line (rename t ρC (weaken-ren ρI)))]
    [(App t s) (App (rename t ρC ρI) (rename s ρC ρI))]
    [(iApp t i) (iApp (rename t ρC ρI) (rename i ρC ρI))]
    [(Path X e1 e2) (Path (rename X ρC ρI) (rename e1 ρC ρI) (rename e2 ρC ρI))]
    [(PathP X e1 e2) (PathP (rename X ρC ρI) (rename e1 ρC ρI) (rename e2 ρC ρI))]))

(define (weaken-sub ρ)
  (λ (n) (if (zero? n) (ΓVar 0) (rename (ρ (sub1 n)) add1 (λ (x) x)))))

(define (weaken-sub-i ρ)
  (λ (n) (rename (ρ n) (λ (x) x) add1)))

(define (subst expr ρ)
  (match expr
    [(? symbol?) expr]
    [(ΓVar n) (ρ n)]
    [(iVar n) (iVar n)]
    [(Lam t) (Lam (subst t (weaken-sub ρ)))]
    [(Line t) (Line (subst t (weaken-sub-i ρ)))]
    [(App t s) (App (subst t ρ) (subst s ρ))]
    [(iApp t i) (iApp (subst t ρ) (subst i ρ))]
    [(Path X e1 e2) (Path (subst X ρ) (subst e1 ρ) (subst e2 ρ))]
    [(PathP X e1 e2) (PathP (subst X ρ) (subst e1 ρ) (subst e2 ρ))]))

(define (shift expr t)
  (subst expr (λ (n) (if (zero? n) t (ΓVar (sub1 n))))))

(define (norm expr)
  (match expr
    [(? symbol?) expr]
    [(ΓVar n) (ΓVar n)]
    [(iVar n) (iVar n)]
    [(Lam t) (Lam (norm t))]
    [(Line t) (Line (norm t))]
    [(App t s)
     (let
         ([tp (norm t)]
          [sp (norm s)])
       (match tp
         [(Lam g) (norm (shift g sp))]
         [else (App tp sp)]))]
    [(iApp t i) (iApp (norm t) (norm i))]
    [(Path X e1 e2) (Path (norm X) (norm e1) (norm e2))]
    [(PathP X e1 e2) (PathP (norm X) (norm e1) (norm e2))]))

(define (evens expr ρ)
  (match expr
    [(XVar n) (XVar (* 2 n))]
    [(αVar n) (αVar (* 2 n))]
    [(ΓVar n) (ΓVar (ρ n))]
    [(iVar n) (iVar n)]
    [(Lam t) (Lam (evens t (weaken-ren ρ)))]
    [(Line t) (Line (evens t ρ))]
    [(App t s) (App (evens t ρ) (evens s ρ))]
    [(iApp t i) (iApp (evens t ρ) (evens i ρ))]
    [(Path X e1 e2) (Path (evens X ρ) (evens e1 ρ) (evens e2 ρ))]
    [(PathP X e1 e2) (PathP (evens X ρ) (evens e1 ρ) (evens e2 ρ))]))

(define (display expr)
  (match expr
    [(XVar n) (XVar (add1 (* 2 n)))]
    [(αVar n) (αVar (add1 (* 2 n)))]
    [(ΓVar n) (ΓVar (* 2 n))]
    [(Lam t) (Lam (Lam (display t)))]
    [(Line t) (Line (display t))]
    [(App t s) (App (App (display t) (evens s (λ (n) (add1 (* 2 n))))) (display s))]
    [(iApp t i) (iApp (display t) i)]
    [(Path X e1 e2)
     (Lam (PathP (Line (App (rename (display X) add1 add1) (iApp (ΓVar 0) (iVar 0))))
                 (rename (display e1) add1 (λ (x) x))
                 (rename (display e2) add1 (λ (x) x))))]
    [(PathP (Line X) e1 e2)
     (Lam (PathP (Line (App (rename (display X) add1 (λ (x) x)) (iApp (ΓVar 0) (iVar 0))))
                 (rename (display e1) add1 (λ (x) x))
                 (rename (display e2) add1 (λ (x) x))))]))

(define (décalage σ)
  (match σ
    ['() '()]
    [(cons t σ) (cons (evens t (λ (n) (add1 (* 2 n)))) (cons (display t) (décalage σ)))]))

(define (eval expr Xenv αenv)
  (match expr
    [(? symbol?) expr]
    [(XVar n) (list-ref Xenv n)]
    [(αVar n) (list-ref αenv n)]
    [(ΓVar n) (ΓVar n)]
    [(iVar n) (iVar n)]
    [(Lam t) (Lam (eval t Xenv αenv))]
    [(Line t) (Line (eval t Xenv αenv))]
    [(App t s) (App (eval t Xenv αenv) (eval s Xenv αenv))]
    [(iApp t i) (iApp (eval t Xenv αenv) (eval i Xenv αenv))]
    [(Path X e1 e2) (Path (eval X Xenv αenv) (eval e1 Xenv αenv) (eval e2 Xenv αenv))]
    [(PathP X e1 e2) (PathP (eval X Xenv αenv) (eval e1 Xenv αenv) (eval e2 Xenv αenv))]))

(define (update-α A αgen)
  (append αgen
          (list (list (integer->char (+ 65 A))))
          (map (λ (l) (cons (integer->char (+ 65 A)) l)) αgen)))

(define (extract-α A αgen)
  (map
   (λ (l) (string->symbol (apply string (reverse l))))
   (cons (list (integer->char (+ 65 A)))
         (map (λ (l) (cons (integer->char (+ 65 A)) l)) αgen))))

(define (itr n A SX Xenv αgen)
  (cond
    [(zero? n)
     (norm
      (foldl (λ (arg expr) (App expr arg))
             (last Xenv)
             (reverse (rest (reverse (extract-α A αgen))))))]
    [else
     (let ([αbatch (extract-α A αgen)])
       (itr
        (sub1 n)
        (add1 A)
        (décalage SX)
        (append Xenv (map (λ (X) (norm (eval X Xenv αbatch))) SX))
        (update-α A αgen)))]))

(define (Xn n)
  (itr n
       0
       (list (Lam (Path (XVar 0) (αVar 0) (ΓVar 0))))
       '(X)
       '()))

(define (skip ρ)
  (λ (n) (if (< n 0) (add1 (ρ n)) (ρ n))))

(define (pretty-print-expr e ρ)
  (match e
    [(? symbol? x) (symbol->string x)]
    [(App e1 e2) (format "~a ~a" (pretty-print-expr e1 ρ) (pretty-print-expr e2 ρ))]
    [(iApp e i) (format "(~a ~a)" (pretty-print-iapp e ρ) (pretty-print-expr i ρ))]
    [(iVar n) (string (integer->char (+ 105 (ρ n))))]
    [(Line e) (format "(λ ~a. ~a)" (string (integer->char (+ 105 (ρ -1)))) (pretty-print-expr e (λ (n) (ρ (sub1 n)))))]
    [(Path X a b) (format "Path ~a ~a ~a" (pretty-print-expr X ρ) (pretty-print-expr a ρ) (pretty-print-expr b ρ))]
    [(PathP X a b) (format "PathP ~a ~a ~a" (pretty-print-expr X ρ) (pretty-print-expr a (skip ρ)) (pretty-print-expr b (skip ρ)))]))

(define (pretty-print-iapp e ρ)
  (match e
    [(iApp e i) (format "~a ~a" (pretty-print-iapp e ρ) (pretty-print-expr i ρ))]
    [else (pretty-print-expr e ρ)]))

(define (simplex-type n)
  (displayln (pretty-print-expr (Xn n) (λ (n) (sub1 (- n))))))

(simplex-type 0)
(simplex-type 1)
(simplex-type 2)
(simplex-type 3)
(simplex-type 4)
(simplex-type 5)