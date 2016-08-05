module notes where

Subset : Set → Set₁
Subset(X) = X → Set

_∈_ : ∀ {X} → X → Subset(X) → Set
(x ∈ A) = A(x)

_⊆_ : ∀ {X} → Subset(X) → Subset(X) → Set
(A ⊆ B) = ∀ x → (x ∈ A) → (x ∈ B)

record Inhabited {X} (S : Subset(X)) : Set where
  constructor _,_
  field witness : X
  field witness-in : (witness ∈ S)
  
Rel : Set → Set₁
Rel(X) = X → X → Set

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
(zero + n) = n
(succ m + n) = succ(m + n)

data _^_ (X : Set) : ℕ → Set where
  nil : (X ^ zero)
  _∷_ : ∀ {n} → X → (X ^ n) → (X ^ succ(n))

data _≡_ {D : Set} (d : D) : D → Set where
  refl : (d ≡ d)

sym : ∀ {D} {d e : D} → (d ≡ e) → (e ≡ d)
sym refl = refl

trans : ∀ {D} {d e f : D} → (d ≡ e) → (e ≡ f) → (d ≡ f)
trans refl refl = refl

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

¬ : Set → Set
¬(X) = (X → ⊥)

contradiction : ∀ {X : Set} → ⊥ → X
contradiction ()

data _∨_ (X Y : Set) : Set where
  in₁ : X → (X ∨ Y)
  in₂ : Y → (X ∨ Y)

_∪_ : ∀ {X} → Subset(X) → Subset(X) → Subset(X)
(A ∪ B) x = (x ∈ A) ∨ (x ∈ B)

record _∧_ (X Y : Set) : Set where
  constructor _,_
  field proj₁ : X
  field proj₂ : Y
  
_∩_ : ∀ {X} → Subset(X) → Subset(X) → Subset(X)
(A ∩ B) x = (x ∈ A) ∧ (x ∈ B)

All : ∀ {X n} → Subset(X) → Subset(X ^ n)
All(S) nil = ⊤
All(S) (x ∷ xs) = (x ∈ S) ∧ (xs ∈ All(S))

All-resp-⊆ : ∀ {X} {A B : Subset(X)} {n} → (A ⊆ B) → (All {n = n} (A) ⊆ All(B))
All-resp-⊆ A⊆B nil tt = tt
All-resp-⊆ A⊆B (x ∷ xs) (x∈A , xs∈A) = (A⊆B x x∈A , All-resp-⊆ A⊆B xs xs∈A)

All-resp-∩ : ∀ {X} {A B : Subset(X)} {n} → ((All {n = n} (A) ∩ All(B)) ⊆ All(A ∩ B))
All-resp-∩ nil (tt , tt) = tt
All-resp-∩ (d ∷ ds) ((d∈A , ds∈A) , (d∈B , ds∈B)) = ((d∈A , d∈B) , (All-resp-∩ ds (ds∈A , ds∈B)))

record DirectedGraph(D : Set) : Set₁ where

  field _⇒_ : Rel(D)

  data _⇒+_ (d e : D) : Set where
    ⇒-impl-⇒+ : (d ⇒ e) → (d ⇒+ e)
    ⇒⇒+-impl-⇒+ : ∀ {f} → (d ⇒ f) → (f ⇒+ e) → (d ⇒+ e)

record Forest(D : Set) : Set₁ where

  field DG : DirectedGraph(D)
  open DirectedGraph DG public

  field ⇒-parent-uniq : ∀ {d e f} → (d ⇒ f) → (e ⇒ f) → (d ≡ e)
  field ⇒-acyclic : ∀ {d} → (d ⇒+ d) → ⊥
  
record PartialOrder(D : Set) : Set₁ where

  field _≤_ : Rel(D)
  field ≤-refl : ∀ {d} → (d ≤ d)
  field ≤-trans : ∀ {d e f} → (d ≤ e) → (e ≤ f) → (d ≤ f)
  field ≤-asym : ∀ {d e} → (d ≤ e) → (e ≤ d) → (d ≡ e)

  field _≤?_ : ∀ d e → ((d ≤ e) ∨ ¬(d ≤ e))
  
  _<_ : Rel(D)
  d < e = (d ≤ e) ∧ ¬(d ≡ e)

  ≡-impl-≤ : ∀ {d e} → (d ≡ e) → (d ≤ e)
  ≡-impl-≤ refl = ≤-refl

  <-trans-≤ : ∀ {d e f} → (d < e) → (e ≤ f) → (d < f)
  <-trans-≤ (d≤e , d≠e) e≤f = (≤-trans d≤e e≤f , (λ d≡f → d≠e (trans d≡f (≤-asym (≤-trans (≡-impl-≤ (sym d≡f)) d≤e) e≤f))))

  <-trans : ∀ {d e f} → (d < e) → (e < f) → (d < f)
  <-trans d<e (e≤f , e≠f) = <-trans-≤ d<e e≤f

  <-impl-≱ : ∀ {d e} → (d < e) → ¬(e ≤ d)
  <-impl-≱ (d≤e , d≠e) e≤d = d≠e (≤-asym d≤e e≤d)
  
  Past : D → Subset(D)
  Past(d) e = (e < d)

  Decreasing : ∀ {n} → Subset(D ^ n)
  Decreasing nil = ⊤
  Decreasing (d ∷ ds) = (ds ∈ (All(Past(d)) ∩  Decreasing))

  _≤*_ : ∀ {n} → Rel(D ^ n)
  nil ≤* nil = ⊤
  (d ∷ ds) ≤* (e ∷ es) = (d ≤ e) ∧ (ds ≤* es)

  Min : Subset(D) → Subset(D)
  Min(S) d = (d ∈ S) ∧ (∀ e → (e ∈ S) → (d ≤ e))

  Max : Subset(D) → Subset(D)
  Max(S) d = (d ∈ S) ∧ (∀ e → (e ∈ S) → (e ≤ d))

  Max* : ∀ {n} → Subset(D ^ n) → Subset(D ^ n)
  Max*(S) ds = (ds ∈ S) ∧ (∀ es → (es ∈ S) → (es ≤* ds))

record FiniteTotalOrder(D : Set) : Set₁ where

  field PO : PartialOrder(D)
  open PartialOrder PO public

  field min_∵_ : ∀ (S : Subset(D)) → Inhabited(S) → Inhabited(Min(S))
  field max_∵_ : ∀ (S : Subset(D)) → Inhabited(S) → Inhabited(Max(S))

  ≤-total : ∀ d e → (d ≤ e) ∨ (e < d)
  ≤-total d e with d ≤? e
  ≤-total d e | in₁ d≤e = in₁ d≤e
  ≤-total d e | in₂ d≰e with max (λ f → (d ≡ f) ∨ (e ≡ f)) ∵ (d , in₁ refl)
  ≤-total d e | in₂ d≰e | .d , (in₁ refl , d-max) = in₂ (e≤d , e≠d) where

    e≤d = d-max e (in₂ refl)
    e≠d = λ e=d → d≰e (≡-impl-≤ (sym e=d))
    
  ≤-total d e | in₂ d≰e | .e , (in₂ refl , e-max) = contradiction (d≰e (e-max d (in₁ refl)))
  
  Max-hd : ∀ S {n} d (ds : D ^ n) →
    ((d ∷ ds) ∈ Max*(Decreasing ∩ All(S))) →
    (d ∈ Max(S))
  Max-hd S d ds (((d>ds , ds↓) , (d∈S , ds∈S)) , d∷ds-max) = (d∈S , d-max) where

    d-max : ∀ e → (e ∈ S) → (e ≤ d)
    d-max e e∈S with ≤-total e d
    d-max e e∈S | in₁ e≤d = e≤d
    d-max e e∈S | in₂ d<e with d∷ds-max (e ∷ ds) ((All-resp-⊆ (λ f d<f → <-trans d<f d<e) ds d>ds , ds↓) , (e∈S , ds∈S))
    d-max e e∈S | in₂ d<e | (e≤d , ds≤ds) = e≤d

  Max-tl : ∀ S {n} d (ds : D ^ n) →
    ((d ∷ ds) ∈ Max*(Decreasing ∩ All(S))) →
    (ds ∈ Max*(All(Past(d)) ∩ (Decreasing ∩ All(S))))
  Max-tl S d ds (((d>ds , ds↓) , (d∈S , ds∈S)) , d∷ds-max) = ((d>ds , (ds↓ , ds∈S)) , ds-max) where

    ds-max : ∀ es → (es ∈ (All(Past(d)) ∩ (Decreasing ∩ All(S)))) → (es ≤* ds)
    ds-max es (d>es , (es↓ , es∈S)) with d∷ds-max (d ∷ es) ((d>es , es↓) , (d∈S , es∈S)) 
    ds-max es (d>es , (es↓ , es∈S)) | (d≤d , es≤ds) = es≤ds
  
record Equivalence(D : Set) : Set₁ where

  field _~_ : Rel(D)
  field ~-refl : ∀ {d} → (d ~ d)
  field ~-trans : ∀ {d e f} → (d ~ e) → (e ~ f) → (d ~ f)
  field ~-sym : ∀ {d e} → (d ~ e) → (e ~ d)

  field _~?_ : ∀ d e → ((d ~ e) ∨ ¬(d ~ e))

  ≡-impl-~ : ∀ {d e} → (d ≡ e) → (d ~ e)
  ≡-impl-~ refl = ~-refl
  
record NavigationHistory(D : Set) : Set₁ where

  field A : Subset(D)
  field Fo : Forest(D)
  field FTO : FiniteTotalOrder(D)
  field Eq : Equivalence(D)

  open FiniteTotalOrder FTO public
  open Forest Fo public
  open Equivalence Eq public

  field active : D → D
  field active-A : ∀ d → A(active d)
  field active-~ : ∀ d → (active d ~ d)
  field active-uniq : ∀ d e → A(e) → (d ~ e) → (e ≡ active d)
  
  field ⇒-trans-~ : ∀ {d e f} → (d ⇒ e) → (e ~ f) → (d ⇒ f)

  _≲_ : Rel(D)
  (d ≲ e) = (d < e) ∧ (d ~ e)
  
  ≲-trans : ∀ {d e f} → (d ≲ e) → (e ≲ f) → (d ≲ f)
  ≲-trans (d<e , d~e) (e<f , e~f) = ((<-trans d<e e<f) , (~-trans d~e e~f))

  ≲-impl-< : ∀ {d e} → (d ≲ e) → (d < e)
  ≲-impl-< (d<e , d~e) = d<e

  ≲-impl-~ : ∀ {d e} → (d ≲ e) → (d ~ e)
  ≲-impl-~ (d<e , d~e) = d~e
  
  SessionPast : D → Subset(D)
  SessionPast(d) e = (e ≲ d)

  JointSessionPast : Subset(D)
  JointSessionPast d = Inhabited (λ a → (a ∈ A) ∧ (d ≲ a))

  CanGoBack : Subset(D)
  CanGoBack d = Inhabited(SessionPast(d))
  
  BackTarget : Subset(D)
  BackTarget = Max(A ∩ CanGoBack)

  BackTarget* : ∀ {n} → Subset(D ^ n)
  BackTarget* = Max*(Decreasing ∩ All((A ∪ JointSessionPast) ∩ CanGoBack))
  
open NavigationHistory public using (BackTarget ; BackTarget*)

_traverse-to_ : ∀ {D} → NavigationHistory(D) → D → NavigationHistory(D)
H traverse-to d = H′ where

  D = _
  open NavigationHistory H

  A′ : Subset(D)
  A′(e) = (¬(d ~ e) ∧ A(e)) ∨ (d ≡ e)

  active′ : D → D
  active′ e with (d ~? e)
  active′ e | in₁ d~e = d
  active′ e | in₂ ¬d~e = active e

  active′-A′ :  ∀ d → A′(active′ d)
  active′-A′ e with (d ~? e)
  active′-A′ e | in₁ d~e = in₂ refl
  active′-A′ e | in₂ ¬d~e = in₁ ((λ d~ae → ¬d~e (~-trans d~ae (active-~ e))) , active-A e)

  active′-~ :  ∀ d → (active′ d ~ d)
  active′-~ e with (d ~? e)
  active′-~ e | in₁ d~e = d~e
  active′-~ e | in₂ ¬d~e = active-~ e

  active′-uniq : ∀ d e → A′ e → (d ~ e) → (e ≡ active′ d)
  active′-uniq e f (in₁ (¬d~f , f∈A)) e~f with (d ~? e)
  active′-uniq e f (in₁ (¬d~f , f∈A)) e~f | in₁ d~e = contradiction (¬d~f (~-trans d~e e~f))
  active′-uniq e f (in₁ (¬d~f , f∈A)) e~f | in₂ ¬d~e = active-uniq e f f∈A e~f
  active′-uniq e .d (in₂ refl) e~d with (d ~? e)
  active′-uniq e .d (in₂ refl) e~d | in₁ d~e = refl
  active′-uniq e .d (in₂ refl) e~d | in₂ ¬d~e = contradiction (¬d~e (~-sym e~d))
  
  H′ = record { A = A′ ; Fo = Fo ; FTO = FTO ; Eq = Eq
              ; active = active′ ; active-A = active′-A′ ; active-~ = active′-~ ; active-uniq = active′-uniq
              ; ⇒-trans-~ = ⇒-trans-~ }

_traverses-to_ : ∀ {D n} → NavigationHistory(D) → (D ^ n) → NavigationHistory(D)
(H traverses-to nil) = H
(H traverses-to (d ∷ ds)) = (H traverse-to d) traverses-to ds

_traverse-from_∵_ : ∀ {D} (H : NavigationHistory(D)) d →
  let open NavigationHistory H in 
  (d ∈ CanGoBack) →
  NavigationHistory(D)
(H traverse-from d ∵ d∈CGB) with max(SessionPast(d)) ∵ d∈CGB where open NavigationHistory H
(H traverse-from d ∵ d∈CGB) | (c , _) = (H traverse-to c)

 -- _traverses-from_∵_ : ∀ {D n} (H : NavigationHistory(D)) (ds : D ^ n) →
--   let open NavigationHistory H in 
--   (ds ∈ All(CanGoBack)) →
--   NavigationHistory(D)
-- (H traverses-from ds ∵ ds∈CGB) = (H traverses-to (prev*(ds) ∵ ds∈CGB)) where open NavigationHistory H

BT-hd : ∀ {D} {H : NavigationHistory(D)} {n} d (ds : D ^ n) →
  ((d ∷ ds) ∈ BackTarget*(H)) →
  (d ∈ BackTarget(H))
BT-hd {D} {H} {n} d ds d∷ds∈BT with Max-hd ((A ∪ JointSessionPast) ∩ CanGoBack) d ds d∷ds∈BT where open NavigationHistory H
BT-hd {D} {H} {n} d ds d∷ds∈BT | ((in₁ d∈A , d∈CGB), d-max′) = ((d∈A , d∈CGB) , d-max) where

  open NavigationHistory H

  d-max : ∀ e → (e ∈ (A ∩ CanGoBack) → (e ≤ d))
  d-max e (e∈A , e∈CGB) = d-max′ e ((in₁ e∈A) , e∈CGB)

BT-hd {D} {H} {n} d ds d∷ds∈BT | ((in₂ (a , (a∈A , (d<a , d~a))) , d∈CGB), d-max) = contradiction (<-impl-≱ d<a (d-max a ((in₁ a∈A) , (d , (d<a , d~a))))) where open NavigationHistory H

BT-tl : ∀ {D} {H : NavigationHistory(D)} {n} d d∈CGB (ds : D ^ n) →
  ((d ∷ ds) ∈ BackTarget*(H)) →
  (ds ∈ BackTarget*(H traverse-from d ∵ d∈CGB))
BT-tl {D} {H} {n} d d∈CGB ds d∷ds∈BT with Max-tl ((A ∪ JointSessionPast) ∩ CanGoBack) d ds d∷ds∈BT where open NavigationHistory H
BT-tl {D} {H} {n} d d∈CGB ds d∷ds∈BT | ((d>ds , (ds↓ , ds∈BT′)) , ds-max′) with max(SessionPast(d)) ∵ d∈CGB where open NavigationHistory H 
BT-tl {D} {H} {n} d d∈CGB ds d∷ds∈BT | ((d>ds , (ds↓ , ds∈BT′)) , ds-max′) | (c , ((c<d , c~d) , c-max)) = ((ds↓ , ds∈BT) , ds-max) where

  open NavigationHistory H
  open NavigationHistory (H traverse-to c) using () renaming (A to A′ ; JointSessionPast to JointSessionPast′)

  d∈A : (d ∈ A)
  d∈A with BT-hd {H = H} d ds d∷ds∈BT
  d∈A | ((d∈A , _) , _) = d∈A

  d-max : ∀ e → (e ∈ (A ∩ CanGoBack) → (e ≤ d))
  d-max with BT-hd {H = H} d ds d∷ds∈BT
  d-max | ((_ , _) , d-max) = d-max

  lemma : (Past(d) ∩ ((A ∪ JointSessionPast) ∩ CanGoBack)) ⊆ ((A′ ∪ JointSessionPast′) ∩ CanGoBack)
  lemma e  (e<d , (_                              , e∈CGB)) with c ~? e
  lemma e  (e<d , (_                              , e∈CGB)) | in₁ c~e with ≤-total c e
  lemma e  (e<d , (_                              , e∈CGB)) | in₁ c~e | in₁ c≤e with ≤-asym c≤e (c-max e (e<d , ~-trans (~-sym c~e) c~d))
  lemma ._ (e<d , (_                              , e∈CGB)) | in₁ c~e | in₁ c≤e | refl = ((in₁ (in₂ refl)) , e∈CGB)
  lemma e  (e<d , (_                              , e∈CGB)) | in₁ c~e | in₂ e<c = (in₂ (_ , (in₂ refl , (e<c , ~-sym c~e))) , e∈CGB)
  lemma e  (e<d , (in₁ e∈A                        , e∈CGB)) | in₂ c≁e = ((in₁ (in₁ (c≁e , e∈A))) , e∈CGB)
  lemma e  (e<d , (in₂ (a , (a∈A ,  (e<a , e~a))) , e∈CGB)) | in₂ c≁e = (in₂ (a , (in₁ ((λ c~a → c≁e (~-trans c~a (~-sym e~a))) , a∈A) , (e<a , e~a))) , e∈CGB)
  
  lemma′ : ((A′ ∪ JointSessionPast′) ∩ CanGoBack) ⊆ ((A ∪ JointSessionPast) ∩ CanGoBack)
  lemma′ e  (in₁ (in₁ (c≁e , e∈A)) , e∈CGB) = ((in₁ e∈A) , e∈CGB)
  lemma′ ._ (in₁ (in₂ refl) , c∈CGB) = ((in₂ (d , (d∈A , (c<d , c~d)))) , c∈CGB)
  lemma′ e (in₂ (a , (in₁ (c≁a , a∈A) , e≲a)) , e∈CGB) = (in₂ (a , (a∈A , e≲a)) , e∈CGB)
  lemma′ e (in₂ (._ , (in₂ refl , e≲c)) , e∈CGB) = ((in₂ (d , (d∈A , ≲-trans e≲c (c<d , c~d)))) , e∈CGB)
  
  lemma″ : ((A′ ∪ JointSessionPast′) ∩ CanGoBack) ⊆ (Past(d))
  lemma″ e  (in₁ (in₁ (c≁e , e∈A)) , e∈CGB) = (d-max e (e∈A , e∈CGB) , (λ e≡d → c≁e (~-trans c~d (≡-impl-~ (sym e≡d)))))
  lemma″ ._ (in₁ (in₂ refl) , c∈CGB) = c<d
  lemma″ e (in₂ (a , (in₁ (c≁a , a∈A) , e≲a)) , e∈CGB) = <-trans-≤ (≲-impl-< e≲a) (d-max a (a∈A , (e , e≲a)))
  lemma″ e (in₂ (._ , (in₂ refl , (e<c , e~c))) , e∈CGB) = <-trans e<c c<d
  
  ds∈BT : ds ∈ All((A′ ∪ JointSessionPast′) ∩ CanGoBack)
  ds∈BT = All-resp-⊆ lemma ds (All-resp-∩ ds (d>ds , ds∈BT′))
  
  ds-max : ∀ es → (es ∈ (Decreasing ∩ All((A′ ∪ JointSessionPast′) ∩ CanGoBack))) → (es ≤* ds)
  ds-max es (es↓ , es∈BT′) = ds-max′ es (All-resp-⊆ lemma″ es es∈BT′ , (es↓ , All-resp-⊆ lemma′ es es∈BT′))
  
