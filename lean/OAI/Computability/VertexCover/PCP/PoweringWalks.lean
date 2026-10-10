import Mathlib

namespace OAI

                                                                                      

namespace UniqueGames.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

@[simp] theorem rot_rot (G : PortGraph V D) (e : Edge V D) :
    G.rot (G.rot e) = e := G.rot_involutive e

def walkEnd (G : PortGraph V D) : V → List D → V
  | v, [] => v
  | v, d :: ds => walkEnd G (next G v d) ds

@[simp] theorem walkEnd_nil (G : PortGraph V D) (v : V) : walkEnd G v [] = v := rfl

@[simp] theorem walkEnd_cons (G : PortGraph V D) (v : V) (d : D) (ds : List D) :
    walkEnd G v (d :: ds) = walkEnd G (next G v d) ds := rfl

theorem walkEnd_append (G : PortGraph V D) (v : V) (as bs : List D) :
    walkEnd G v (as ++ bs) = walkEnd G (walkEnd G v as) bs := by
  induction as generalizing v with
  | nil => rfl
  | cons d ds ih => exact ih (next G v d)

def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def rotateHead (G : PortGraph V D) (n : Nat) : Walk V D (n + 1) ≃ Walk V D (n + 1) :=
  (splitHead V D n).trans
    ((Equiv.prodCongr G.rot (Equiv.refl (Fin n → D))).trans (splitHead V D n).symm)

@[simp] theorem rotateHead_vertex (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).1 = next G w.1 (w.2 0) := rfl

@[simp] theorem rotateHead_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).2 0 = (G.rot (w.1, w.2 0)).2 := rfl

@[simp] theorem rotateHead_succ (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (j : Fin n) :
    (rotateHead G n w).2 j.succ = w.2 j.succ := rfl

def permutePorts {t : Nat} (σ : Fin t ≃ Fin t) : Walk V D t ≃ Walk V D t where
  toFun w := (w.1, fun j => w.2 (σ j))
  invFun w := (w.1, fun j => w.2 (σ.symm j))
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact congrArg w.2 (σ.apply_symm_apply j)
  right_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact congrArg w.2 (σ.symm_apply_apply j)

def wordEnd (G : PortGraph V D) : (n : Nat) → V → (Fin n → D) → V
  | 0, v, _ => v
  | n + 1, v, p => wordEnd G n (next G v (p 0)) (fun j => p j.succ)

def endpoint (G : PortGraph V D) {n : Nat} (w : Walk V D n) : V :=
  wordEnd G n w.1 w.2

theorem natCard_walk [Finite V] [Finite D] (n : Nat) :
    Nat.card (Walk V D n) = Nat.card V * Nat.card D ^ n := by
  simp [Walk, Nat.card_prod, Nat.card_fun]

def headTailEquiv (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ (Walk V D n × D) where
  toFun w := ((w.1, fun j => w.2 j.succ), w.2 0)
  invFun z := (z.1.1, Fin.cases z.2 z.1.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def advanceTail {n : Nat} (G : PortGraph V D) (w : Walk V D (n + 1)) : Walk V D n :=
  ((G.rot (w.1, w.2 0)).1, fun j => w.2 j.succ)

def edgeAt (G : PortGraph V D) :
    (n : Nat) → Walk V D (n + 1) → Fin (n + 1) → Edge V D
  | 0, w, _ => (w.1, w.2 0)
  | n + 1, w, k => Fin.cases (w.1, w.2 0)
      (fun j => edgeAt G n (advanceTail G w) j) k

def pivotEquiv (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) →
      (Walk V D (n + 1) ≃ (Edge V D × (Fin n → D)))
  | 0, _ => splitHead V D 0
  | n + 1, k => Fin.cases (splitHead V D (n + 1))
      (fun j => (rotateHead G (n + 1)).trans
        ((headTailEquiv V D (n + 1)).trans
          ((Equiv.prodCongr (pivotEquiv G n j) (Equiv.refl D)).trans
            (headTailEquiv (Edge V D) D n).symm))) k

theorem pivotEquiv_fst (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      (pivotEquiv G n k w).1 = edgeAt G n w k := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change (pivotEquiv G n j (advanceTail G w)).1 =
        edgeAt G n (advanceTail G w) j
      exact ih j (advanceTail G w)

theorem edgeAt_port (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      (edgeAt G n w k).2 = w.2 k := by
  intro n
  induction n with
  | zero =>
    intro w k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · exact ih (advanceTail G w) j

theorem pivotEquiv_zero_apply (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    pivotEquiv G n 0 w = ((w.1, w.2 0), fun j => w.2 j.succ) := by
  cases n <;> rfl

theorem pivotEquiv_succ_apply (G : PortGraph V D)
    (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 2)) :
    pivotEquiv G (n + 1) k.succ w =
      ((pivotEquiv G n k (advanceTail G w)).1,
       Fin.cases (G.rot (w.1, w.2 0)).2
         (pivotEquiv G n k (advanceTail G w)).2) := rfl

def projectedFiberEquiv {X E R : Type*} (e : X ≃ E × R) (f : X → E)
    (he : ∀ x, (e x).1 = f x) (a : E) : {x // f x = a} ≃ R where
  toFun x := (e x.val).2
  invFun r := ⟨e.symm (a, r), by
    exact (he _).symm.trans (congrArg Prod.fst (e.apply_symm_apply (a, r)))⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext ((he x.val).trans x.property).symm rfl
  right_inv r := congrArg Prod.snd (e.apply_symm_apply (a, r))

def projectedEventEquiv {X E R : Type*} (e : X ≃ E × R) (f : X → E)
    (he : ∀ x, (e x).1 = f x) (P : E → Prop) :
    {x // P (f x)} ≃ ({a // P a} × R) where
  toFun x := (⟨(e x.val).1, by rw [he]; exact x.property⟩, (e x.val).2)
  invFun ar := ⟨e.symm (ar.1.val, ar.2), by
    have h : f (e.symm (ar.1.val, ar.2)) = ar.1.val :=
      (he _).symm.trans (congrArg Prod.fst (e.apply_symm_apply (ar.1.val, ar.2)))
    simpa only [h] using ar.1.property⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.val
  right_inv ar := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.apply_symm_apply (ar.1.val, ar.2))
    · change (e (e.symm (ar.1.val, ar.2))).2 = ar.2
      exact congrArg Prod.snd (e.apply_symm_apply (ar.1.val, ar.2))

theorem natCard_edgeAt_fiber (G : PortGraph V D) (n : Nat) (k : Fin (n + 1))
    (a : Edge V D) :
    Nat.card {w : Walk V D (n + 1) // edgeAt G n w k = a} = Nat.card D ^ n := by
  calc
    _ = Nat.card (Fin n → D) := Nat.card_congr
      (projectedFiberEquiv (pivotEquiv G n k) (fun w => edgeAt G n w k)
        (pivotEquiv_fst G n k) a)
    _ = _ := by simp [Nat.card_fun]

theorem natCard_edgeAt_event (G : PortGraph V D) (n : Nat) (k : Fin (n + 1))
    (P : Edge V D → Prop) :
    Nat.card {w : Walk V D (n + 1) // P (edgeAt G n w k)} =
      Nat.card {a : Edge V D // P a} * Nat.card D ^ n := by
  calc
    _ = Nat.card ({a : Edge V D // P a} × (Fin n → D)) := Nat.card_congr
      (projectedEventEquiv (pivotEquiv G n k) (fun w => edgeAt G n w k)
        (pivotEquiv_fst G n k) P)
    _ = _ := by simp [Nat.card_prod, Nat.card_fun]

def leftFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → V → (Fin n → D) → V
  | 0, _, v, _ => v
  | n + 1, k, v, r => Fin.cases v
      (fun j => next G (leftFromPivot G n j v (fun m => r m.succ)) (r 0)) k

def rightFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → Edge V D → (Fin n → D) → V
  | 0, _, e, _ => next G e.1 e.2
  | n + 1, k, e, r => Fin.cases
      (wordEnd G (n + 1) (next G e.1 e.2) r)
      (fun j => rightFromPivot G n j e (fun m => r m.succ)) k

theorem leftFromPivot_zero (G : PortGraph V D) (n : Nat)
    (v : V) (r : Fin n → D) : leftFromPivot G n 0 v r = v := by
  cases n <;> rfl

theorem rightFromPivot_zero (G : PortGraph V D) (n : Nat)
    (e : Edge V D) (r : Fin n → D) :
    rightFromPivot G n 0 e r = wordEnd G n (next G e.1 e.2) r := by
  cases n <;> rfl

theorem leftFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      leftFromPivot G n k (pivotEquiv G n k w).1.1 (pivotEquiv G n k w).2 = w.1 := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change next G
        (leftFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1.1
          (pivotEquiv G n j (advanceTail G w)).2)
        (G.rot (w.1, w.2 0)).2 = w.1
      rw [ih j (advanceTail G w)]
      change (G.rot ((G.rot (w.1, w.2 0)).1, (G.rot (w.1, w.2 0)).2)).1 = w.1
      exact congrArg Prod.fst (rot_rot G (w.1, w.2 0))

theorem rightFromPivot_actual (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (w : Walk V D (n + 1)),
      rightFromPivot G n k (pivotEquiv G n k w).1 (pivotEquiv G n k w).2 =
        endpoint G w := by
  intro n
  induction n with
  | zero => intro k w; rfl
  | succ n ih =>
    intro k w
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · rw [pivotEquiv_succ_apply]
      change rightFromPivot G n j (pivotEquiv G n j (advanceTail G w)).1
        (pivotEquiv G n j (advanceTail G w)).2 = endpoint G w
      rw [ih j (advanceTail G w)]
      rfl

end UniqueGames.Foundations.PCP.PoweringWalks

end OAI
