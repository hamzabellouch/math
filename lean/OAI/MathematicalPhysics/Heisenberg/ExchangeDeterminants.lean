import OAI.MathematicalPhysics.Heisenberg.ConditionalMoments

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

namespace Heisenberg.Exposure

section
variable {K J Ω : Type*} [Fintype K] [Fintype J] [Fintype Ω]
  [DecidableEq K] [DecidableEq J]
variable {R : Type*} [CommRing R]

lemma det_block_extraction (X : Matrix (K ⊕ J) (K ⊕ J) R) (D : Matrix K K R) :
    (1 - (Matrix.fromBlocks D 0 0 0) * X).det =
      (1-D*X.submatrix Sum.inl Sum.inl).det := by
  have he : 1 - (Matrix.fromBlocks D 0 0 0) * X =
      Matrix.fromBlocks (1-D*X.submatrix Sum.inl Sum.inl)
        (-D*X.submatrix Sum.inl Sum.inr) 0 1 := by
    ext i j
    rcases i with i|i <;> rcases j with j|j <;>
      simp [Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks,Matrix.one_apply]
  rw [he,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one]

theorem DeterminantLaw.inl {p : Ω → R} {X : Ω → Matrix (K ⊕ J) (K ⊕ J) R}
    (h : DeterminantLaw p X) :
    DeterminantLaw p (fun ω => (X ω).submatrix Sum.inl Sum.inl) := by
  intro D
  have hh := h (Matrix.fromBlocks D 0 0 0)
  simp only [det_block_extraction] at hh
  convert hh using 1
  congr 3
  ext i j
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.submatrix_apply]

variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq N] [DecidableEq M]

theorem DeterminantLaw.reindex {p : Ω → R} {X : Ω → Matrix N N R}
    (h : DeterminantLaw p X) (e : M ≃ N) :
    DeterminantLaw p (fun ω => (X ω).submatrix e e) := by
  intro D
  have hh := h (D.submatrix e.symm e.symm)
  have hr : ∀ Y : Matrix N N R,
      (1-D.submatrix e.symm e.symm*Y).det =
        (1-D*Y.submatrix e e).det := by
    intro Y
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    change (1 : Matrix N N R).submatrix e e -
      (D.submatrix e.symm e.symm*Y).submatrix e e = _
    rw [Matrix.submatrix_one_equiv]
    rw [← Matrix.submatrix_mul_equiv _ _ e e e]
    simp only [Matrix.submatrix_submatrix,Equiv.symm_comp_self,Matrix.submatrix_id_id]
  simp only [hr] at hh
  convert hh using 1
  congr 3
  ext i j
  simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.submatrix_apply]

theorem DeterminantLaw.subtype {p : Ω → R} {X : Ω → Matrix N N R}
    (h : DeterminantLaw p X) (P : N → Prop) [DecidablePred P] :
    DeterminantLaw p (fun ω => (X ω).submatrix (fun x : {i // P i} => x.val) (fun x => x.val)) := by
  exact (h.reindex (Equiv.sumCompl P)).inl

end

variable {N Ω Ψ B R : Type*} [Fintype N] [DecidableEq N]
  [Fintype Ω] [Fintype Ψ] [Fintype B] [CommRing R]

lemma DeterminantLaw.reparam {p : Ω → R} {X : Ω → Matrix N N R}
    (h : DeterminantLaw p X) (e : Ψ ≃ Ω) :
    DeterminantLaw (p ∘ e) (X ∘ e) := by
  intro D
  change (∑ x, p (e x)*(1-D*X (e x)).det) = (1-D*(∑ x,p (e x) • X (e x))).det
  rw [e.sum_comp (fun x => p x*(1-D*X x).det),e.sum_comp (fun x => p x • X x)]
  exact h D

lemma DeterminantLaw.const_left {p : Ω → R} {X : Ω → Matrix N N R}
    (h : DeterminantLaw p X) (C : Matrix N N R) :
    DeterminantLaw p (fun ω => C*X ω) := by
  intro D
  simpa only [Matrix.mul_assoc,Matrix.mul_sum,Matrix.mul_smul] using h (D*C)

lemma determinantLaw_constant (p : Ω → R) (hp : ∑ x,p x=1) (C : Matrix N N R) :
    DeterminantLaw p (fun _ => C) := by
  intro D
  simp only [← Finset.sum_mul,← Finset.sum_smul,hp,one_mul,one_smul]

omit [Fintype N] [DecidableEq N] [Fintype Ω] [Fintype Ψ] [Fintype B] [CommRing R] in
def splitArray (n : ℕ) : (Fin (n+1) → B) ≃ B × (Fin n → B) where
  toFun f := (f 0,fun i => f i.succ)
  invFun z := Fin.cons z.1 z.2
  left_inv f := by funext i; refine Fin.cases rfl (fun i => rfl) i
  right_inv z := by rfl

omit [Fintype N] [DecidableEq N] [Fintype Ω] [Fintype Ψ] [Fintype B] [CommRing R] in
def orderedProduct {A : Type*} [Monoid A] : (n : ℕ) → (Fin n → A) → A
  | 0, _ => 1
  | n+1, f => f 0 * orderedProduct n (fun i => f i.succ)

theorem determinantLaw_array (n : ℕ)
    (w : Fin n → B → R) (X : Fin n → B → Matrix N N R)
    (h : ∀ i, DeterminantLaw (w i) (X i)) :
    DeterminantLaw (fun b : Fin n → B => ∏ i,w i (b i))
      (fun b => orderedProduct n (fun i => X i (b i))) := by
  induction n with
  | zero => intro D; simp [orderedProduct]
  | succ n ih =>
    have hh := (h 0).independent_mul (ih (fun i => w i.succ) (fun i => X i.succ) (fun i => h i.succ))
    have ht := hh.reparam (splitArray (B:=B) n)
    convert ht using 1
    · funext b
      exact Fin.prod_univ_succ _
    · rfl

end Heisenberg.Exposure

namespace Heisenberg.LayeredExchange
variable {T V : Type*}

def fibers (σ : T → Equiv.Perm V) : Equiv.Perm (T × V) where
  toFun z := (z.1, σ z.1 z.2)
  invFun z := (z.1, (σ z.1).symm z.2)
  left_inv z := by simp
  right_inv z := by simp

@[simp] lemma fibers_apply (σ : T → Equiv.Perm V) (t : T) (v : V) :
    fibers σ (t,v) = (t,σ t v) := rfl

@[simp] lemma fibers_one : fibers (fun _ : T => (1 : Equiv.Perm V)) = 1 := by
  ext ⟨t,v⟩ <;> rfl

lemma fibers_mul (σ τ : T → Equiv.Perm V) :
    fibers (fun t => σ t * τ t) = fibers σ * fibers τ := by rfl

def wiring (s : Equiv.Perm T) (σ : T → Equiv.Perm V) : Equiv.Perm (T × V) :=
  (Equiv.prodCongr s (Equiv.refl V)) * fibers σ

@[simp] lemma wiring_apply (s : Equiv.Perm T) (σ : T → Equiv.Perm V) (t : T) (v : V) :
    wiring s σ (t,v) = (s t,σ t v) := rfl

lemma fibers_update [DecidableEq T] (σ : T → Equiv.Perm V) (t : T) (τ : Equiv.Perm V) :
    fibers (Function.update σ t (τ * σ t)) =
      fibers (Function.update (fun _ => 1) t τ) * fibers σ := by
  ext ⟨u,v⟩ <;> by_cases h : u = t <;> simp [fibers,Function.update,h]

lemma fibers_swap [DecidableEq T] [DecidableEq V] (t : T) (u v : V) :
    fibers (Function.update (fun _ : T => 1) t (Equiv.swap u v)) = Equiv.swap (t,u) (t,v) := by
  ext ⟨a,b⟩ <;> by_cases ht : a = t
  · subst a
    simp [fibers,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · simp [fibers,Function.update,ht,Equiv.swap_apply_def]
  · subst a
    simp [fibers,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · simp [fibers,Function.update,ht,Equiv.swap_apply_def]

end Heisenberg.LayeredExchange

namespace Heisenberg.Exposure
variable {A B : Type*} [Monoid A] [Monoid B]

lemma orderedProduct_map (f : A →* B) (n : ℕ) (x : Fin n → A) :
    f (orderedProduct n x) = orderedProduct n (fun i => f (x i)) := by
  induction n with
  | zero => exact f.map_one
  | succ n ih => simp only [orderedProduct,map_mul,ih]

lemma orderedProduct_one (n : ℕ) (x : Fin n → A) (hx : ∀ i,x i=1) :
    orderedProduct n x = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [orderedProduct,hx,ih _ fun _ => rfl]

lemma orderedProduct_single {n : ℕ} (x : Fin n → A) (i : Fin n)
    (hx : ∀ j,j ≠ i → x j=1) : orderedProduct n x = x i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      rw [orderedProduct,orderedProduct_one _ _ (fun j => hx j.succ (Fin.succ_ne_zero j)),mul_one]
    | succ i =>
      rw [orderedProduct,hx 0 (Fin.succ_ne_zero i).symm,one_mul]
      exact ih _ i (fun j hj => hx j.succ (by simpa using hj))

end Heisenberg.Exposure
namespace Heisenberg.LayeredExchange

section
open Exposure
variable {T V : Type*}

def fibersHom : (T → Equiv.Perm V) →* Equiv.Perm (T × V) where
  toFun := fibers
  map_one' := fibers_one
  map_mul' := fibers_mul

lemma fibers_ordered_product (n : ℕ) (σ : Fin n → Equiv.Perm V) :
    fibers σ = orderedProduct n (fun i => fibers (Function.update (fun _ => 1) i (σ i))) := by
  change fibersHom σ = orderedProduct n
    (fun i => fibersHom (Function.update (fun _ => 1) i (σ i)))
  rw [← orderedProduct_map (fibersHom (T:=Fin n) (V:=V))]
  apply congrArg fibers
  funext i
  let eval : (Fin n → Equiv.Perm V) →* Equiv.Perm V :=
    { toFun := fun f => f i, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have he := orderedProduct_map eval n (fun j => Function.update (fun _ => 1) j (σ j))
  change σ i = eval (orderedProduct n (fun j => Function.update (fun _ => 1) j (σ j)))
  rw [he,orderedProduct_single _ i]
  · simp [eval]
  · intro j hj
    simp [eval,Function.update,Ne.symm hj]

end

open Exposure
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : Type*} [CommRing R]

def forwardHom : Equiv.Perm V →* Matrix V V R where
  toFun π := (π.permMatrix R).transpose
  map_one' := by simp
  map_mul' π σ := by rw [Matrix.permMatrix_mul, Matrix.transpose_mul]

lemma forwardHom_swap (a b : V) :
    forwardHom (R:=R) (Equiv.swap a b) = (Equiv.swap a b).permMatrix R := by
  simp [forwardHom,Matrix.transpose_permMatrix]

lemma determinantLaw_phase {n : ℕ} (i : Fin n) (a b : V) (p : R)
    (fixed : Option (Equiv.Perm V)) :
    DeterminantLaw (fun c : Bool => if c then p else 1-p)
      (fun c => forwardHom (R:=R) (fibers (Function.update (fun _ => 1) i
        (fixed.getD (if c then Equiv.swap a b else 1))))) := by
  cases fixed with
  | some σ =>
    simp only [Option.getD_some]
    exact determinantLaw_constant (fun c : Bool => if c then p else 1-p)
      (by simp) (forwardHom (R:=R) (fibers (Function.update (fun _ => 1) i σ)))
  | none =>
    have he : ∀ c : Bool,
        forwardHom (R:=R) (fibers (Function.update (fun _ => 1) i
          ((none : Option (Equiv.Perm V)).getD (if c then Equiv.swap a b else 1)))) =
          if c then (Equiv.swap (i,a) (i,b)).permMatrix R else 1 := by
      intro c
      cases c
      · simp [forwardHom,fibers_one]
      · simp only [↓reduceIte,Option.getD_none,fibers_swap,forwardHom_swap]
    simp_rw [he]
    exact determinantLaw_bernoulli _ _ _

theorem determinantLaw_wiring {n : ℕ} (s : Equiv.Perm (Fin n))
    (a b : Fin n → V) (p : Fin n → R) (fixed : Fin n → Option (Equiv.Perm V)) :
    DeterminantLaw (fun c : Fin n → Bool => ∏ i,if c i then p i else 1-p i)
      (fun c => forwardHom (R:=R) (wiring s
        (fun i => (fixed i).getD (if c i then Equiv.swap (a i) (b i) else 1)))) := by
  have h := determinantLaw_array n (fun i (c : Bool) => if c then p i else 1-p i)
    (fun i c => forwardHom (R:=R) (fibers (Function.update (fun _ => 1) i
      ((fixed i).getD (if c then Equiv.swap (a i) (b i) else 1)))))
    (fun i => determinantLaw_phase i (a i) (b i) (p i) (fixed i))
  have hh := h.const_left (forwardHom (R:=R) (Equiv.prodCongr s (Equiv.refl V)))
  convert hh using 1
  funext c
  rw [wiring,map_mul,fibers_ordered_product,orderedProduct_map]

end Heisenberg.LayeredExchange
end

end OAI
