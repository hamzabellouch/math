import Mathlib
import OAI.Algebra.FrobeniusObstruction.MixedForms
import OAI.Algebra.FrobeniusObstruction.ExteriorSplit
import OAI.Algebra.FrobeniusObstruction.Derivations

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormsSplit
open scoped TensorProduct
open Frobenius MixedForms
variable {ι κ k : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [CommRing k] (ell : ℕ)

abbrev QForms (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  MixedForms.Forms (k := k) (A := Frobenius.Ring (ι := ι) (k := k) ell) (ι := ι)

noncomputable def includeLeft : QForms (k := k) ell ι →ₐ[k] QForms (k := k) ell (ι ⊕ κ) :=
  Algebra.TensorProduct.map (includeVariables ell Sum.inl)
    (ExteriorAlgebra.map ExteriorSplit.leftVec)
noncomputable def includeRight : QForms (k := k) ell κ →ₐ[k] QForms (k := k) ell (ι ⊕ κ) :=
  Algebra.TensorProduct.map (includeVariables ell Sum.inr)
    (ExteriorAlgebra.map ExteriorSplit.rightVec)

                                                                            
                                                                               
noncomputable def sumEquiv : QForms (k := k) ell (ι ⊕ κ) ≃ₗ[k]
    QForms (k := k) ell ι ⊗[k] QForms (k := k) ell κ :=
  (TensorProduct.congr (Frobenius.sumEquiv (k := k) (ι := ι) (κ := κ) ell).toLinearEquiv
      (ExteriorSplit.sumEquiv (k := k) (ι := ι) (κ := κ))).trans
    (TensorProduct.tensorTensorTensorComm k _ _ _ _)

@[simp] theorem sumEquiv_symm_tmul (x : QForms (k := k) ell ι)
    (y : QForms (k := k) ell κ) :
    (sumEquiv (k := k) (ι := ι) (κ := κ) ell).symm (x ⊗ₜ[k] y) =
      includeLeft ell x * includeRight ell y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, add_mul, hx, hx']
  | tmul a e =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, mul_add, hy, hy']
    | tmul b f =>
      change (TensorProduct.congr
        (Frobenius.sumEquiv (k := k) (ι := ι) (κ := κ) ell).toLinearEquiv
        (ExteriorSplit.sumEquiv (k := k) (ι := ι) (κ := κ))).symm
          ((TensorProduct.tensorTensorTensorComm k _ _ _ _).symm
            ((a ⊗ₜ[k] e) ⊗ₜ[k] (b ⊗ₜ[k] f))) = _
      rw [TensorProduct.tensorTensorTensorComm_symm, TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.congr_symm,
        TensorProduct.congr_tmul, ExteriorSplit.sumEquiv_symm_tmul]
      change merge (k := k) (ι := ι) (κ := κ) ell (a ⊗ₜ[k] b) ⊗ₜ[k]
        (ExteriorAlgebra.map ExteriorSplit.leftVec e * ExteriorAlgebra.map ExteriorSplit.rightVec f) = _
      rw [merge_tmul]
      simp only [includeLeft, includeRight, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]

omit [Fintype ι] [Fintype κ] in
@[simp] theorem exterior_left_gen (i : ι) :
    ExteriorAlgebra.map (ExteriorSplit.leftVec (k := k) (κ := κ)) (gen i) =
      gen (Sum.inl i : ι ⊕ κ) := by
  rw [gen, ExteriorAlgebra.map_apply_ι]
  congr 1
  funext j
  cases j <;> simp [ExteriorSplit.leftVec, Pi.single_apply]

omit [Fintype ι] [Fintype κ] in
@[simp] theorem exterior_right_gen (i : κ) :
    ExteriorAlgebra.map (ExteriorSplit.rightVec (k := k) (ι := ι)) (gen i) =
      gen (Sum.inr i : ι ⊕ κ) := by
  rw [gen, ExteriorAlgebra.map_apply_ι]
  congr 1
  funext j
  cases j <;> simp [ExteriorSplit.rightVec, Pi.single_apply]

 theorem involute_map {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] (f : V →ₗ[k] W) (e : ExteriorAlgebra k V) :
    CliffordAlgebra.involute (ExteriorAlgebra.map f e) =
      ExteriorAlgebra.map f (CliffordAlgebra.involute e) := by
  have h : (CliffordAlgebra.involute : ExteriorAlgebra k W →ₐ[k] _).comp
      (ExteriorAlgebra.map f) = (ExteriorAlgebra.map f).comp CliffordAlgebra.involute := by
    ext v
    simp
  exact AlgHom.congr_fun h e

@[simp] theorem parity_includeLeft (x : QForms (k := k) ell ι) :
    parity (includeLeft (κ := κ) ell x) = includeLeft ell (parity x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => simp only [includeLeft, Algebra.TensorProduct.map_tmul, parity_tmul,
      involute_map]

@[simp] theorem parity_includeRight (x : QForms (k := k) ell κ) :
    parity (includeRight (ι := ι) ell x) = includeRight ell (parity x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => simp only [includeRight, Algebra.TensorProduct.map_tmul, parity_tmul,
      involute_map]

variable [CharP k ell]

@[simp] theorem d_includeLeft (x : QForms (k := k) ell ι) :
    d (partialDeriv ell) (includeLeft (κ := κ) ell x) =
      includeLeft ell (d (partialDeriv ell) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    simp only [includeLeft, Algebra.TensorProduct.map_tmul, d_tmul,
      Fintype.sum_sum_type, partial_include_left, partial_include_left_other,
      TensorProduct.zero_tmul, Finset.sum_const_zero, add_zero, map_sum, map_mul,
      exterior_left_gen]

@[simp] theorem d_includeRight (x : QForms (k := k) ell κ) :
    d (partialDeriv ell) (includeRight (ι := ι) ell x) =
      includeRight ell (d (partialDeriv ell) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    simp only [includeRight, Algebra.TensorProduct.map_tmul, d_tmul,
      Fintype.sum_sum_type, partial_include_right, partial_include_right_other,
      TensorProduct.zero_tmul, Finset.sum_const_zero, zero_add, map_sum, map_mul,
      exterior_right_gen]

omit [CharP k ell] in
@[simp] theorem includeLeft_coeff (a : Ring (ι := ι) (k := k) ell) :
    includeLeft (κ := κ) ell (coeff a) = coeff (includeVariables ell Sum.inl a) := by
  simp only [includeLeft, coeff_apply, Algebra.TensorProduct.map_tmul, map_one]
omit [CharP k ell] in
@[simp] theorem includeRight_coeff (a : Ring (ι := κ) (k := k) ell) :
    includeRight (ι := ι) ell (coeff a) = coeff (includeVariables ell Sum.inr a) := by
  simp only [includeRight, coeff_apply, Algebra.TensorProduct.map_tmul, map_one]

@[simp] theorem gradient_include_left (a : Ring (ι := ι) (k := k) ell) :
    gradient (partialDeriv ell) (includeVariables ell (Sum.inl : ι → ι ⊕ κ) a) =
      includeLeft ell (gradient (partialDeriv ell) a) := by
  change d (partialDeriv ell) (coeff (includeVariables ell Sum.inl a)) = _
  rw [← includeLeft_coeff, d_includeLeft, d_coeff]

@[simp] theorem gradient_include_right (a : Ring (ι := κ) (k := k) ell) :
    gradient (partialDeriv ell) (includeVariables ell (Sum.inr : κ → ι ⊕ κ) a) =
      includeRight ell (gradient (partialDeriv ell) a) := by
  change d (partialDeriv ell) (coeff (includeVariables ell Sum.inr a)) = _
  rw [← includeRight_coeff, d_includeRight, d_coeff]

theorem gradient_add {A : Type*} [CommRing A] [Algebra k A]
    (pd : ι → Derivation k A A) (a b : A) :
    gradient pd (a + b) = gradient pd a + gradient pd b := by
  simp only [MixedForms.gradient, TensorProduct.add_tmul, map_add]

                                                                           
                                                                        
theorem delta_product (Q : Ring (ι := ι) (k := k) ell)
    (R : Ring (ι := κ) (k := k) ell) (x : QForms (k := k) ell ι)
    (y : QForms (k := k) ell κ) :
    delta (partialDeriv ell) (includeVariables ell Sum.inl Q + includeVariables ell Sum.inr R)
      (includeLeft ell x * includeRight ell y) =
        includeLeft ell (delta (partialDeriv ell) Q x) * includeRight ell y +
          includeLeft ell (parity x) * includeRight ell (delta (partialDeriv ell) R y) := by
  rw [delta_apply, gradient_add, gradient_include_left, gradient_include_right, add_mul]
  congr 1
  · rw [delta_apply, map_mul, mul_assoc]
  · rw [← gradient_include_right, ← mul_assoc, gradient_supercommute, parity_includeLeft,
      mul_assoc, delta_apply, map_mul, gradient_include_right]

end BoundaryOnly.FormalObstruction.FormsSplit

namespace BoundaryOnly.FormalObstruction.GlobalForms
open Frobenius MixedForms
open scoped TensorProduct
variable {k : Type*} [CommRing k]

                                                                         
abbrev Coordinates : (n : ℕ) → (Fin n → Type) → Type
  | 0, _ => PEmpty
  | n + 1, V => V 0 ⊕ Coordinates n (fun i => V i.succ)

instance coordinatesFintype : ∀ (n : ℕ) (V : Fin n → Type) [∀ i, Fintype (V i)],
    Fintype (Coordinates n V)
  | 0, _, _ => inferInstanceAs (Fintype PEmpty)
  | n + 1, V, _ => by
      letI := coordinatesFintype n (fun i => V i.succ)
      exact inferInstanceAs (Fintype (V 0 ⊕ Coordinates n (fun i => V i.succ)))

instance coordinatesDecidableEq : ∀ (n : ℕ) (V : Fin n → Type) [∀ i, DecidableEq (V i)],
    DecidableEq (Coordinates n V)
  | 0, _, _ => inferInstanceAs (DecidableEq PEmpty)
  | n + 1, V, _ => by
      letI := coordinatesDecidableEq n (fun i => V i.succ)
      exact inferInstanceAs (DecidableEq (V 0 ⊕ Coordinates n (fun i => V i.succ)))

abbrev consIndex (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by intro i; cases i with
    | inl u => cases u; rfl
    | inr i => rfl
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem consIndex_zero (n : ℕ) : consIndex n (.inl ()) = 0 := rfl
@[simp] theorem consIndex_succ (n : ℕ) (i : Fin n) : consIndex n (.inr i) = i.succ := rfl

                                                                                  
def tensorCons {n : ℕ} (V : Fin (n + 1) → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] : (⨂[k] i, V i) ≃ₗ[k] V 0 ⊗[k] (⨂[k] i : Fin n, V i.succ) :=
  ((PiTensorProduct.reindex k V (consIndex n).symm).trans
    (PiTensorProduct.tmulEquivDep k (fun j => V (consIndex n j))).symm).trans
      (TensorProduct.congr (PiTensorProduct.subsingletonEquiv ()) (LinearEquiv.refl _ _))

@[simp] theorem tensorCons_tprod {n : ℕ} (V : Fin (n + 1) → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] (v : ∀ i, V i) :
    tensorCons (k := k) V (PiTensorProduct.tprod k v) =
      v 0 ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin n => v i.succ) := by
  simp only [tensorCons, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod,
    PiTensorProduct.tmulEquivDep_symm_apply, Equiv.symm_symm]
  change (TensorProduct.congr
      (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : Unit => V 0) ())
      (LinearEquiv.refl k (⨂[k] i : Fin n, V i.succ)))
      ((PiTensorProduct.tprod k (fun _ : Unit => v 0)) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun i : Fin n => v i.succ)) = _
  rw [TensorProduct.congr_tmul, PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

def emptyCoefficients (ell : ℕ) (hell : 0 < ell) :
    Ring (ι := PEmpty) (k := k) ell ≃ₐ[k] k :=
  AlgEquiv.ofAlgHom
    { constantHom ell hell with commutes' := constantHom_algebraMap ell hell }
    (Algebra.ofId k _)
    (by ext)
    (by apply algHom_ext; intro i; exact PEmpty.elim i)

def emptyExterior : ExteriorAlgebra k (PEmpty.{1} → k) ≃ₐ[k] k :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.lift k ⟨0, by simp⟩) (Algebra.ofId k _)
    (by ext)
    (by apply ExteriorAlgebra.hom_ext
        apply LinearMap.ext
        intro v
        have hv : v = 0 := Subsingleton.elim _ _
        rw [hv]
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
        rw [show (ExteriorAlgebra.ι k) (0 : PEmpty.{1} → k) = 0 from
          (ExteriorAlgebra.ι k).map_zero]
        simp)

abbrev QForms (ell : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] :=
  MixedForms.Forms (k := k) (A := Ring (ι := ι) (k := k) ell) (ι := ι)

def emptyForms (ell : ℕ) (hell : 0 < ell) : QForms (k := k) ell PEmpty ≃ₗ[k] k :=
  (TensorProduct.congr (emptyCoefficients (k := k) ell hell).toLinearEquiv
    (emptyExterior (k := k)).toLinearEquiv).trans (TensorProduct.lid k k)

                                                                             
noncomputable def blockEquiv (ell : ℕ) (hell : 0 < ell) :
    ∀ (n : ℕ) (V : Fin n → Type) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)],
      QForms (k := k) ell (Coordinates n V) ≃ₗ[k] (⨂[k] i, QForms (k := k) ell (V i))
  | 0, _, _, _ => (emptyForms ell hell).trans (PiTensorProduct.isEmptyEquiv (Fin 0)).symm
  | n + 1, V, _, _ =>
    ((FormsSplit.sumEquiv (k := k) (ι := V 0) (κ := Coordinates n (fun i => V i.succ)) ell).trans
      (TensorProduct.congr (LinearEquiv.refl k (QForms (k := k) ell (V 0)))
        (blockEquiv ell hell n (fun i => V i.succ)))).trans
          (tensorCons (k := k) (fun i => QForms (k := k) ell (V i))).symm

end BoundaryOnly.FormalObstruction.GlobalForms

end

end OAI
