import Mathlib
import OAI.Algebra.FrobeniusObstruction.SignedTensor

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.GlobalForms
open Frobenius MixedForms FormsSplit SignedTensor
open scoped TensorProduct BigOperators
variable {k : Type*} [Field k] (ell : ℕ) (hell : 0 < ell)

@[simp] theorem blockEquiv_succ_symm_tensorCons {n : ℕ} (V : Fin (n + 1) → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (x : QForms (k := k) ell (V 0))
    (y : ⨂[k] i : Fin n, QForms (k := k) ell (V i.succ)) :
    (blockEquiv (k := k) ell hell (n + 1) V).symm
      ((tensorCons (k := k) (fun i => QForms (k := k) ell (V i))).symm (x ⊗ₜ[k] y)) =
      includeLeft (κ := Coordinates n (fun i => V i.succ)) ell x * includeRight (ι := V 0) ell
        ((blockEquiv ell hell n (fun i => V i.succ)).symm y) := by
  simp only [blockEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, TensorProduct.congr_symm_tmul,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply, sumEquiv_symm_tmul]

@[simp] theorem blockEquiv_succ_symm_tprod {n : ℕ} (V : Fin (n + 1) → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (v : ∀ i, QForms (k := k) ell (V i)) :
    (blockEquiv (k := k) ell hell (n + 1) V).symm (PiTensorProduct.tprod k v) =
      includeLeft (κ := Coordinates n (fun i => V i.succ)) ell (v 0) * includeRight (ι := V 0) ell
        ((blockEquiv ell hell n (fun i => V i.succ)).symm
          (PiTensorProduct.tprod k (fun i => v i.succ))) := by
  have h := blockEquiv_succ_symm_tensorCons ell hell V (v 0)
    (PiTensorProduct.tprod k (fun i : Fin n => v i.succ))
  rw [← tensorCons_tprod (k := k) (fun i => QForms (k := k) ell (V i)) v,
    LinearEquiv.symm_apply_apply] at h
  exact h

                                                                       
noncomputable def potential : ∀ (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)],
    (∀ i, Ring (ι := V i) (k := k) ell) → Ring (ι := Coordinates n V) (k := k) ell
  | 0, _, _, _, _ => 0
  | n + 1, V, _, _, q => includeVariables ell Sum.inl (q 0) +
      includeVariables ell Sum.inr (potential n (fun i => V i.succ) (fun i => q i.succ))

end BoundaryOnly.FormalObstruction.GlobalForms

namespace BoundaryOnly.FormalObstruction.GlobalForms
open Frobenius MixedForms FormsSplit SignedTensor
open scoped TensorProduct BigOperators
variable {k : Type*} [Field k] (ell : ℕ) (hell : 0 < ell)

@[simp] theorem parity_empty (x : QForms (k := k) ell PEmpty) : parity x = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, hx, hy]
  | tmul a e =>
    rw [parity_tmul]
    congr 1
    induction e using ExteriorAlgebra.induction with
    | algebraMap r => exact AlgHom.commutes _ _
    | ι v =>
      have hv : v = 0 := Subsingleton.elim _ _
      simp [hv]
    | mul x y hx hy => simp only [map_mul, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]

                                                                            
theorem blockEquiv_symm_parity (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (t : ⨂[k] i, QForms (k := k) ell (V i)) :
    parity ((blockEquiv (k := k) ell hell n V).symm t) =
      (blockEquiv (k := k) ell hell n V).symm
        (PiTensorProduct.map (fun i => (parity (k := k) (A := Ring (ι := V i) (k := k) ell)
          (ι := V i)).toLinearMap) t) := by
  induction n with
  | zero =>
    rw [parity_empty]
    congr 1
    have h : (fun i : Fin 0 => (parity (k := k) (A := Ring (ι := V i) (k := k) ell)
        (ι := V i)).toLinearMap) = (fun i => LinearMap.id (R := k) (M := QForms (k := k) ell (V i))) := by
      funext i; exact Fin.elim0 i
    rw [h, PiTensorProduct.map_id, LinearMap.id_apply]
  | succ n ih =>
    induction t using PiTensorProduct.induction_on with
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul_tprod r v =>
      simp only [map_smul, PiTensorProduct.map_tprod]
      congr 1
      rw [blockEquiv_succ_symm_tprod, blockEquiv_succ_symm_tprod,
        map_mul, parity_includeLeft, parity_includeRight, ih]
      rw [PiTensorProduct.map_tprod]
      rfl

 theorem blockEquiv_succ_symm_differential_tprod {n : ℕ} (V : Fin (n + 1) → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (P D : EndFamily (k := k) (fun i => QForms (k := k) ell (V i)))
    (v : ∀ i, QForms (k := k) ell (V i)) :
    (blockEquiv (k := k) ell hell (n + 1) V).symm
      (differential (fun i => QForms (k := k) ell (V i)) P D (PiTensorProduct.tprod k v)) =
      includeLeft (κ := Coordinates n (fun i => V i.succ)) ell (D 0 (v 0)) *
        includeRight (ι := V 0) ell ((blockEquiv (k := k) ell hell n (fun i => V i.succ)).symm
          (PiTensorProduct.tprod k (fun i => v i.succ))) +
      includeLeft (κ := Coordinates n (fun i => V i.succ)) ell (P 0 (v 0)) *
        includeRight (ι := V 0) ell ((blockEquiv (k := k) ell hell n (fun i => V i.succ)).symm
          (differential (fun i : Fin n => QForms (k := k) ell (V i.succ))
            (fun i => P i.succ) (fun i => D i.succ)
            (PiTensorProduct.tprod k (fun i => v i.succ)))) := by
  have h := congrArg (fun z => (blockEquiv (k := k) ell hell (n + 1) V).symm
      ((tensorCons (k := k) (fun i => QForms (k := k) ell (V i))).symm z))
    (differential_cons_tprod (fun i => QForms (k := k) ell (V i)) P D v)
  simp only [LinearEquiv.symm_apply_apply, LinearEquiv.map_add] at h
  rw [blockEquiv_succ_symm_tensorCons (k := k) ell hell V,
    blockEquiv_succ_symm_tensorCons (k := k) ell hell V] at h
  exact h

variable [CharP k ell]

                                                                                 
theorem blockEquiv_symm_d (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (t : ⨂[k] i, QForms (k := k) ell (V i)) :
    d (partialDeriv (k := k) ell) ((blockEquiv (k := k) ell hell n V).symm t) =
      (blockEquiv (k := k) ell hell n V).symm
        (differential (fun i => QForms (k := k) ell (V i))
          (fun i => (parity (k := k) (A := Ring (ι := V i) (k := k) ell) (ι := V i)).toLinearMap)
          (fun i => d (partialDeriv (ι := V i) (k := k) ell)) t) := by
  induction n with
  | zero =>
    simp only [d, differential, Fin.sum_univ_zero, LinearMap.zero_apply, LinearEquiv.map_zero]
    have h : (∑ i : Coordinates 0 V, TensorProduct.map
        (partialDeriv (k := k) ell i).toLinearMap (wedge i)) = 0 := by
      exact Finset.sum_eq_zero (fun i _ => PEmpty.elim i)
    rw [h, LinearMap.zero_apply]
  | succ n ih =>
    induction t using PiTensorProduct.induction_on with
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul_tprod r v =>
      simp only [map_smul]
      congr 1
      rw [blockEquiv_succ_symm_tprod, blockEquiv_succ_symm_differential_tprod,
        d_mul, d_includeLeft, d_includeRight, parity_includeLeft, ih]
      rfl

                                                                           
                                                             
theorem blockEquiv_symm_delta (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (q : ∀ i, Ring (ι := V i) (k := k) ell)
    (t : ⨂[k] i, QForms (k := k) ell (V i)) :
    delta (partialDeriv (k := k) ell) (potential (k := k) ell n V q)
      ((blockEquiv (k := k) ell hell n V).symm t) =
      (blockEquiv (k := k) ell hell n V).symm
        (differential (fun i => QForms (k := k) ell (V i))
          (fun i => (parity (k := k) (A := Ring (ι := V i) (k := k) ell) (ι := V i)).toLinearMap)
          (fun i => delta (partialDeriv (ι := V i) (k := k) ell) (q i)) t) := by
  induction n with
  | zero => simp only [potential, delta_apply, MixedForms.gradient, TensorProduct.zero_tmul,
      LinearMap.map_zero, LinearEquiv.map_zero, zero_mul, differential,
      Fin.sum_univ_zero, LinearMap.zero_apply]
  | succ n ih =>
    induction t using PiTensorProduct.induction_on with
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul_tprod r v =>
      simp only [map_smul]
      congr 1
      rw [blockEquiv_succ_symm_tprod, blockEquiv_succ_symm_differential_tprod]
      change delta (partialDeriv (k := k) ell)
        (includeVariables ell Sum.inl (q 0) + includeVariables ell Sum.inr
          (potential (k := k) ell n (fun i => V i.succ) (fun i => q i.succ))) _ = _
      rw [delta_product, ih]
      rfl

end BoundaryOnly.FormalObstruction.GlobalForms

namespace BoundaryOnly.FormalObstruction.GlobalForms
open Frobenius MixedForms FormsSplit SignedTensor
open scoped TensorProduct BigOperators
variable {k : Type*} [Field k] (ell : ℕ) (hell : 0 < ell)

                                                                                 
def insertScalar : ∀ (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)],
    (i : Fin n) → Ring (ι := V i) (k := k) ell →ₐ[k]
      Ring (ι := Coordinates n V) (k := k) ell
  | 0, _, _, _, i => Fin.elim0 i
  | n+1, V, _, _, i => Fin.cases (includeVariables ell Sum.inl)
      (fun i => (includeVariables ell Sum.inr).comp
        (insertScalar n (fun j => V j.succ) i)) i

                                                                                   
def insertForms : ∀ (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)],
    (i : Fin n) → QForms (k := k) ell (V i) →ₐ[k] QForms (k := k) ell (Coordinates n V)
  | 0, _, _, _, i => Fin.elim0 i
  | n+1, V, _, _, i => Fin.cases (includeLeft ell)
      (fun i => (includeRight ell).comp (insertForms n (fun j => V j.succ) i)) i

@[simp] theorem includeLeft_coeff {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (a : Ring (ι := ι) (k := k) ell) :
    includeLeft (κ := κ) ell (coeff a) = coeff (includeVariables ell Sum.inl a) := by
  simp only [includeLeft, coeff_apply, Algebra.TensorProduct.map_tmul, map_one]

@[simp] theorem includeRight_coeff {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (a : Ring (ι := κ) (k := k) ell) :
    includeRight (ι := ι) ell (coeff a) = coeff (includeVariables ell Sum.inr a) := by
  simp only [includeRight, coeff_apply, Algebra.TensorProduct.map_tmul, map_one]

@[simp] theorem insertForms_coeff (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (i : Fin n) (a : Ring (ι := V i) (k := k) ell) :
    insertForms ell n V i (coeff a) = coeff (insertScalar ell n V i a) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact includeLeft_coeff ell a
    | succ i =>
      change includeRight ell (insertForms ell n (fun j => V j.succ) i (coeff a)) = _
      rw [ih, includeRight_coeff]
      rfl

 theorem potential_sum (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (q : ∀ i, Ring (ι := V i) (k := k) ell) :
    potential ell n V q = ∑ i, insertScalar ell n V i (q i) := by
  induction n with
  | zero => simp [potential]
  | succ n ih =>
    rw [potential, ih, map_sum, Fin.sum_univ_succ]
    rfl

 theorem blockEquiv_symm_tprod_prod (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (x : ∀ i, QForms (k := k) ell (V i)) :
    (blockEquiv (k := k) ell hell n V).symm (PiTensorProduct.tprod k x) =
      (List.ofFn fun i => insertForms ell n V i (x i)).prod := by
  induction n with
  | zero =>
    apply (emptyForms (k := k) ell hell).injective
    simp only [blockEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, List.ofFn_zero, List.prod_nil]
    simp [emptyForms, emptyCoefficients, emptyExterior, Algebra.TensorProduct.one_def]
  | succ n ih =>
    rw [blockEquiv_succ_symm_tprod, ih, List.ofFn_succ, List.prod_cons]
    change _ = includeLeft ell (x 0) *
      (List.ofFn fun i => includeRight ell (insertForms ell n (fun j => V j.succ) i (x i.succ))).prod
    rw [map_list_prod, List.map_ofFn]
    rfl

variable [CharP k ell]

 theorem d_insertForms (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (i : Fin n) (x : QForms (k := k) ell (V i)) :
    d (partialDeriv ell) (insertForms ell n V i x) =
      insertForms ell n V i (d (partialDeriv ell) x) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact d_includeLeft ell x
    | succ i =>
      change d (partialDeriv ell) (includeRight ell (insertForms ell n (fun j => V j.succ) i x)) = _
      rw [d_includeRight, ih]
      rfl

 theorem gradient_insertScalar (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (i : Fin n) (q : Ring (ι := V i) (k := k) ell) :
    gradient (partialDeriv ell) (insertScalar ell n V i q) =
      insertForms ell n V i (gradient (partialDeriv ell) q) := by
  rw [← d_coeff, ← insertForms_coeff, d_insertForms, d_coeff]

 theorem delta_insertForms (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (i : Fin n) (q : Ring (ι := V i) (k := k) ell) (x : QForms (k := k) ell (V i)) :
    delta (partialDeriv ell) (insertScalar ell n V i q) (insertForms ell n V i x) =
      insertForms ell n V i (delta (partialDeriv ell) q x) := by
  rw [delta_apply, gradient_insertScalar, delta_apply, map_mul]

end BoundaryOnly.FormalObstruction.GlobalForms

namespace BoundaryOnly.FormalObstruction.GlobalForms
open Frobenius MixedForms FormsSplit
open scoped BigOperators TensorProduct
variable {k : Type*} [Field k]

def sigmaSucc {n : ℕ} (V : Fin (n+1) → Type) :
    (Σ i, V i) ≃ V 0 ⊕ (Σ i : Fin n, V i.succ) where
  toFun x := Fin.cases (fun y => Sum.inl y) (fun i y => Sum.inr ⟨i,y⟩) x.1 x.2
  invFun := Sum.elim (fun y => ⟨0,y⟩) (fun y => ⟨y.1.succ,y.2⟩)
  left_inv := by rintro ⟨i,y⟩; cases i using Fin.cases <;> rfl
  right_inv := by intro y; cases y <;> rfl

def coordinateEquiv : ∀ (n : ℕ) (V : Fin n → Type), Coordinates n V ≃ (Σ i, V i)
  | 0, _ => Equiv.equivOfIsEmpty _ _
  | n+1, V => (Equiv.sumCongr (Equiv.refl (V 0))
      (coordinateEquiv n (fun i => V i.succ))).trans (sigmaSucc V).symm

@[simp] theorem coordinateEquiv_zero {n : ℕ} (V : Fin (n+1) → Type) (y : V 0) :
    coordinateEquiv (n+1) V (Sum.inl y) = ⟨0,y⟩ := rfl

@[simp] theorem coordinateEquiv_succ {n : ℕ} (V : Fin (n+1) → Type)
    (y : Coordinates n (fun i => V i.succ)) :
    coordinateEquiv (n+1) V (Sum.inr y) =
      ⟨(coordinateEquiv n (fun i => V i.succ) y).1.succ,
        (coordinateEquiv n (fun i => V i.succ) y).2⟩ := rfl

@[simp] theorem coordinateEquiv_symm_zero {n : ℕ} (V : Fin (n+1) → Type) (y : V 0) :
    (coordinateEquiv (n+1) V).symm ⟨0,y⟩ = Sum.inl y := rfl

@[simp] theorem coordinateEquiv_symm_succ {n : ℕ} (V : Fin (n+1) → Type)
    (i : Fin n) (y : V i.succ) :
    (coordinateEquiv (n+1) V).symm ⟨i.succ,y⟩ =
      Sum.inr ((coordinateEquiv n (fun i => V i.succ)).symm ⟨i,y⟩) := rfl

variable (ell : ℕ)
@[simp] theorem insertScalar_coordinate (n : ℕ) (V : Fin n → Type)
    [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (i : Fin n) (y : V i) :
    insertScalar (k := k) ell n V i (coordinate ell y) =
      coordinate ell ((coordinateEquiv n V).symm ⟨i,y⟩) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => exact includeVariables_coordinate ell Sum.inl y
    | succ i =>
      change includeVariables ell Sum.inr
        (insertScalar ell n (fun i => V i.succ) i (coordinate ell y)) = _
      rw [ih, includeVariables_coordinate]
      rfl

end BoundaryOnly.FormalObstruction.GlobalForms

end

end OAI
