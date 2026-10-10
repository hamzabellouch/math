import Mathlib
import OAI.Algebra.FrobeniusObstruction.BlockPairing
import OAI.Algebra.FrobeniusObstruction.ParameterLifts

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.ActualBlocks
open Frobenius MixedForms FormsSplit GlobalForms SignedTensor
open scoped TensorProduct BigOperators
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}

abbrev Variables (n : Fin d → ℕ) (i : Fin d) := Bool × Fin (n i)

def grouping : (Σ i, Variables n i) ≃ InternalVar n where
  toFun x := (x.2.1, ⟨x.1,x.2.2⟩)
  invFun x := ⟨x.2.1,(x.1,x.2.2)⟩
  left_inv := by rintro ⟨i,b,y⟩; rfl
  right_inv := by rintro ⟨b,i,y⟩; rfl

def coordinates : Coordinates d (Variables n) ≃ InternalVar n :=
  (coordinateEquiv d (Variables n)).trans grouping

variable (ell : ℕ) [Fact ell.Prime] [CharP k ell]

abbrev Scalar (i : Fin d) := Frobenius.Ring (ι := Variables n i) (k := k) ell
abbrev Block (i : Fin d) := GlobalForms.QForms (k := k) ell (Variables n i)
abbrev Ambient := GlobalForms.QForms (k := k) ell (InternalVar n)

def includeScalar (i : Fin d) : Scalar (n := n) (k := k) ell i →ₐ[k]
    Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  includeVariables ell (fun y => (y.1,⟨i,y.2⟩))

def includeBlock (i : Fin d) : Block (n := n) (k := k) ell i →ₐ[k]
    Ambient (n := n) (k := k) ell :=
  (FormsReindex.equiv ell coordinates).toAlgHom.comp
    (insertForms ell d (Variables n) i)

omit [Fact ell.Prime] [CharP k ell] in
@[simp] theorem reindex_insertScalar (i : Fin d) (a : Scalar (n := n) (k := k) ell i) :
    Frobenius.reindex ell coordinates (insertScalar ell d (Variables n) i a) =
      includeScalar ell i a := by
  have h : (Frobenius.reindex (k := k) ell (coordinates (n := n))).toAlgHom.comp
      (insertScalar ell d (Variables n) i) = includeScalar ell i := by
    apply algHom_ext
    intro y
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, insertScalar_coordinate, reindex_coordinate,
      includeScalar, includeVariables_coordinate]
    congr 1
    change grouping (coordinateEquiv d (Variables n) ((coordinateEquiv d (Variables n)).symm ⟨i,y⟩)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  exact AlgHom.congr_fun h a

omit [Fact ell.Prime] [CharP k ell] in
@[simp] theorem includeBlock_coeff (i : Fin d) (a : Scalar (n := n) (k := k) ell i) :
    includeBlock ell i (coeff a) = coeff (includeScalar ell i a) := by
  simp only [includeBlock, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, insertForms_coeff,
    FormsReindex.equiv_coeff, reindex_insertScalar]

def wall (b : Bool) (i : Fin d) :
    Frobenius.Ring (ι := WallVar n i) (k := k) ell →ₐ[k] Scalar (n := n) (k := k) ell i :=
  eval ell (Sum.elim (fun _ => 0) (fun y => coordinate ell (b,y))) (by
    intro v
    cases v with
    | inl _ => exact zero_pow (Nat.Prime.ne_zero Fact.out)
    | inr _ => exact coordinate_pow ell _)

omit [CharP k ell] in
@[simp] theorem include_wall (b : Bool) (i : Fin d)
    (x : Frobenius.Ring (ι := WallVar n i) (k := k) ell) :
    includeScalar ell i (wall ell b i x) = wallSpecial ell b i x := by
  have h : (includeScalar (n := n) (k := k) ell i).comp (wall ell b i) = wallSpecial ell b i := by
    apply algHom_ext
    intro y
    simp only [AlgHom.comp_apply, wall, eval_coordinate]
    cases y with
    | inl j => simp only [Sum.elim_inl, map_zero, wallSpecial_slope]
    | inr y => simp only [Sum.elim_inr, includeScalar, includeVariables_coordinate,
        wallSpecial_internal]
  exact AlgHom.congr_fun h x

def blockPotential (D : FormalData (k := k) n) (i : Fin d) : Scalar (n := n) (k := k) ell i :=
  wall ell true i (Ideal.Quotient.mk _ (D.P i)) -
    wall ell false i (Ideal.Quotient.mk _ (D.P i))

def blockSlope (D : FormalData (k := k) n) (i : Fin d) : Scalar (n := n) (k := k) ell i :=
  includeVariables ell (fun y => (true,y)) (Ideal.Quotient.mk _ (slopeDerivative n D.P i))

omit [Fact ell.Prime] [CharP k ell] in
@[simp] theorem include_blockSlope (D : FormalData (k := k) n) (i : Fin d) :
    includeScalar ell i (blockSlope ell D i) = specialSlope ell D true i := by
  have h : (includeScalar (k := k) ell i).comp (includeVariables ell (fun y : Fin (n i) => (true,y))) =
      includeVariables ell (fun y : Fin (n i) => (true,⟨i,y⟩)) := by
    apply algHom_ext
    intro y
    simp only [AlgHom.comp_apply, includeVariables_coordinate, includeScalar]
  exact AlgHom.congr_fun h (Ideal.Quotient.mk _ (slopeDerivative n D.P i))

@[simp] theorem reindex_potential (D : FormalData (k := k) n) :
    Frobenius.reindex ell coordinates
      (GlobalForms.potential ell d (Variables n) (blockPotential ell D)) =
      specialPotential ell D := by
  rw [GlobalForms.potential_sum, map_sum, specialPotential_separated]
  apply Finset.sum_congr rfl
  intro i _
  rw [reindex_insertScalar]
  simp only [blockPotential, map_sub, include_wall]

variable (hell : 0 < ell)

def tensorToForms : (⨂[k] i, Block (n := n) (k := k) ell i) ≃ₗ[k]
    Ambient (n := n) (k := k) ell :=
  (blockEquiv (k := k) ell hell d (Variables n)).symm.trans
    (FormsReindex.equiv ell coordinates).toLinearEquiv

omit [Fact ell.Prime] [CharP k ell] in
@[simp] theorem tensorToForms_tprod (x : ∀ i, Block (n := n) (k := k) ell i) :
    tensorToForms ell hell (PiTensorProduct.tprod k x) =
      (List.ofFn fun i => includeBlock ell i (x i)).prod := by
  change FormsReindex.equiv ell coordinates
    ((blockEquiv ell hell d (Variables n)).symm (PiTensorProduct.tprod k x)) = _
  rw [blockEquiv_symm_tprod_prod, map_list_prod, List.map_ofFn]
  rfl

omit [Fact ell.Prime] in
@[simp] theorem tensorToForms_D (x : ⨂[k] i, Block (n := n) (k := k) ell i) :
    tensorToForms ell hell (differential (Block (n := n) (k := k) ell)
      (fun i => (parity (k := k) (A := Scalar (n := n) (k := k) ell i) (ι := Variables n i)).toLinearMap)
      (fun i => MixedForms.d (partialDeriv (ι := Variables n i) (k := k) ell)) x) =
      MixedForms.d (partialDeriv ell) (tensorToForms ell hell x) := by
  change FormsReindex.equiv ell coordinates ((blockEquiv ell hell d (Variables n)).symm _) = _
  rw [← blockEquiv_symm_d, FormsReindex.equiv_d]
  rfl

@[simp] theorem tensorToForms_delta (D : FormalData (k := k) n)
    (x : ⨂[k] i, Block (n := n) (k := k) ell i) :
    tensorToForms ell hell (differential (Block (n := n) (k := k) ell)
      (fun i => (parity (k := k) (A := Scalar (n := n) (k := k) ell i) (ι := Variables n i)).toLinearMap)
      (fun i => delta (partialDeriv (ι := Variables n i) (k := k) ell) (blockPotential ell D i)) x) =
      delta (partialDeriv ell) (specialPotential ell D) (tensorToForms ell hell x) := by
  change FormsReindex.equiv ell coordinates ((blockEquiv ell hell d (Variables n)).symm _) = _
  rw [← blockEquiv_symm_delta, FormsReindex.equiv_delta, reindex_potential]
  rfl

omit [Fact ell.Prime] in
 theorem d_includeBlock (i : Fin d) (x : Block (n := n) (k := k) ell i) :
    MixedForms.d (partialDeriv ell) (includeBlock ell i x) =
      includeBlock ell i (MixedForms.d (partialDeriv ell) x) := by
  simp only [includeBlock, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ← FormsReindex.equiv_d, d_insertForms]

omit [Fact ell.Prime] in
 theorem gradient_includeScalar (i : Fin d) (a : Scalar (n := n) (k := k) ell i) :
    gradient (partialDeriv ell) (includeScalar ell i a) =
      includeBlock ell i (gradient (partialDeriv ell) a) := by
  rw [← d_coeff, ← includeBlock_coeff, d_includeBlock, d_coeff]

omit [Fact ell.Prime] in
 theorem delta_includeBlock (i : Fin d) (a : Scalar (n := n) (k := k) ell i)
    (x : Block (n := n) (k := k) ell i) :
    delta (partialDeriv ell) (includeScalar ell i a) (includeBlock ell i x) =
      includeBlock ell i (delta (partialDeriv ell) a x) := by
  rw [delta_apply, delta_apply, gradient_includeScalar, map_mul]

end BoundaryOnly.FormalObstruction.ActualBlocks

namespace BoundaryOnly.FormalObstruction.MixedForms
variable {k A ι t : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem list_prod_coeff_mul (l : List t) (a : t → A)
    (x : t → Forms (k := k) (A := A) (ι := ι)) :
    (l.map (fun i => coeff (a i) * x i)).prod =
      coeff ((l.map a).prod) * (l.map x).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, map_one, one_mul]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, ih, map_mul]
    rw [mul_assoc (coeff (a i)), ← mul_assoc (x i), ← coeff_commute,
      mul_assoc, mul_assoc]

theorem left_cycle_mul_delta (pd : ι → Derivation k A A) (F : A)
    (x y : Forms (k := k) (A := A) (ι := ι)) (hx : delta pd F x = 0) :
    x * delta pd F y = 0 := by
  have hp : gradient pd F * parity x = 0 := by
    have h := congrArg parity hx
    simpa only [delta_apply, map_mul, parity_gradient, neg_mul,
      map_zero, neg_eq_zero] using h
  rw [gradient_supercommute, parity_sq] at hp
  rw [delta_apply, ← mul_assoc, hp, zero_mul]

end BoundaryOnly.FormalObstruction.MixedForms

namespace BoundaryOnly.FormalObstruction.ActualBlocks
open Frobenius MixedForms FormsSplit GlobalForms SignedTensor
open scoped TensorProduct BigOperators
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) [Fact ell.Prime] [CharP k ell] (hell : 0 < ell)

omit [Fact ell.Prime] [CharP k ell] in
 theorem tensorToForms_S (s : ∀ i, Scalar (n := n) (k := k) ell i)
    (I : Finset (Fin d)) (z : ⨂[k] i, Block (n := n) (k := k) ell i) :
    tensorToForms ell hell
      (tensorAction (Block (n := n) (k := k) ell) (BlockTensor.S s) I z) =
      coeff (∏ i ∈ I, includeScalar ell i (s i)) * tensorToForms ell hell z := by
  induction z using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]
  | smul_tprod r x =>
    simp only [map_smul, mul_smul_comm]
    congr 1
    rw [tensorAction, PiTensorProduct.map_tprod, tensorToForms_tprod, tensorToForms_tprod]
    have h (i : Fin d) :
        includeBlock ell i ((if i ∈ I then BlockTensor.S s i else LinearMap.id) (x i)) =
          coeff (if i ∈ I then includeScalar ell i (s i) else 1) * includeBlock ell i (x i) := by
      by_cases hi : i ∈ I
      · simp only [ite_eq_left hi]
        change includeBlock ell i (coeff (s i)*x i) = _
        rw [map_mul, includeBlock_coeff]
      · simp only [ite_eq_right hi, LinearMap.id_apply, map_one, one_mul]
    change (List.ofFn (fun i => includeBlock ell i
      ((if i ∈ I then BlockTensor.S s i else LinearMap.id) (x i)))).prod = _
    have hh : (List.ofFn (fun i => includeBlock ell i
        ((if i ∈ I then BlockTensor.S s i else LinearMap.id) (x i)))) =
        List.ofFn (fun i => coeff (if i ∈ I then includeScalar ell i (s i) else 1) *
          includeBlock ell i (x i)) := by
      apply congrArg List.ofFn
      funext i
      exact h i
    rw [hh]
    have hp := list_prod_coeff_mul (k := k) (ι := InternalVar n)
      (List.ofFn (fun i : Fin d => i))
      (fun i => if i ∈ I then includeScalar ell i (s i) else 1)
      (fun i => includeBlock ell i (x i))
    simp only [List.map_ofFn, Function.comp_def] at hp
    rw [hp]
    congr 2
    rw [List.prod_ofFn, Finset.prod_ite_mem_eq]

end BoundaryOnly.FormalObstruction.ActualBlocks

end

end OAI
