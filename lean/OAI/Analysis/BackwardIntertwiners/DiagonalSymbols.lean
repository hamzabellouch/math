import OAI.Analysis.BackwardIntertwiners.OrdinaryStructure

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal


open scoped Classical

def diagonalSymbols : StarSubalgebra ℂ (Base → ℤ → ℂ) where
  carrier := {a | (∀ j, Measurable (fun x => a x j)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x j, ‖a x j‖ ≤ C}
  zero_mem' := ⟨fun _ => measurable_const, 0, le_rfl, by simp⟩
  one_mem' := ⟨fun _ => measurable_const, 1, zero_le_one, by simp⟩
  add_mem' := by
    rintro a b ⟨ha,C,hC,hCa⟩ ⟨hb,D,hD,hDb⟩
    exact ⟨fun j => (ha j).add (hb j), C+D, add_nonneg hC hD,
      fun x j => (norm_add_le _ _).trans (add_le_add (hCa x j) (hDb x j))⟩
  mul_mem' := by
    rintro a b ⟨ha,C,hC,hCa⟩ ⟨hb,D,hD,hDb⟩
    refine ⟨fun j => (ha j).mul (hb j), C*D, mul_nonneg hC hD, fun x j => ?_⟩
    change ‖a x j * b x j‖ ≤ C*D
    rw [norm_mul]
    exact mul_le_mul (hCa x j) (hDb x j) (norm_nonneg _) hC
  algebraMap_mem' c := ⟨fun _ => measurable_const, ‖c‖, norm_nonneg c, fun _ _ => le_rfl⟩
  star_mem' := by
    rintro a ⟨ha,C,hC,hCa⟩
    refine ⟨fun j => continuous_star.measurable.comp (ha j), C,hC, fun x j => ?_⟩
    simpa using hCa x j
abbrev DiagonalSymbol := ↥diagonalSymbols
namespace DiagonalSymbol
instance : CoeFun DiagonalSymbol (fun _ => Base → ℤ → ℂ) := ⟨fun a => a.val⟩
lemma measurable (a : DiagonalSymbol) (j : ℤ) : Measurable (fun x => a x j) := a.property.1 j
noncomputable def bound (a : DiagonalSymbol) : ℝ := a.property.2.choose
lemma bound_nonneg (a : DiagonalSymbol) : 0 ≤ a.bound := a.property.2.choose_spec.1
lemma norm_le_bound (a : DiagonalSymbol) (x : Base) (j : ℤ) : ‖a x j‖ ≤ a.bound :=
  a.property.2.choose_spec.2 x j
@[simp] lemma zero_apply (x : Base) (j : ℤ) : (0 : DiagonalSymbol) x j = 0 := rfl
@[simp] lemma one_apply (x : Base) (j : ℤ) : (1 : DiagonalSymbol) x j = 1 := rfl
@[simp] lemma add_apply (a b : DiagonalSymbol) (x : Base) (j : ℤ) : (a+b) x j = a x j + b x j := rfl
@[simp] lemma mul_apply (a b : DiagonalSymbol) (x : Base) (j : ℤ) : (a*b) x j = a x j * b x j := rfl
@[simp] lemma sub_apply (a b : DiagonalSymbol) (x : Base) (j : ℤ) : (a-b) x j = a x j - b x j := rfl
@[simp] lemma star_apply (a : DiagonalSymbol) (x : Base) (j : ℤ) : (star a) x j = star (a x j) := rfl
@[simp] lemma smul_apply (c : ℂ) (a : DiagonalSymbol) (x : Base) (j : ℤ) : (c • a) x j = c * a x j := rfl
@[simp] lemma algebraMap_apply (c : ℂ) (x : Base) (j : ℤ) :
    algebraMap ℂ DiagonalSymbol c x j = c := rfl
@[simp] lemma pow_apply (a : DiagonalSymbol) (n : ℕ) (x : Base) (j : ℤ) :
    (a^n) x j = (a x j)^n := by induction n <;> simp_all [pow_succ]
end DiagonalSymbol

def diagonalFiber (a : DiagonalSymbol) (x : Base) : Fiber →L[ℂ] Fiber :=
  fiberMultiplier (a x) a.bound a.bound_nonneg (a.norm_le_bound x)
@[simp] lemma diagonalFiber_apply (a : DiagonalSymbol) (x : Base) (v : Fiber) (j : ℤ) :
    diagonalFiber a x v j = a x j*v j := rfl
lemma diagonalFiber_norm (a : DiagonalSymbol) (x : Base) : ‖diagonalFiber a x‖ ≤ a.bound :=
  fiberMultiplier_norm_le _ _ _ _
lemma diagonalFiber_measurable (a : DiagonalSymbol) (f : Base → Fiber)
    (hf : AEStronglyMeasurable f baseMeasure) :
    AEStronglyMeasurable (fun x => diagonalFiber a x (f x)) baseMeasure :=
  weightedPermutation_aestronglyMeasurable (Equiv.refl ℤ) a a.bound a.bound_nonneg
    a.norm_le_bound a.measurable hf

def diagonalOperator (a : DiagonalSymbol) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  fieldOperator (diagonalFiber a) a.bound a.bound_nonneg (diagonalFiber_norm a)
    (diagonalFiber_measurable a)
lemma diagonalOperator_ae (a : DiagonalSymbol) (f : GlobalHilbert) :
    diagonalOperator a f =ᵐ[baseMeasure] fun x => diagonalFiber a x (f x) :=
  fieldOperator_ae _ _ _ _ _ _
lemma diagonalOperator_coord (a : DiagonalSymbol) (f : GlobalHilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ j, diagonalOperator a f x j = a x j*f x j := by
  filter_upwards [diagonalOperator_ae a f] with x hx j
  rw [hx]; rfl
lemma diagonalOperator_norm_le (a : DiagonalSymbol) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ x j, ‖a x j‖ ≤ C) : ‖diagonalOperator a‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  calc
    _ ≤ ‖(C:ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [diagonalOperator_ae a f, Lp.coeFn_smul (C:ℂ) f] with x hx hs
      rw [hx,hs,Pi.smul_apply]
      apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
      intro j
      simp only [diagonalFiber_apply,lp.coeFn_smul,Pi.smul_apply,norm_smul,norm_mul,
        Complex.norm_real,Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha x j) (norm_nonneg _)
    _ = C*‖f‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]
lemma diagonalOperator_zero : diagonalOperator 0 = 0 := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord 0 f,Lp.coeFn_zero Fiber 2 baseMeasure] with x hx h0
  ext j
  change diagonalOperator 0 f x j = (0 : GlobalHilbert) x j
  rw [hx,h0]; simp
lemma diagonalOperator_one : diagonalOperator 1 = 1 := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord 1 f] with x hx
  ext j
  simpa using hx j
lemma diagonalOperator_add (a b : DiagonalSymbol) :
    diagonalOperator (a+b) = diagonalOperator a + diagonalOperator b := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord (a+b) f, diagonalOperator_coord a f,
    diagonalOperator_coord b f, Lp.coeFn_add (diagonalOperator a f) (diagonalOperator b f)] with x hab ha hb hs
  ext j
  change diagonalOperator (a+b) f x j = (diagonalOperator a f + diagonalOperator b f) x j
  rw [hs,Pi.add_apply,lp.coeFn_add,Pi.add_apply,hab,ha,hb,DiagonalSymbol.add_apply,add_mul]
lemma diagonalOperator_mul (a b : DiagonalSymbol) :
    diagonalOperator (a*b) = diagonalOperator a * diagonalOperator b := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord (a*b) f, diagonalOperator_coord a (diagonalOperator b f),
    diagonalOperator_coord b f] with x hab ha hb
  ext j
  change diagonalOperator (a*b) f x j = diagonalOperator a (diagonalOperator b f) x j
  rw [hab,ha,hb,DiagonalSymbol.mul_apply,mul_assoc]
lemma diagonalOperator_smul (c : ℂ) (a : DiagonalSymbol) :
    diagonalOperator (c • a) = c • diagonalOperator a := by
  ext1 f
  apply Lp.ext
  filter_upwards [diagonalOperator_coord (c • a) f, diagonalOperator_coord a f,
    Lp.coeFn_smul c (diagonalOperator a f)] with x hca ha hs
  ext j
  change diagonalOperator (c • a) f x j = (c • diagonalOperator a f) x j
  rw [hs,Pi.smul_apply,lp.coeFn_smul,Pi.smul_apply,hca,ha,DiagonalSymbol.smul_apply,smul_eq_mul,mul_assoc]
lemma diagonalFiber_inner (a : DiagonalSymbol) (x : Base) (v z : Fiber) :
    inner ℂ (diagonalFiber a x v) z = inner ℂ v (diagonalFiber (star a) x z) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  simp only [diagonalFiber_apply,DiagonalSymbol.star_apply,RCLike.inner_apply,map_mul,starRingEnd_apply]
  ring
lemma diagonalOperator_star (a : DiagonalSymbol) :
    diagonalOperator (star a) = star (diagonalOperator a) := by
  ext1 f
  apply ext_inner_left ℂ
  intro g
  change inner ℂ g (diagonalOperator (star a) f) = inner ℂ g ((diagonalOperator a).adjoint f)
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [diagonalOperator_ae (star a) f, diagonalOperator_ae a g] with x hf hg
  rw [hf,hg,diagonalFiber_inner]

def diagonalRepresentation : DiagonalSymbol →⋆ₐ[ℂ] (GlobalHilbert →L[ℂ] GlobalHilbert) where
  toFun := diagonalOperator
  map_zero' := diagonalOperator_zero
  map_one' := diagonalOperator_one
  map_add' := diagonalOperator_add
  map_mul' := diagonalOperator_mul
  map_star' := diagonalOperator_star
  commutes' c := by
    have he : algebraMap ℂ DiagonalSymbol c = c • (1 : DiagonalSymbol) := by
      apply Subtype.ext
      funext x j
      simp
    rw [he,diagonalOperator_smul,diagonalOperator_one]
    exact (Algebra.algebraMap_eq_smul_one c).symm

def fullMultiplierAlgebra : StarSubalgebra ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) :=
  diagonalRepresentation.range



end
end BackwardIntertwiners

end OAI
