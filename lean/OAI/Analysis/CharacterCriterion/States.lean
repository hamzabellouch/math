import OAI.Analysis.CharacterCriterion.NoncommutingPair

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology


open NormedSpace
open scoped ComplexOrder
namespace KirchbergRordam.GenericRW
namespace States

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

lemma norm_rotation (a : A) (ha : IsSelfAdjoint a) (t : ℝ) :
    ‖exp (t • (Complex.I • a))‖ = 1 := by
  have he : exp (t • (Complex.I • a)) =
      (selfAdjoint.expUnitary (t • (⟨a, ha⟩ : selfAdjoint A)) : A) := by
    change exp (t • (Complex.I • a)) = exp (Complex.I • t • a)
    rw [smul_comm]
  rw [he, CStarRing.norm_coe_unitary]

lemma eval_selfAdjoint_im_zero (φ : A →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) (h1 : φ 1 = 1)
    (a : A) (ha : IsSelfAdjoint a) : (φ a).im = 0 := by
  let l : A →L[ℝ] ℝ := Complex.reCLM.comp (φ.restrictScalars ℝ)
  have hd : HasDerivAt (fun t : ℝ => l (exp (t • (Complex.I • a))))
      (-(φ a).im) 0 := by
    have hh := l.hasFDerivAt.comp_hasDerivAt 0
      (hasDerivAt_exp_smul_const (Complex.I • a) (0 : ℝ))
    convert hh using 1 <;> first | rfl | simp [l, map_smul, Complex.mul_re]
  have hmax : IsLocalMax (fun t : ℝ => l (exp (t • (Complex.I • a)))) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change (φ (exp (t • (Complex.I • a)))).re ≤ (φ (exp ((0 : ℝ) • (Complex.I • a)))).re
    simp only [zero_smul, exp_zero, h1, Complex.one_re]
    exact (Complex.re_le_norm _).trans <|
      (φ.le_opNorm _).trans <| by rw [norm_rotation a ha t, mul_one]; exact hφ
  exact neg_eq_zero.mp (hmax.hasDerivAt_eq_zero hd)

variable [PartialOrder A] [StarOrderedRing A]

lemma eval_nonneg (φ : A →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ 1) (h1 : φ 1 = 1)
    (a : A) (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hi := eval_selfAdjoint_im_zero φ hφ h1 a (IsSelfAdjoint.of_nonneg ha)
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, hi.symm⟩
  by_cases hz : a = 0
  · simp [hz]
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr hz
  let b := ‖a‖⁻¹ • a
  have hb : 0 ≤ b := smul_nonneg (inv_nonneg.mpr hn.le) ha
  have hbn : ‖b‖ ≤ 1 := by
    dsimp [b]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hb1 : b ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg b hb).mp hbn
  have hn1 : ‖1 - b‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (sub_nonneg.mpr hb1)).mpr (sub_le_self _ hb)
  have hh : (φ (1 - b)).re ≤ 1 :=
    (Complex.re_le_norm _).trans <| (φ.le_opNorm _).trans <|
      (mul_le_mul_of_nonneg_left hn1 (norm_nonneg φ)).trans (by simpa using hφ)
  rw [map_sub, h1, Complex.sub_re, Complex.one_re] at hh
  have hbr : (φ b).re = ‖a‖⁻¹ * (φ a).re := by
    dsimp [b]
    change ((φ.restrictScalars ℝ) (‖a‖⁻¹ • a)).re = _
    rw [map_smul]
    simp
  rw [hbr] at hh
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hn)).mp (by linarith : 0 ≤ ‖a‖⁻¹ * (φ a).re)


theorem exists_state : ∃ φ : A →ₚ[ℂ] ℂ, φ 1 = 1 := by
  obtain ⟨φ, hφ, h1⟩ := exists_dual_vector ℂ (1 : A) (by simp)
  have h1 : φ 1 = 1 := by simpa using h1
  exact ⟨PositiveLinearMap.mk₀ φ.toLinearMap (eval_nonneg φ hφ.le h1), h1⟩

end States
end KirchbergRordam.GenericRW


open scoped ComplexOrder
namespace KirchbergRordam.GenericRW
namespace PureStates
variable (A : Type*) [CStarAlgebra A]

def normStates : Set (WeakDual ℂ A) := {φ | ‖φ.toStrongDual‖ ≤ 1 ∧ φ 1 = 1}

def evaluationReal : WeakDual ℂ A →ₗ[ℝ] (A → ℂ) where
  toFun φ := φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance locallyConvexReal : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
  LocallyConvexSpace.induced (evaluationReal A)

lemma normStates_compact : IsCompact (normStates A) := by
  have h := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).inter_right
    (isClosed_eq (WeakDual.eval_continuous (1 : A)) (continuous_const (y := (1 : ℂ))))
  convert h using 1
  ext φ
  simp [normStates, Metric.mem_closedBall]

variable [Nontrivial A]

lemma normStates_nonempty : (normStates A).Nonempty := by
  obtain ⟨φ, hφ, h1⟩ := exists_dual_vector ℂ (1 : A) (by simp)
  refine ⟨(StrongDual.toWeakDual φ), hφ.le, ?_⟩
  simpa using h1


def IsPure (φ : A →L[ℂ] ℂ) : Prop :=
  (StrongDual.toWeakDual φ) ∈ (normStates A).extremePoints ℝ

theorem exists_pure : ∃ φ : A →L[ℂ] ℂ, IsPure A φ := by
  obtain ⟨φ, hφ⟩ := (normStates_compact A).extremePoints_nonempty (normStates_nonempty A)
  exact ⟨φ.toStrongDual, hφ⟩

variable {A}

omit [Nontrivial A] in
lemma IsPure.norm_le_one {φ : A →L[ℂ] ℂ} (hp : IsPure A φ) : ‖φ‖ ≤ 1 := hp.1.1
omit [Nontrivial A] in
lemma IsPure.map_one {φ : A →L[ℂ] ℂ} (hp : IsPure A φ) : φ 1 = 1 := hp.1.2

omit [Nontrivial A] in
lemma IsPure.extreme {φ ψ χ : A →L[ℂ] ℂ} (hp : IsPure A φ)
    (hψ : ‖ψ‖ ≤ 1) (hψ1 : ψ 1 = 1) (hχ : ‖χ‖ ≤ 1) (hχ1 : χ 1 = 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (he : φ = t • ψ + (1 - t) • χ) : ψ = φ := by
  apply StrongDual.toWeakDual.injective
  apply hp.2 (show (StrongDual.toWeakDual ψ) ∈ normStates A from ⟨hψ, hψ1⟩)
    (show (StrongDual.toWeakDual χ) ∈ normStates A from ⟨hχ, hχ1⟩)
  exact ⟨t, 1 - t, ht, sub_pos.mpr ht1, by ring, by
    change t • ψ + (1 - t) • χ = φ
    exact he.symm⟩

end PureStates
end KirchbergRordam.GenericRW
end

end OAI
