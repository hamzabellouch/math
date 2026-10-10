import OAI.Analysis.WeakInfiniteness.NonunitalSchwarz
import OAI.Analysis.Nuclearity.CompletedConjugation

namespace OAI

/-! A completely positive map is contractive when it is contractive on
positive elements. The argument normalizes by the operator norm
and applies Schwarz once; no quantitative limit is needed. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem cp_norm_le_one_of_positive_bound (T : A →L[ℂ] B)
    (hT : CompletelyPositive T) (hpos : ∀ a, 0 ≤ a → ‖T a‖ ≤ ‖a‖) : ‖T‖ ≤ 1 := by
  by_cases hz : ‖T‖ = 0
  · rw [hz]
    exact zero_le_one
  have hn : 0 < ‖T‖ := lt_of_le_of_ne (norm_nonneg T) (Ne.symm hz)
  let S : A →L[ℂ] B := ‖T‖⁻¹ • T
  have hS : CompletelyPositive S := by
    intro n M hM
    change 0 ≤ (‖T‖⁻¹ : ℝ) • matrixLinearMap T M
    exact smul_nonneg (inv_nonneg.mpr hn.le) (hT n M hM)
  have hSn : ‖S‖ ≤ 1 := by
    dsimp only [S]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hz]
  have hsq (a : A) : ‖T a‖ ^ 2 ≤ ‖T‖ * ‖a‖ ^ 2 := by
    have hs := completelyPositive_schwarz_nonunital_domain hS hSn a
    have hb := CStarAlgebra.norm_le_norm_of_le_of_nonneg hs (star_mul_self_nonneg (S a))
    rw [CStarRing.norm_star_mul_self] at hb
    have hp := hpos (star a * a) (star_mul_self_nonneg a)
    rw [CStarRing.norm_star_mul_self] at hp
    have hval (b : A) : ‖S b‖ = ‖T‖⁻¹ * ‖T b‖ := by
      simp only [S, smul_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn)]
    rw [hval, hval] at hb
    calc
      ‖T a‖ ^ 2 = ‖T‖ ^ 2 * (‖T‖⁻¹ * ‖T a‖) ^ 2 := by field_simp
      _ ≤ ‖T‖ ^ 2 * (‖T‖⁻¹ * ‖T (star a * a)‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [pow_two] using hb) (sq_nonneg _)
      _ = ‖T‖ * ‖T (star a * a)‖ := by field_simp
      _ ≤ ‖T‖ * ‖a‖ ^ 2 := mul_le_mul_of_nonneg_left (by simpa only [pow_two] using hp) hn.le
  have hbound : ‖T‖ ≤ Real.sqrt ‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro a
    have h := hsq a
    apply (sq_le_sq₀ (norm_nonneg (T a))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg a))).mp
    simpa only [mul_pow, Real.sq_sqrt hn.le] using h
  have hs := Real.sq_sqrt hn.le
  nlinarith [Real.sqrt_nonneg ‖T‖]

section NonunitalTarget

variable {X Y : Type*} [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
  [PartialOrder X] [StarOrderedRing X] [PartialOrder Y] [StarOrderedRing Y]

local instance cpNormUnitizationOrder : PartialOrder (Unitization ℂ Y) := CStarAlgebra.spectralOrder _
local instance cpNormUnitizationOrdered : StarOrderedRing (Unitization ℂ Y) := CStarAlgebra.spectralOrderedRing _

theorem cp_norm_le_one_of_positive_bound_nonunital (T : X →L[ℂ] Y)
    (hT : CompletelyPositive T) (hpos : ∀ a, 0 ≤ a → ‖T a‖ ≤ ‖a‖) : ‖T‖ ≤ 1 := by
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ Y
  let F := (starHomContinuousLinear ι).comp T
  have hF : CompletelyPositive F := by
    intro n M hM
    exact map_nonneg (CStarMatrix.mapₙₐ ι) (hT n M hM)
  have hval (a : X) : F a = (T a : Unitization ℂ Y) := rfl
  have hFn : ‖F‖ ≤ 1 := cp_norm_le_one_of_positive_bound F hF (by
    intro a ha
    rw [hval, Unitization.norm_inr]
    exact hpos a ha)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  calc
    ‖T a‖ = ‖F a‖ := by rw [hval, Unitization.norm_inr]
    _ ≤ ‖F‖ * ‖a‖ := F.le_opNorm a
    _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right hFn (norm_nonneg a)

end NonunitalTarget

end WeakPureInfiniteness

end

end OAI
