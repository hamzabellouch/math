import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroPolynomial
import OAI.NumberTheory.Ostmann.Characters.CharacterDiskGrowth

namespace OAI

/-! # The actual finite zero set removed around a horizontal contour edge -/

namespace Ostmann

open Metric Set MeromorphicOn
open scoped BigOperators Classical

noncomputable def characterContourDivisor (χ : PrimitiveComplexCharacter) (t : ℝ) :=
  divisor χ.L (closedBall (characterZeroCenter t) (21 / 8 : ℝ))

noncomputable def characterContourZeros (χ : PrimitiveComplexCharacter) (t : ℝ) : Finset ℂ :=
  ((characterContourDivisor χ t).finiteSupport
    (isCompact_closedBall (characterZeroCenter t) (21 / 8 : ℝ))).toFinset

theorem characterContourDivisor_eq (χ : PrimitiveComplexCharacter) (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ)) :
    characterContourDivisor χ t z = (analyticOrderNatAt χ.L z : ℤ) := by
  rw [← characterZeroOrder_eq_nat]
  unfold characterContourDivisor characterZeroOrder
  rw [AnalyticOnNhd.divisor_apply (fun z _ => χ.L_analytic z) hz,
    AnalyticOnNhd.divisor_apply (fun z _ => χ.L_analytic z) (mem_univ z)]

theorem mem_characterContourZeros (χ : PrimitiveComplexCharacter) (t : ℝ) (z : ℂ) :
    z ∈ characterContourZeros χ t ↔
      z ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ) ∧ χ.L z = 0 := by
  change z ∈ ((characterContourDivisor χ t).finiteSupport (isCompact_closedBall _ _)).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  change characterContourDivisor χ t z ≠ 0 ↔ _
  constructor
  · intro hn
    have hz : z ∈ closedBall (characterZeroCenter t) (21 / 8 : ℝ) :=
      (characterContourDivisor χ t).supportWithinDomain hn
    refine ⟨hz, ?_⟩
    rw [characterContourDivisor_eq χ t z hz, ← characterZeroOrder_eq_nat] at hn
    exact (characterZeroOrder_pos_iff χ z).mp
      (lt_of_le_of_ne (characterZeroOrder_nonneg χ z) (Ne.symm hn))
  · rintro ⟨hz, he⟩
    rw [characterContourDivisor_eq χ t z hz, ← characterZeroOrder_eq_nat]
    exact ne_of_gt ((characterZeroOrder_pos_iff χ z).mpr he)

theorem characterContourZeros_mass_eq (χ : PrimitiveComplexCharacter) (t : ℝ) :
    (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) =
      ((∑ᶠ z, characterContourDivisor χ t z : ℤ) : ℝ) := by
  rw [finsum_eq_sum_of_support_subset (s := characterContourZeros χ t) _ (by
    intro z hz
    exact ((characterContourDivisor χ t).finiteSupport
      (isCompact_closedBall _ _)).mem_toFinset.mpr hz), Int.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [characterContourDivisor_eq χ t z ((mem_characterContourZeros χ t z).mp hz).1]
  simp

theorem characterContourZeros_mass_bound (χ : PrimitiveComplexCharacter) (t M : ℝ)
    (hM : 1 ≤ M)
    (hbound : ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M) :
    (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) ≤
      Real.log (3 * M) / Real.log (22 / 21 : ℝ) := by
  have ha : AnalyticOnNhd ℂ χ.L (closedBall (characterZeroCenter t) |(11 / 4 : ℝ)|) :=
    fun z _ => χ.L_analytic z
  have hlo := χ.L_lower_re_two (characterZeroCenter t) (characterZeroCenter_re t)
  have hne : χ.L (characterZeroCenter t) ≠ 0 := by
    intro he
    rw [he, norm_zero] at hlo
    linarith
  have hj := ha.sum_divisor_le (r := (21 / 8 : ℝ)) (R := (11 / 4 : ℝ))
    (by norm_num) (by norm_num) hM hne (fun z hz => hbound z (by
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 11 / 4)] using
        sphere_subset_closedBall hz))
  have hn : 0 < ‖χ.L (characterZeroCenter t)‖ := by linarith
  have hr : M / ‖χ.L (characterZeroCenter t)‖ ≤ 3 * M := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  rw [characterContourZeros_mass_eq]
  change ((∑ᶠ z, divisor χ.L (closedBall (characterZeroCenter t) (21 / 8)) z : ℤ) : ℝ) ≤ _
  rw [show |(21 / 8 : ℝ)| = 21 / 8 by norm_num,
    show (11 / 4 : ℝ) / (21 / 8) = 22 / 21 by norm_num] at hj
  apply hj.trans
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (div_pos (by linarith) hn) hr)
    (Real.log_pos (by norm_num)).le

end Ostmann

end OAI
