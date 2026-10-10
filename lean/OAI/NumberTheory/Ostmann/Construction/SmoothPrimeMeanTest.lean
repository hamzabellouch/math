import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import OAI.NumberTheory.Ostmann.Construction.SmoothLogCellProfile

namespace OAI

/-! # A fixed smooth test for the prime mean of the sparse weight -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

noncomputable def primeMeanTest (t : ℝ) : ℝ := logCellProfile (8 * (t - 3 / 4))

theorem primeMeanTest_nonneg (t : ℝ) : 0 ≤ primeMeanTest t := logCellProfile_nonneg _

theorem primeMeanTest_le_one (t : ℝ) : primeMeanTest t ≤ 1 := logCellProfile_le_one _

theorem primeMeanTest_contDiff {n : ℕ∞} : ContDiff ℝ n primeMeanTest :=
  logCellProfile_contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem primeMeanTest_zero_outside (t : ℝ) (ht : t ∉ Set.Icc (5 / 8 : ℝ) (7 / 8)) :
    primeMeanTest t = 0 := by
  apply logCellProfile_zero_outside
  by_contra h
  have hh := abs_lt.mp (lt_of_not_ge h)
  exact ht ⟨by linarith, by linarith⟩

theorem primeMeanTest_compactSupport : HasCompactSupport primeMeanTest :=
  HasCompactSupport.intro isCompact_Icc primeMeanTest_zero_outside

theorem primeMeanTest_center : primeMeanTest (3 / 4) = 1 := by
  norm_num [primeMeanTest, logCellProfile, Real.smoothTransition.zero,
    Real.smoothTransition.one]

theorem primeMeanTest_integral_pos : 0 < ∫ t : ℝ, primeMeanTest t := by
  apply (primeMeanTest_contDiff (n := 0)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := (3 / 4 : ℝ)) primeMeanTest_compactSupport primeMeanTest_nonneg
  rw [primeMeanTest_center]
  norm_num

noncomputable def primeMeanMellin (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), (primeMeanTest t : ℂ) *
    Complex.exp ((s - 1) * (Real.log t : ℂ))

noncomputable def smoothMangoldtMean (q : ℕ) (χ : DirichletCharacter ℂ q) (X : ℝ) : ℂ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * primeMeanTest (n / X)

end Ostmann

end OAI
