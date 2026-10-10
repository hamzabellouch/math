import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothLeftContourBound

namespace OAI

/-! # Integrability of the starting vertical line in the contour shift -/

namespace Ostmann

open Complex MeasureTheory Filter
open scoped Topology BigOperators

noncomputable def rightContourIntegrand (χ : PrimitiveComplexCharacter) (X t : ℝ) : ℂ :=
  (-deriv χ.L (primeMellinLine t) / χ.L (primeMellinLine t)) * primeVerticalWeight X t

theorem character_logDeriv_re_two_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), s.re = 2 → ‖logDeriv χ.L s‖ ≤ C := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let C : ℝ := ∑' n, ‖LSeries.term f (2 : ℂ) n‖
  have hsum : LSeriesSummable f (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hC : 0 ≤ C := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C + 1, by positivity, ?_⟩
  intro χ s hs
  have hcs : LSeriesSummable (characterMangoldtCoefficient χ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character (by rw [hs]; norm_num)
  have hterm (n : ℕ) : ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ ≤
      ‖LSeries.term f (2 : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs]
    rw [show (2 : ℂ).re = (2 : ℝ) by norm_num]
    split_ifs with hn
    · exact le_rfl
    · apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      dsimp only [characterMangoldtCoefficient, f]
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.character.norm_le_one _)
  calc
    ‖logDeriv χ.L s‖ = ‖LSeries (characterMangoldtCoefficient χ) s‖ := by
      rw [χ.mangoldt_LSeries_eq s (by rw [hs]; norm_num), logDeriv_apply, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ :=
      norm_tsum_le_tsum_norm hcs.norm
    _ ≤ C := hcs.norm.tsum_le_tsum hterm hsum.norm
    _ ≤ C + 1 := by linarith

theorem rightContourIntegrand_integrable (χ : PrimitiveComplexCharacter) (X : ℝ)
    (hX : 0 < X) : Integrable (rightContourIntegrand χ X) := by
  obtain ⟨C, hC, hbound⟩ := character_logDeriv_re_two_bound
  have hcn : Continuous (rightContourIntegrand χ X) := by
    have hL : Continuous χ.L := continuous_iff_continuousAt.mpr
      (fun z => (χ.L_analytic z).continuousAt)
    have hL' : Continuous (deriv χ.L) := continuous_iff_continuousAt.mpr
      (fun z => (χ.L_analytic z).deriv.continuousAt)
    have hn (t : ℝ) : χ.L (primeMellinLine t) ≠ 0 :=
      χ.L_ne_zero_one_le_re _ (by simp)
    exact ((hL'.comp primeMellinLine_continuous).neg.div
      (hL.comp primeMellinLine_continuous) hn).mul (primeVerticalWeight_continuous X hX)
  apply ((primeVerticalWeight_integrable X hX).norm.const_mul C).mono' hcn.aestronglyMeasurable
  filter_upwards with t
  rw [rightContourIntegrand, norm_mul]
  have hn : ‖-deriv χ.L (primeMellinLine t) / χ.L (primeMellinLine t)‖ =
      ‖logDeriv χ.L (primeMellinLine t)‖ := by simp [logDeriv_apply, neg_div]
  rw [hn]
  exact mul_le_mul_of_nonneg_right (hbound χ _ (by simp)) (norm_nonneg _)

end Ostmann

end OAI
