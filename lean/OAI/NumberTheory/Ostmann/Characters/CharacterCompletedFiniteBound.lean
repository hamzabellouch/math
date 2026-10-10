import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedFiniteFactors
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedLogGrowth
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteZeroLogDerivative
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteZeroPolynomialLogDerivative

namespace OAI

/-! # A finite nontrivial zero set would bound the completed logarithmic derivative -/

namespace Ostmann

open Complex
open scoped BigOperators Classical

theorem completed_logDeriv_bounded_of_finite_zeros (χ : PrimitiveComplexCharacter)
    (hfinite : (complexCharacterZeros χ).Finite) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ s : ℂ, R ≤ s.re →
      ‖logDeriv χ.completed s‖ ≤ C := by
  obtain ⟨g, hg, hgne, he⟩ := character_completed_finite_factors χ hfinite
  obtain ⟨A, hA, hgrowth⟩ := character_completed_log_growth χ
  let S := hfinite.toFinset
  obtain ⟨c, hc⟩ := finite_zero_quotient_logDeriv_constant χ.completed g S hg hgne he A hA hgrowth
  obtain ⟨R, hR⟩ := exists_nat_gt (∑ z ∈ S, ‖z‖)
  let D : ℝ := ∑ z ∈ S, (analyticOrderNatAt χ.completed z : ℝ)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  refine ⟨(R : ℝ) + 1, ‖c‖ + D + 1, by positivity, by positivity, ?_⟩
  intro s hs
  have hdist (z : ℂ) (hz : z ∈ S) : 1 ≤ ‖s - z‖ := by
    have hzR : ‖z‖ ≤ (R : ℝ) :=
      (Finset.single_le_sum (fun w _ => norm_nonneg w) hz).trans hR.le
    have ha := abs_re_le_norm (s - z)
    have hb := (le_abs_self z.re).trans (abs_re_le_norm z)
    have hh := le_abs_self ((s - z).re)
    simp only [sub_re] at ha hh
    linarith
  have hsnot : s ∉ S := by
    intro hz
    have hh := hdist s hz
    simp only [sub_self, norm_zero] at hh
    linarith
  have hsum : ‖∑ z ∈ S, (analyticOrderNatAt χ.completed z : ℂ) / (s - z)‖ ≤ D := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro z hz
    rw [norm_div, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg _) (hdist z hz)
  have hfun : χ.completed = fun z => finiteZeroPolynomial χ.completed S z * g z := funext he
  have hsplit : logDeriv χ.completed s = logDeriv (finiteZeroPolynomial χ.completed S) s + logDeriv g s := by
    conv_lhs => rw [hfun]
    exact logDeriv_fun_mul s (finiteZeroPolynomial_ne_zero χ.completed S s hsnot) (hgne s)
      (finiteZeroPolynomial_analytic χ.completed S s).differentiableAt (hg s).differentiableAt
  rw [hsplit, hc s, finiteZeroPolynomial_logDeriv χ.completed S s hsnot]
  exact (norm_add_le _ _).trans (by linarith)

end Ostmann

end OAI
