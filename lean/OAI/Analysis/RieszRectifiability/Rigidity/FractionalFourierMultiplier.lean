import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalFourierFubini

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Filter
open scoped FourierTransform

theorem schwartz_inverse_fourier_second_difference {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) (x h : Ambient d) :
    symmetricSecondDifference (𝓕⁻ g : 𝓢(Ambient d, ℂ)) x h =
      ∫ ξ, (-2 * (1 - Real.cos (2 * Real.pi * inner ℝ ξ h)) : ℝ) •
        (fourierPhase ξ x * g ξ) := by
  have hp := fourierPhase_test_integrable g (x + h)
  have hm := fourierPhase_test_integrable g (x - h)
  have hx := fourierPhase_test_integrable g x
  have hi : (∫ ξ, fourierPhase ξ (x + h) * g ξ + fourierPhase ξ (x - h) * g ξ -
      (2 : ℂ) * (fourierPhase ξ x * g ξ)) =
      (∫ ξ, fourierPhase ξ (x + h) * g ξ) + (∫ ξ, fourierPhase ξ (x - h) * g ξ) -
        (2 : ℂ) * (∫ ξ, fourierPhase ξ x * g ξ) := by
    calc
      _ = (∫ ξ, fourierPhase ξ (x + h) * g ξ + fourierPhase ξ (x - h) * g ξ) -
          ∫ ξ, (2 : ℂ) * (fourierPhase ξ x * g ξ) :=
        integral_sub (hp.add hm) (hx.const_mul (2 : ℂ))
      _ = _ := by
        erw [integral_add hp hm, integral_const_mul]
  unfold symmetricSecondDifference
  rw [schwartz_inverse_fourier_phase_integral, schwartz_inverse_fourier_phase_integral,
    schwartz_inverse_fourier_phase_integral]
  change ((∫ ξ, fourierPhase ξ (x + h) * g ξ) + (∫ ξ, fourierPhase ξ (x - h) * g ξ) -
    (2 : ℝ) • (∫ ξ, fourierPhase ξ x * g ξ)) = _
  erw [Complex.real_smul]
  norm_num only [Complex.ofReal_ofNat]
  erw [← hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ξ
  calc
    _ = symmetricSecondDifference (fourierPhase ξ) x h * g ξ := by
      unfold symmetricSecondDifference
      erw [two_smul ℝ]
      ring
    _ = _ := by
      rw [fourierPhase_second_difference]
      simp only [Complex.real_smul]
      ring

theorem schwartz_inverse_fourier_fractional_kernel (p : ℕ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x h : Ambient (p + 1)) :
    fractionalSchwartzKernel (p + 1) (𝓕⁻ g : 𝓢(Ambient (p + 1), ℂ)) x h =
      (-2 : ℝ) • (∫ ξ, fractionalFourierKernel p g x (ξ, h)) := by
  unfold fractionalSchwartzKernel
  rw [schwartz_inverse_fourier_second_difference]
  erw [Complex.real_smul]
  simp +instances only [Complex.real_smul]
  erw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ξ
  unfold fractionalFourierKernel fractionalSymbolKernel
  simp only [Complex.real_smul]
  push_cast
  ring

theorem fractionalSchwartz_inverse_fourier_multiplier (p : ℕ)
    (g : 𝓢(Ambient (p + 1), ℂ)) (x : Ambient (p + 1)) :
    fractionalSchwartzTest p (𝓕⁻ g) x =
      ∫ ξ, fractionalSymbol p ξ • (fourierPhase ξ x * g ξ) := by
  unfold fractionalSchwartzTest
  simp_rw [schwartz_inverse_fourier_fractional_kernel]
  simp +instances only [Complex.real_smul]
  erw [integral_const_mul, ← mul_assoc]
  norm_num
  exact fractionalFourierKernel_integral_swap p g x

theorem fractionalSchwartz_positive_norm_multiplier (p : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : 𝓢(Ambient (p + 1), ℂ), ∀ x : Ambient (p + 1),
      fractionalSchwartzTest p (𝓕⁻ g) x =
        ∫ ξ, (c * ‖ξ‖ : ℝ) • (fourierPhase ξ x * g ξ) := by
  obtain ⟨c, hc, hs⟩ := fractionalSymbol_eq_positive_constant_mul_norm p
  refine ⟨c, hc, fun g x => ?_⟩
  rw [fractionalSchwartz_inverse_fourier_multiplier]
  exact integral_congr_ae (Eventually.of_forall fun ξ => by
    dsimp only
    rw [hs ξ])

end

end RieszRectifiability

end OAI
