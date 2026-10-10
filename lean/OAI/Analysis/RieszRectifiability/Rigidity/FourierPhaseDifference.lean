import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FractionalSchwartzKernel
import OAI.Analysis.RieszRectifiability.Rigidity.FourierMeanZeroTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform

def fourierPhase {d : ℕ} (ξ x : Ambient d) : ℂ :=
  Complex.exp ((2 * Real.pi * inner ℝ ξ x : ℝ) * Complex.I)

theorem fourierPhase_norm {d : ℕ} (ξ x : Ambient d) : ‖fourierPhase ξ x‖ = 1 := by
  simp [fourierPhase, Complex.norm_exp]

theorem fourierPhase_add {d : ℕ} (ξ x h : Ambient d) :
    fourierPhase ξ (x + h) = fourierPhase ξ x * fourierPhase ξ h := by
  unfold fourierPhase
  rw [inner_add_right, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem fourierPhase_sub {d : ℕ} (ξ x h : Ambient d) :
    fourierPhase ξ (x - h) = fourierPhase ξ x * fourierPhase ξ (-h) := by
  rw [sub_eq_add_neg, fourierPhase_add]

theorem fourierPhase_add_neg {d : ℕ} (ξ h : Ambient d) :
    fourierPhase ξ h + fourierPhase ξ (-h) =
      2 * (Real.cos (2 * Real.pi * inner ℝ ξ h) : ℂ) := by
  simp only [fourierPhase, inner_neg_right, mul_neg, Complex.ofReal_neg]
  rw [← Complex.two_cos, ← Complex.ofReal_cos]

theorem fourierPhase_second_difference {d : ℕ} (ξ x h : Ambient d) :
    symmetricSecondDifference (fourierPhase ξ) x h =
      (-2 * (1 - Real.cos (2 * Real.pi * inner ℝ ξ h)) : ℝ) • fourierPhase ξ x := by
  unfold symmetricSecondDifference
  rw [fourierPhase_add, fourierPhase_sub]
  have hs := fourierPhase_add_neg ξ h
  simp only [two_smul ℝ, Complex.real_smul]
  push_cast at hs ⊢
  linear_combination (fourierPhase ξ x) * hs

theorem schwartz_inverse_fourier_phase_integral {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) :
    (𝓕⁻ g) x = ∫ ξ, fourierPhase ξ x * g ξ := by
  calc
    (𝓕⁻ g) x = 𝓕⁻ (g : Ambient d → ℂ) x := congrFun (fourierInv_coe g) x
    _ = ∫ ξ, fourierPhase ξ x * g ξ := by
      rw [Real.fourierInv_eq']
      rfl

theorem fourierPhase_test_integrable {d : ℕ} (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) :
    Integrable (fun ξ => fourierPhase ξ x * g ξ) volume := by
  apply g.integrable.bdd_mul
  · apply Measurable.aestronglyMeasurable
    unfold fourierPhase
    fun_prop
  · exact Filter.Eventually.of_forall fun ξ => (fourierPhase_norm ξ x).le

end

end RieszRectifiability

end OAI
