import OAI.NumberTheory.CubicMoment.Estimates.GaussianTrace
import OAI.NumberTheory.CubicMoment.Estimates.TraceDuality

namespace OAI

/-! The Gaussian test-function identity used to evaluate the Riesz integral. -/

noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma integrable_trace_gaussian {t : ℝ} (ht : 0 < t) :
    Integrable (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (t:ℂ)) (by simpa using ht) 0 0
  simpa using h

lemma integral_traceFourier_gaussian (f : ℂ → ℂ) (hf : Integrable f)
    {t : ℝ} (ht : 0 < t) :
    (∫ y : ℂ, traceFourier f y*Complex.exp (-(t:ℂ)*‖y‖^2)) =
      (Real.pi/t:ℝ)*(∫ x : ℂ, f x*Complex.exp ((-4*Real.pi^2/t*Complex.normSq x:ℝ):ℂ)) := by
  rw [integral_traceFourier_mul f _ hf (integrable_trace_gaussian ht)]
  simp_rw [traceFourier_gaussian ht]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

end CubicFirstMoment

end

end OAI
