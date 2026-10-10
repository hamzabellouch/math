import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySobolevPoint

namespace OAI

/-! # Sampling a variable real part without moving left of the density line -/

namespace Ostmann

open MeasureTheory Set

 theorem density_forward_interval_sample (f g : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) (t : ℝ) :
    ‖f t‖ ^ 2 ≤ 2 * (∫ x in t..t + 1, ‖f x‖ ^ 2) +
      ∫ x in t..t + 1, ‖g x‖ ^ 2 := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hab : t ≤ t + 1 := by linarith
  have hpoint (u : ℝ) (hu : u ∈ Icc t (t + 1)) :=
    density_energy_oscillation f g hf hg t (t + 1) t u ⟨le_rfl, hab⟩ hu
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab intervalIntegrable_const
    (((hcont.norm.pow 2).intervalIntegrable t (t + 1)).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add,
    intervalIntegral.integral_const, intervalIntegral.integral_add] at hi
  · simp only [show t + 1 - t = (1 : ℝ) by ring, smul_eq_mul, one_mul] at hi
    change ‖f t‖ ^ 2 ≤ (∫ x in t..t + 1, ‖f x‖ ^ 2) +
      ((∫ x in t..t + 1, ‖f x‖ ^ 2) + ∫ x in t..t + 1, ‖g x‖ ^ 2) at hi
    linarith
  · exact (hcont.norm.pow 2).intervalIntegrable _ _
  · exact (hg.norm.pow 2).intervalIntegrable _ _
  · exact (hcont.norm.pow 2).intervalIntegrable _ _
  · exact intervalIntegrable_const

 theorem density_abscissa_sample (f g : ℝ → ℂ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g)
    (σ β : ℝ) (hσβ : σ ≤ β) (hβ : β ≤ 1) :
    ‖f β‖ ^ 2 ≤ 2 * (∫ x in σ..2, ‖f x‖ ^ 2) + ∫ x in σ..2, ‖g x‖ ^ 2 := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have h := density_forward_interval_sample f g hf hg β
  have hF := intervalIntegral.integral_mono_interval (μ := volume) hσβ (by linarith : β ≤ β + 1)
    (by linarith : β + 1 ≤ 2)
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖))
    ((hcont.norm.pow 2).intervalIntegrable σ 2)
  have hG := intervalIntegral.integral_mono_interval (μ := volume) hσβ (by linarith : β ≤ β + 1)
    (by linarith : β + 1 ≤ 2)
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖g x‖))
    ((hg.norm.pow 2).intervalIntegrable σ 2)
  linarith

end Ostmann

end OAI
