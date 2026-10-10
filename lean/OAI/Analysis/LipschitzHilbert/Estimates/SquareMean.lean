import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! Passing a local square bound to a local mean bound. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert

theorem integral_le_of_square_mean_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    {K : ℝ} (hK : 0 < K) (h2 : (∫ x, f x ^ 2 ∂μ) ≤ K ^ 2 * μ.real univ) :
    (∫ x, f x ∂μ) ≤ K * μ.real univ := by
  have hpoint (x : X) : (2 * K) * f x ≤ f x ^ 2 + K ^ 2 := by
    nlinarith [sq_nonneg (f x - K)]
  have h := integral_mono (hf.const_mul (2 * K)) (hf2.add (integrable_const (K ^ 2))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add hf2 (integrable_const (K ^ 2)), integral_const,
    smul_eq_mul] at h
  nlinarith

end LipschitzHilbert

end

end OAI
