import OAI.MeasureTheory.Falconer.Shells.FiniteWeightedShell

namespace OAI

namespace PlanarFalconer
open MeasureTheory

theorem finite_sum_square_integrable {ι : Type*} (s : Finset ι)
    (μ : Measure ℝ) (F : ι → ℝ → ℂ)
    (hm : ∀ i ∈ s, Measurable (F i))
    (hi : ∀ i ∈ s, Integrable (fun r => ‖F i r‖^2) μ) :
    Integrable (fun r => ‖∑ i ∈ s, F i r‖^2) μ := by
  have hsm : Measurable (fun r => ∑ i ∈ s, F i r) := by
    exact Finset.measurable_sum s hm
  have hb := (integrable_finsetSum s hi).const_mul (∑ _i ∈ s, (1:ℝ))
  apply hb.mono' (hsm.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with r
  change ‖‖∑ i ∈ s, F i r‖^2‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s _) 2).trans
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun _ => (1:ℝ)) (g := fun i => ‖F i r‖^2) (r := fun i => ‖F i r‖)
    (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)

end PlanarFalconer

end OAI
