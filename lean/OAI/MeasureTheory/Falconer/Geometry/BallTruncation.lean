import OAI.MeasureTheory.Falconer.Recursion.PotentialPair
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

/-! # Enforcing ball bounds by deleting points of excessive local mass -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem measurable_ball_mass (μ : Measure X) [SFinite μ] (r : ℝ) :
    Measurable (fun x => μ (ball x r)) := by
  have hS : MeasurableSet {z : X × X | dist z.1 z.2 < r} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hm := measurable_measure_prodMk_left (ν := μ) hS
  convert hm using 1
  ext x
  congr 1
  ext y
  simp only [mem_preimage,mem_ofPred_eq,mem_ball,dist_comm]

theorem ball_mass_pair_integral (μ : Measure X) [SFinite μ] (r : ℝ) :
    (∫⁻ x, μ (ball x r) ∂μ) = (μ.prod μ) {z | dist z.1 z.2 < r} := by
  rw [Measure.prod_apply (measurableSet_lt (by fun_prop) measurable_const)]
  apply lintegral_congr
  intro x
  congr 1
  ext y
  simp only [mem_preimage,mem_ofPred_eq,mem_ball,dist_comm]

theorem excessive_ball_mass (μ : Measure X) [SFinite μ] (r : ℝ)
    {B : ℝ≥0∞} (hB : B ≠ 0) :
    μ {x | B < μ (ball x r)} ≤ B⁻¹*(μ.prod μ) {z | dist z.1 z.2 < r} := by
  by_cases hTop : B = ∞
  · simp [hTop]
  calc
    _ ≤ μ {x | B ≤ μ (ball x r)} := measure_mono (show {x | B < μ (ball x r)} ⊆
        {x | B ≤ μ (ball x r)} from by
      intro x hx
      change B < μ (ball x r) at hx
      exact hx.le)
    _ ≤ (∫⁻ x, μ (ball x r) ∂μ)/B :=
      meas_ge_le_lintegral_div (measurable_ball_mass μ r).aemeasurable hB hTop
    _ = _ := by rw [ball_mass_pair_integral,div_eq_mul_inv,mul_comm]

omit [SecondCountableTopology X] in
theorem restricted_good_ball_bound (μ : Measure X) [SFinite μ] (r : ℝ) (B : ℝ≥0∞) :
    ∀ a : X, (μ.restrict {x | μ (ball x (2*r)) ≤ B}) (ball a r) ≤ B := by
  intro a
  rw [Measure.restrict_apply measurableSet_ball]
  by_cases hne : (ball a r ∩ {x | μ (ball x (2*r)) ≤ B}).Nonempty
  · obtain ⟨x,hxa,hx⟩ := hne
    have hsub : ball a r ∩ {x | μ (ball x (2*r)) ≤ B} ⊆ ball x (2*r) := by
      rintro y ⟨hy,_⟩
      rw [mem_ball] at hxa hy ⊢
      have htri := dist_triangle y a x
      rw [dist_comm a x] at htri
      linarith
    exact (measure_mono hsub).trans hx
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,measure_empty]
    exact bot_le

end Falconer

end OAI
