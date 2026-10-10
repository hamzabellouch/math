import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [MeasurableSpace Y]

theorem weighted_error_integral_le (p : FiniteProbabilityWeights X) (μ : Measure Y)
    (F W : Y → X → ℂ) (hF : ∀ x, Integrable (fun y => F y x) μ)
    (hW : ∀ x, Measurable (fun y => W y x)) (hW1 : ∀ y x, ‖W y x‖ ≤ 1)
    (e : X → ℝ) (he : ∀ x, (∫ y, ‖F y x‖ ∂μ) ≤ e x) :
    Integrable (fun y => p.complexMean (fun x => W y x * F y x)) μ ∧
    (∫ y, ‖p.complexMean (fun x => W y x * F y x)‖ ∂μ) ≤ p.mean e := by
  have hwF (x : X) : Integrable (fun y => W y x * F y x) μ :=
    (hF x).bdd_mul (hW x).aestronglyMeasurable (Filter.Eventually.of_forall (fun y => hW1 y x))
  have havg := p.complexMean_integrable μ (fun y x => W y x * F y x) hwF
  have hnorm : Integrable (fun y => p.mean (fun x => ‖F y x‖)) μ :=
    integrable_finsetSum _ (fun x _ => (hF x).norm.const_mul (p.weight x))
  have hpoint (y : Y) : ‖p.complexMean (fun x => W y x * F y x)‖ ≤ p.mean (fun x => ‖F y x‖) := by
    apply (p.norm_complexMean_le_mean_norm _).trans
    apply p.mean_mono
    intro x
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hW1 y x) (norm_nonneg _)).trans_eq (one_mul _)
  refine ⟨havg, ?_⟩
  calc
    (∫ y, ‖p.complexMean (fun x => W y x * F y x)‖ ∂μ) ≤
        ∫ y, p.mean (fun x => ‖F y x‖) ∂μ := integral_mono havg.norm hnorm hpoint
    _ = p.mean (fun x => ∫ y, ‖F y x‖ ∂μ) := by
      unfold mean
      rw [integral_finsetSum _ (fun x _ => (hF x).norm.const_mul (p.weight x))]
      simp only [integral_const_mul]
    _ ≤ p.mean e := p.mean_mono he

end Erdos3.FiniteProbabilityWeights

end

end OAI
