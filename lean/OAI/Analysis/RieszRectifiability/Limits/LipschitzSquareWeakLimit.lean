import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.WeakRestriction
import OAI.Analysis.RieszRectifiability.Kernel.BoundedRegionTests

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal BoundedContinuousFunction

theorem lipschitz_memLp_of_ae_ball {d : ℕ}
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (a : Ambient d) (R : ℝ) (hμ : ∀ᵐ x ∂μ, x ∈ ball a R)
    (v : Ambient d → ℝ) (L : ℝ≥0) (hv : LipschitzWith L v) :
    MemLp v 2 μ := by
  obtain ⟨g, K, B, _, hg, hB, heq⟩ := exists_compact_lipschitz_test_on_ball a R v L hv
  have hgm : MemLp g 2 μ := MemLp.of_bound hg.continuous.aestronglyMeasurable (B : ℝ)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hB x)
  apply hgm.ae_eq
  filter_upwards [hμ] with x hx
  exact heq x hx

theorem lipschitz_square_integral_tendsto_of_ae_ball {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (a : Ambient d) (R : ℝ)
    (hμ : ∀ j, ∀ᵐ x ∂(μ j : Measure (Ambient d)), x ∈ ball a R)
    (hν : ∀ᵐ x ∂(ν : Measure (Ambient d)), x ∈ ball a R)
    (v : Ambient d → ℝ) (L : ℝ≥0) (hv : LipschitzWith L v) :
    Tendsto (fun j => ∫ x, v x ^ 2 ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, v x ^ 2 ∂(ν : Measure (Ambient d)))) := by
  obtain ⟨g, K, B, _, hg, hB, heq⟩ := exists_compact_lipschitz_test_on_ball a R v L hv
  let G : Ambient d →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    g hg.continuous (B : ℝ) (fun x => by simpa only [Real.norm_eq_abs] using! hB x)
  have hm : ∀ j, (∫ x, (G * G) x ∂(μ j : Measure (Ambient d))) =
      ∫ x, v x ^ 2 ∂(μ j : Measure (Ambient d)) := by
    intro j
    apply integral_congr_ae
    filter_upwards [hμ j] with x hx
    change g x * g x = v x ^ 2
    rw [heq x hx, pow_two]
  have hn : (∫ x, (G * G) x ∂(ν : Measure (Ambient d))) =
      ∫ x, v x ^ 2 ∂(ν : Measure (Ambient d)) := by
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    change g x * g x = v x ^ 2
    rw [heq x hx, pow_two]
  simpa only [hm, hn] using!
    FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (G * G)

end

end RieszRectifiability

end OAI
