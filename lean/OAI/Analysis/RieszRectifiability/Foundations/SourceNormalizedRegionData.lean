import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SourceNormalizedEnergy

namespace OAI

/-!
# Normalized height data on bounded projection regions

Uniform square-integral and fractional-energy bounds on balls restrict to the
bounded projection regions inside them. Choosing bounds at each region's outer
radius produces constants indexed by the region size, independent of the
sequence index. Positivity of the integrands and monotonicity of restricted
product measures preserve both estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter
open scoped NNReal

theorem normalized_region_data_of_ball_data {ι : Type*} [Fintype ι] {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, SFinite (μ j)]
    (w : ℕ → Ambient d → ℝ) (a : Ambient d)
    (hball : ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
      MemLp (w j) 2 ((μ j).restrict (ball a r)) ∧
      (∫ x in ball a r, w j x ^ 2 ∂μ j) ≤ B ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy n (w j) q.1 q.2)
        (((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy n (w j) q.1 q.2
        ∂((μ j).restrict (ball a r)).prod ((μ j).restrict (ball a r))) ≤ E)
    (π : Ambient d → ι → ℝ) (K : ℝ≥0) :
    ∃ B E : ℕ → ℝ, ∀ H, 0 ≤ B H ∧ 0 ≤ E H ∧ ∀ j,
      MemLp (w j) 2 ((μ j).restrict (boundedProjectionRegion π a K H)) ∧
      (∫ x in boundedProjectionRegion π a K H, w j x ^ 2 ∂μ j) ≤ B H ∧
      Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy n (w j) q.1 q.2)
        (((μ j).restrict (boundedProjectionRegion π a K H)).prod
          ((μ j).restrict (boundedProjectionRegion π a K H))) ∧
      (∫ q : Ambient d × Ambient d, fractionalPairEnergy n (w j) q.1 q.2
        ∂((μ j).restrict (boundedProjectionRegion π a K H)).prod
          ((μ j).restrict (boundedProjectionRegion π a K H))) ≤ E H := by
  choose B E hB hE hd using
    (fun H => hball (planeBoxOuterRadius K H) (planeBoxOuterRadius_pos K H))
  refine ⟨B, E, fun H => ⟨hB H, hE H, fun j => ?_⟩⟩
  have hs : boundedProjectionRegion π a K H ⊆ ball a (planeBoxOuterRadius K H) := inter_subset_right
  have hμ := Measure.restrict_mono (μ := μ j) hs le_rfl
  have hprod : ((μ j).restrict (boundedProjectionRegion π a K H)).prod
      ((μ j).restrict (boundedProjectionRegion π a K H)) ≤
      ((μ j).restrict (ball a (planeBoxOuterRadius K H))).prod
        ((μ j).restrict (ball a (planeBoxOuterRadius K H))) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    exact Measure.restrict_mono (prod_mono hs hs) le_rfl
  exact ⟨MemLp.mono_measure hμ (hd H j).1,
    (integral_mono_measure hμ (Eventually.of_forall fun x => sq_nonneg (w j x))
      (hd H j).1.integrable_sq).trans (hd H j).2.1,
    (hd H j).2.2.1.mono_measure hprod,
    (integral_mono_measure hprod
      (Eventually.of_forall fun q => fractionalPairEnergy_nonneg n (w j) q.1 q.2)
      (hd H j).2.2.1).trans (hd H j).2.2.2⟩

end

end RieszRectifiability

end OAI
