import OAI.Analysis.IrrationalRotation.Model.ScalarSampling
import Mathlib.Topology.EMetricSpace.BoundedVariation

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

structure KernelEstimates (m : ℕ) (u : ℝ → ℝ → ℝ) : Prop where
  boundedVariation : ∀ s, BoundedVariationOn (u s) (Icc (0 : ℝ) 1)
  variation_sharp : ∀ s,
    sSup (Set.range (fun v : ℝ => |u s v|)) +
      (eVariationOn (u s) (Icc (0 : ℝ) 1)).toReal ≤ 11 * (m : ℝ)^(13 / 5 : ℝ)
  variation_coarse : ∀ s,
    sSup (Set.range (fun v : ℝ => |u s v|)) +
      (eVariationOn (u s) (Icc (0 : ℝ) 1)).toReal ≤ 11 * (m : ℝ)^10
  average_bounds : ∀ s, 0 ≤ (∫ v in (0 : ℝ)..1, u s v) ∧
    (∫ v in (0 : ℝ)..1, u s v) ≤ 2
  mass : (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, u s v) = 1 - 2 / (m : ℝ)^2
  average_square_lower : (1 - 2 / (m : ℝ)^2)^2 ≤
    ∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2
  average_square_upper : (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, u s v)^2) ≤
    1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2
  square_mass : (∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, u s v^2) =
    (2 / (m : ℝ)^(-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2)

end Invariant233.ScalarSampling

end OAI
