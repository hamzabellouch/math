import OAI.Analysis.Pureness.Operators.PositiveCutOrder
import OAI.Analysis.Pureness.Projections.FiniteSpectralIntegralBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace MeasureTheory Set
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteDimensionDistribution_mono
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (t : ℝ) : Monotone (fun M : Positive (FinMatrix A n) => finiteDimensionDistribution d n M t) := by
  intro M N hMN
  apply hd
  apply (finitePositiveClass_le_iff n _ _).mpr
  exact (cuntzSubequiv_iff_shared _ _).mpr
    (positive_cut_cuntzBelow_of_le M N hMN t.toNNReal)

theorem finiteSpectralIntegral_monotone
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d) (n : ℕ) :
    Monotone (finiteSpectralIntegral d n) := by
  intro M N hMN
  exact lintegral_mono (fun t => finiteDimensionDistribution_mono d hd n t hMN)
end CuntzPureness

end

end OAI
