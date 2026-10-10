import OAI.Probability.FreeIsing.Ising.CopyGeodesicCorrelations
import OAI.Probability.FreeIsing.Trees.ColoredPathEndpoints

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open ColoredPathAverage IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem pathValue_cavityLogEdgeVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {n : ℕ} {i : Fin d} (p : Path d n i) :
    pathValue (differenceReflection hμ) (cavityLogEdgeVector hμ hbeta t) p =
      cavityLogVector hμ hbeta t (tailVertex p) (headVertex p) := by
  apply pathValue_eq_edgeVector
  · intro i
    rfl
  · intro c v w
    exact differenceReflection_cavityLogVector hμ hbeta c t v w

theorem inner_pathValue_cavityLogEdgeVector
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {n : ℕ} {i : Fin d} (p : Path d n i) :
    inner ℝ (cavityLogEdgeVector hμ hbeta t i)
      (pathValue (differenceReflection hμ) (cavityLogEdgeVector hμ hbeta t) p) =
      ∫ q, cavityLogDifference hbeta t TreeEscape.root (prefixFlip i TreeEscape.root) q *
        cavityLogDifference hbeta t (tailVertex p) (headVertex p) q ∂copies beta μ := by
  rw [pathValue_cavityLogEdgeVector]
  exact inner_cavityLogVector_eq_integral hμ hbeta t _ _ _ _

end Problem367.IsingCopySpectral

end

end OAI
