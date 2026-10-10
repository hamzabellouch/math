import OAI.Probability.InvariantIsing.Cavity.CavityCappedSpinTest

namespace OAI

/-! The usual weak topology, with the marked replica space specified
before synthesizing its measurable topology. -/

noncomputable section
open MeasureTheory

namespace InvariantIsing

instance cavityMarkedProbabilityTopology {m r q : ℕ} :
    TopologicalSpace (ProbabilityMeasure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))) :=
  @ProbabilityMeasure.instTopologicalSpace
    (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)))
    inferInstance inferInstance inferInstance

end InvariantIsing

end

end OAI
