import Mathlib
import OAI.Probability.Perceptron.Interpolation.TiltReplicaCoordinate

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma stablePoissonTotal_log_memLp_two {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    MemLp (fun η => Real.log (stablePoissonTotal η)) 2
      (poissonRandomMeasureLaw (stableLogIntensity b)) := by
  apply (memLp_two_iff_integrable_sq stablePoissonTotal_measurable.log.aestronglyMeasurable).mpr
  simpa only [Real.rpow_zero,one_mul] using
    stablePoissonTotal_weighted_log_sq_integrable (a := 0) hb0 hb1 hb0

end SphericalPerceptronFreeEnergy

end

end OAI
