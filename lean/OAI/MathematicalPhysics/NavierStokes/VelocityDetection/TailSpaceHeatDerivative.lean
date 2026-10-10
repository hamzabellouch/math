import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailConvolution
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HeatKernelsContDiffKernel

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open HeatKernels SpatialCalculus

def heatDerivative {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (i : Fin 2) :
    compatibleJets 2 a →L[ℝ] compatibleJets 2 a :=
  convolve (integrable_partialD_kernel hν ht i)

theorem norm_heatDerivative_le {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (i : Fin 2) (J : compatibleJets 2 a) :
    ‖heatDerivative hν ht i J‖ ≤
      (absoluteMoment i / Real.sqrt (2 * ν)) * (Real.sqrt t)⁻¹ * ‖J‖ := by
  simpa only [heatDerivative, integral_norm_partialD_kernel_eq hν ht i] using
    norm_convolve_le (integrable_partialD_kernel hν ht i) J

end VelocityDetection.TailSpace.Jets
end

end OAI
