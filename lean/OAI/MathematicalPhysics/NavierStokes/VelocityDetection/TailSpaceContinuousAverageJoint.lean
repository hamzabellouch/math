import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceConvolveRescale
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceHeatDerivative

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

theorem continuous_average_joint {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k) :
    Continuous (fun p : ℝ × compatibleJets n a => average k p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _
    ⟨∫ Y, ‖k Y‖, integral_nonneg (fun _ => norm_nonneg _)⟩
  · intro s
    have hh := AddMonoidHomClass.lipschitz_of_bound (averageL (a := a) hk s)
      (∫ Y, ‖k Y‖) (norm_average_le (a := a) hk s)
    rw [Real.toNNReal_of_nonneg (integral_nonneg (fun Y => norm_nonneg (k Y)))] at hh
    exact hh
  · exact continuous_average hk

theorem heatDerivative_eq_average {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (i : Fin 2) (J : compatibleJets 2 a) :
    heatDerivative hν ht i J = -(Real.sqrt (2 * ν * t))⁻¹ •
      average (momentKernel i) (-Real.sqrt (2 * ν * t)) J := by
  have hr : 0 < Real.sqrt (2 * ν * t) := Real.sqrt_pos.mpr (by positivity)
  have hc := convolve_rescale (integrable_momentKernel i) hr J
  change average (SpatialCalculus.partialD i (kernel ν t)) (-1) J = _
  rw [partialD_kernel_rescale hν ht]
  simp only [average, mul_smul]
  rw [integral_smul]
  exact congrArg (fun V => -(Real.sqrt (2 * ν * t))⁻¹ • V) hc

end VelocityDetection.TailSpace.Jets
end

end OAI
