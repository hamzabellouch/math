import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HeatKernelsContDiffKernel

namespace OAI

noncomputable section
namespace VelocityDetection.HeatKernels
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators

@[simp] theorem normal_two_neg (Y : Coord 2) : normal 2 (-Y) = normal 2 Y := by
  simp [normal_two]

theorem momentKernel_neg (i : Fin 2) (Y : Coord 2) : momentKernel i (-Y) = -momentKernel i Y := by
  simp [momentKernel]

theorem integral_momentKernel (i : Fin 2) : ∫ Y, momentKernel i Y = 0 := by
  have hh := integral_neg_eq_self (momentKernel i) volume
  simp only [momentKernel_neg, integral_neg] at hh
  linarith

theorem integral_partialD_kernel {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (i : Fin 2) :
    (∫ Y, SpatialCalculus.partialD i (kernel ν t) Y) = 0 := by
  rw [partialD_kernel_rescale hν ht, integral_const_mul,
    integral_rescale _ (Real.sqrt_pos.mpr (by positivity)), integral_momentKernel, mul_zero]

end VelocityDetection.HeatKernels
end

end OAI
