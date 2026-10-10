import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HeatKernelsNormalTwoNeg

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
open scoped Topology
open SpatialCalculus

theorem normal_eq_kernel : normal 2 = kernel (1 / 2) 1 := by
  ext X
  rw [normal_two]
  simp only [kernel]
  congr 1 <;> congr 1 <;> ring

theorem contDiff_normal : ContDiff ℝ ∞ (normal 2) := by
  rw [normal_eq_kernel]
  exact contDiff_kernel _ _

theorem partialD_normal (i : Fin 2) (X : Coord 2) :
    partialD i (normal 2) X = -momentKernel i X := by
  rw [normal_eq_kernel, partialD_kernel]
  simp only [momentKernel, normal_eq_kernel]
  ring_nf

end VelocityDetection.HeatKernels
end

end OAI
