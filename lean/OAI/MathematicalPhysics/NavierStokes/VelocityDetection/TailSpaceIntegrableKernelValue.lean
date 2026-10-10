import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceNormValueLe
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HeatKernelsNormalEqKernel

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
open scoped Topology
open SpatialCalculus HeatKernels

theorem integrable_kernel_value {n a : ℕ} {k : Coord n → ℝ} (hk : Integrable k)
    (J : compatibleJets n a) (X : Coord n) (s : ℝ) :
    Integrable (fun Y => k Y * value J (X + s • Y)) := by
  have hs : Continuous (fun Y : Coord n => s • Y) := continuous_id.const_smul s
  have hc : Continuous (fun Y : Coord n => value J (X + s • Y)) :=
    (contDiff_value J).continuous.comp (continuous_const.add hs)
  exact hk.mul_bdd hc.aestronglyMeasurable (Eventually.of_forall (fun Y => norm_value_le J _))

theorem moment_average_eq {a : ℕ} (J : compatibleJets 2 (a + 1)) (s : ℝ) (i : Fin 2) :
    average (momentKernel i) s (restrict (Nat.le_succ a) J) =
      s • average (normal 2) s (differentiate i J) := by
  apply value_injective
  ext X
  simp only [value_average (integrable_momentKernel i), restrict_value, value_smul,
    Pi.smul_apply, smul_eq_mul, value_average (integrable_normal 2)]
  have hu : Differentiable ℝ (fun Y => value J (X + s • Y)) := by
    apply ((contDiff_value J).differentiable (by simp)).comp
    exact (differentiable_const X).add (differentiable_id.const_smul s)
  have hn : Differentiable ℝ (normal 2) := contDiff_normal.differentiable (by simp)
  have hd (Y : Coord 2) : fderiv ℝ (normal 2) Y (Pi.single i 1) = -momentKernel i Y := by
    rw [← partialD_eq_fderiv i hn, partialD_normal]
  have hdu (Y : Coord 2) : fderiv ℝ (fun Z => value J (X + s • Z)) Y (Pi.single i 1) =
      s * value (differentiate i J) (X + s • Y) := by
    rw [← partialD_eq_fderiv i hu, partialD_scaled_value]
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := normal 2) (g := fun Y => value J (X + s • Y)) (v := Pi.single i 1)
    (by simp only [hd, neg_mul]; exact (integrable_kernel_value (integrable_momentKernel i) J X s).neg)
    (by
      simp only [hdu]
      simpa only [mul_left_comm] using
        (integrable_kernel_value (integrable_normal 2) (differentiate i J) X s).const_mul s)
    (integrable_kernel_value (integrable_normal 2) J X s)
    (fun Y _ => hn Y) (fun Y _ => hu Y)
  simp only [hd, hdu, neg_mul, integral_neg, neg_neg] at hh
  rw [show (fun Y => normal 2 Y * (s * value (differentiate i J) (X + s • Y))) =
    (fun Y => s * (normal 2 Y * value (differentiate i J) (X + s • Y))) by
      ext Y; ring, integral_const_mul] at hh
  exact hh.symm

end VelocityDetection.TailSpace.Jets
end

end OAI
