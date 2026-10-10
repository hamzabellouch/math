import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HeatKernelsNormalEqKernel
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicJetsCalculus

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators
open SpatialCalculus HeatKernels

theorem hasDerivAt_translate {n a : ℕ} (J : compatibleJets n (a + 1)) (v : Coord n) (s : ℝ) :
    HasDerivAt (fun r : ℝ => translate (r • v) (restrict (Nat.le_succ a) J))
      (translate (s • v) (directional v J)) s := by
  apply hasDerivAt_of_values
    ((continuous_translate (directional v J)).comp (continuous_id.smul continuous_const))
  intro t X
  change HasDerivAt (fun r => value J (X + r • v))
    (value (directional v J) (X + t • v)) t
  rw [value_directional]
  have hh := (hasFDerivAt_value J (X + t • v)).comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const v).const_add X)
  simpa only [one_smul, comp_def, id_eq] using hh

theorem partialD_scaled_value {a : ℕ} (J : compatibleJets 2 (a + 1))
    (X : Coord 2) (s : ℝ) (i : Fin 2) (Y : Coord 2) :
    partialD i (fun Z => value J (X + s • Z)) Y =
      s * value (differentiate i J) (X + s • Y) := by
  have hh (Z : Coord 2) := (hasFDerivAt_value J (X + s • Z)).comp Z
    (((hasFDerivAt_id Z).const_smul s).const_add X)
  simp only [Pi.smul_apply, comp_def, id_eq] at hh
  rw [partialD_eq_fderiv i (fun Z => (hh Z).differentiableAt), (hh Y).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, firstGradient, sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp [Pi.single_apply]

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

end VelocityDetection.PeriodicSpace.Jets
end

noncomputable section
namespace VelocityDetection.PeriodicSpace.Jets
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators
open HeatKernels SpatialCalculus

def heatGradient {a : ℕ} (ν t : ℝ) (i : Fin 2) :
    compatibleJets 2 a →L[ℝ] compatibleJets 2 a :=
  -(Real.sqrt (2 * ν * t))⁻¹ •
    averageL (a := a) (integrable_momentKernel i) (-Real.sqrt (2 * ν * t))

theorem heatGradient_eq {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (i : Fin 2) (J : compatibleJets 2 a) :
    heatGradient ν t i J = heatDerivative hν ht i J :=
  (heatDerivative_eq_average hν ht i J).symm

theorem norm_heatGradient_le {a : ℕ} {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (i : Fin 2) (J : compatibleJets 2 a) :
    ‖heatGradient ν t i J‖ ≤
      (absoluteMoment i / Real.sqrt (2 * ν)) * (Real.sqrt t)⁻¹ * ‖J‖ := by
  rw [heatGradient_eq hν ht]
  exact norm_heatDerivative_le hν ht i J

theorem continuous_heat_joint {a : ℕ} (ν : ℝ) :
    Continuous (fun p : ℝ × compatibleJets 2 a => heat ν p.1 p.2) := by
  exact (continuous_average_joint (integrable_normal 2)).comp
    (((Real.continuous_sqrt.comp (continuous_const.mul continuous_fst)).neg).prodMk continuous_snd)

theorem continuousOn_heatGradient_joint {a : ℕ} {ν : ℝ} (hν : 0 < ν) (i : Fin 2) :
    ContinuousOn (fun p : ℝ × compatibleJets 2 a => heatGradient ν p.1 i p.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  have hs : Continuous (fun p : ℝ × compatibleJets 2 a => Real.sqrt (2 * ν * p.1)) :=
    Real.continuous_sqrt.comp (continuous_const.mul continuous_fst)
  have hi : ContinuousOn (fun p : ℝ × compatibleJets 2 a => (Real.sqrt (2 * ν * p.1))⁻¹)
      (Ioi (0 : ℝ) ×ˢ univ) := hs.continuousOn.inv₀ (fun p hp =>
        (Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) hν) hp.1)).ne')
  have hc := (continuous_average_joint (a := a) (integrable_momentKernel i)).comp
    (hs.neg.prodMk continuous_snd)
  exact hi.neg.smul hc.continuousOn

end VelocityDetection.PeriodicSpace.Jets
end

end OAI
