import OAI.Geometry.SurfaceImmersion.Primitive.BlendedVelocityPath
import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityPeriod

namespace OAI

/-! Exact unit-period moment equations for the prescribed collar density. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def unitDensity (a t : ℝ) : ℝ := density a (2 * Real.pi * t)

lemma unitDensity_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => unitDensity z.1 z.2) :=
  density_smooth.comp (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd))

lemma unitDensity_pos (a t : ℝ) : 0 < unitDensity a t := density_pos a _

lemma unitDensity_periodic (a : ℝ) : Function.Periodic (unitDensity a) 1 := by
  intro t
  unfold unitDensity
  rw [mul_add, mul_one]
  exact density_periodic a _

@[simp] lemma unitDensity_zero (t : ℝ) : unitDensity 0 t = 1 := density_zero _

lemma blendedPath_collar (a A t : ℝ) :
    blendedPath a A 0 0 t = ![arcX a (2 * Real.pi * t), arcY a (2 * Real.pi * t)] := by
  simp [blendedPath, blendedAngle, cos_baseAngle, sin_baseAngle]

lemma collar_density_moments (a A : ℝ) :
    (∫ t in 0..1, unitDensity a t • LoopDensity.augment (blendedPath a A 0 0 t)) =
      LoopDensity.augment ![(1 - a ^ 2 / 2) / (1 + a ^ 2 / 2), 0] := by
  let f : ℝ → LoopDensity.Moments := fun t =>
    unitDensity a t • LoopDensity.augment (blendedPath a A 0 0 t)
  have hp : Continuous (blendedPath a A 0 0) := by
    have hang : Continuous (blendedAngle a A 0 0) := by
      unfold blendedAngle baseAngle
      fun_prop
    have hscaled : Continuous (fun t : ℝ => blendedAngle a A 0 0 (2 * Real.pi * t)) :=
      hang.comp (continuous_const.mul continuous_id)
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.continuous_cos.comp hscaled
    · exact Real.continuous_sin.comp hscaled
  have hρ : Continuous (unitDensity a) :=
    unitDensity_smooth.continuous.comp (continuous_const.prodMk continuous_id)
  have hf : Continuous f :=
    hρ.smul (LoopDensity.augment_continuous.comp hp)
  have heval (i : Fin 3) : (∫ t in 0..1, f t) i = ∫ t in 0..1, f t i :=
    ((ContinuousLinearMap.proj i : LoopDensity.Moments →L[ℝ] ℝ).intervalIntegral_comp_comm
      (hf.intervalIntegrable 0 1)).symm
  change (∫ t in 0..1, f t) = _
  ext i
  rw [heval]
  fin_cases i
  · change (∫ t in 0..1, unitDensity a t * 1) = 1
    simp only [mul_one, unitDensity]
    rw [integral_rescale, mean_density]
  · change (∫ t in 0..1, unitDensity a t * (blendedPath a A 0 0 t) 0) = _
    simp only [blendedPath_collar, Matrix.cons_val_zero, unitDensity]
    exact (integral_rescale (fun u => density a u * arcX a u)).trans (mean_density_arcX a)
  · change (∫ t in 0..1, unitDensity a t * (blendedPath a A 0 0 t) 1) = 0
    simp only [blendedPath_collar, Matrix.cons_val_one, Matrix.cons_val_zero, unitDensity]
    exact (integral_rescale (fun u => density a u * arcY a u)).trans (mean_density_arcY a)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
