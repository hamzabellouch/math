import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderSpatialCalculus
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneTimeRegularity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneFluid

namespace OAI

/-! Classical space-time regularity of the triangular whole-plane solution.
At time zero its time derivative is the right derivative, as in the
Navier–Stokes solution class. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem PlaneScalarSolution.triangularVelocity_plane_smoothOn {T ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) :
    ContDiffOn ℝ ∞ (triangularVelocity a w) (timeCylinder T) := by
  let H : SpaceTime → ℝ × Plane := fun y => (y.1, horizontalLinear y.2)
  have hH : ContDiff ℝ ∞ H :=
    contDiff_fst.prodMk (horizontalLinear.contDiff.comp contDiff_snd)
  have hwc := hw.smooth.comp hH.contDiffOn
    (show MapsTo H (timeCylinder T) (Icc 0 T ×ˢ univ) from
      fun y hy => ⟨hy.1, mem_univ _⟩)
  have hac := ha.comp hH
  exact (planeInclusion.contDiff.comp_contDiffOn hac.contDiffOn).add
    (hwc.smul contDiffOn_const)

theorem GlobalPlaneScalarSolution.velocity_time_differentiable {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    DifferentiableWithinAt ℝ (fun s => triangularVelocity a w (s, x)) (Ici 0) t := by
  have hda : HasDerivAt (fun s => a s (horizontalLinear x))
      (deriv (fun s => a s (horizontalLinear x)) t) t :=
    ((ha.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt
  have hdw := hw.hasDerivWithinAt ht (horizontalLinear x)
  exact ((planeInclusion.hasFDerivAt.comp_hasDerivWithinAt t hda.hasDerivWithinAt).add
    (hdw.smul_const (basis 2))).differentiableWithinAt

theorem GlobalPlaneScalarSolution.velocity_time_formula {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    ShearFlows.initialTimeDerivative (triangularVelocity a w) t x =
      timeDerivative (triangularVelocity a (fun _ _ => 0)) t x +
        planeTimeDerivative ν a h w t (horizontalLinear x) • basis 2 := by
  rw [hw.initialTimeDerivative ha ht, triangularVelocity_timeDerivative ha contDiff_const]
  simp only [triangularLift, planeTimeDerivative, deriv_const, zero_smul, add_zero]

theorem GlobalPlaneScalarSolution.velocity_time_continuous {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (fun y : SpaceTime =>
      ShearFlows.initialTimeDerivative (triangularVelocity a w) y.1 y.2) (timeCylinder T) := by
  have hg := ((hw (T+1) (by linarith)).cylinder_generator (by linarith) ha hh).continuousOn
  have hH : ContinuousOn (fun y : SpaceTime => (y.1, horizontalLinear y.2))
      (timeCylinder T) :=
    (continuous_fst.prodMk (horizontalLinear.continuous.comp continuous_snd)).continuousOn
  have hgc := hg.comp hH (fun y hy => ⟨⟨hy.1.1, by linarith [hy.1.2]⟩, mem_univ _⟩)
  have hb := (timeDerivative_smooth (triangularVelocity_smooth ha (show ContDiff ℝ ∞ (Function.uncurry (fun (_ : ℝ) (_ : Plane) => (0 : ℝ))) from contDiff_const))).continuous
  exact (hb.continuousOn.add (hgc.smul continuousOn_const)).congr
    (fun y hy => hw.velocity_time_formula ha hy.1.1 y.2)

theorem GlobalPlaneScalarSolution.classicalRegularity {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) :
    ClassicalRegularity (triangularVelocity a w) (fun _ => 0) where
  spatial_u t ht := (triangularLift_smooth
    (ha.comp (contDiff_const.prodMk contDiff_id))
    ((hw t ht).slice_smooth ⟨ht, le_rfl⟩)).of_le (by norm_num)
  temporal_u t ht x := hw.velocity_time_differentiable ha ht x
  spatial_p _ _ := contDiff_const
  continuous_u T hT := ((hw T hT).triangularVelocity_plane_smoothOn ha).continuousOn
  continuous_du T hT := by
    have hs := (hw (T+1) (by linarith)).triangularVelocity_plane_smoothOn ha
    exact (cylinder_spatial_fderiv_smooth (by linarith) hs).continuousOn.mono
      (fun y hy => ⟨⟨hy.1.1, by linarith [hy.1.2]⟩, hy.2⟩)
  continuous_ddu T hT := by
    have hs := (hw (T+1) (by linarith)).triangularVelocity_plane_smoothOn ha
    exact (cylinder_second_spatial_fderiv_smooth (by linarith) hs).continuousOn.mono
      (fun y hy => ⟨⟨hy.1.1, by linarith [hy.1.2]⟩, hy.2⟩)
  continuous_ut T hT := hw.velocity_time_continuous ha hh T hT
  continuous_p _ _ := continuousOn_const
  continuous_dp _ _ := by
    simp only [gradient_constant]
    exact continuousOn_const

end ForcedComputation.VelocityDetector

end

end OAI
