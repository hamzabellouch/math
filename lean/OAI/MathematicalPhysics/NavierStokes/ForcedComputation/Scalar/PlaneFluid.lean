import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarGlobal
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.TriangularForce
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingCutoffObservation

namespace OAI

/-! The whole-plane scalar produces an actual Navier–Stokes velocity.
The force is prescribed from the drift and source, before solving for w. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter MeasureTheory
open scoped ContDiff Topology

theorem GlobalPlaneScalarSolution.hasDerivWithinAt {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w) {t : ℝ} (ht : 0 ≤ t) (x : Plane) :
    HasDerivWithinAt (fun s => w s x)
      (scalarGenerator ν (a t) (w t) x + h t x) (Ici 0) t := by
  have he := (hw (t + 1) (by linarith)).equation t ⟨ht, by linarith⟩ x
  apply he.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    (show Iic (t + 1) ∈ 𝓝[Ici (0 : ℝ)] t from
      nhdsWithin_le_nhds (Iic_mem_nhds (by linarith : t < t + 1)))] with s hs hs'
  exact ⟨hs, hs'⟩

theorem GlobalPlaneScalarSolution.initialTimeDerivative {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    initialTimeDerivative (triangularVelocity a w) t x =
      triangularLift (fun z => deriv (fun s => a s z) t)
        (fun z => scalarGenerator ν (a t) (w t) z + h t z) x := by
  have hda : HasDerivAt (fun s => a s (horizontalLinear x))
      (deriv (fun s => a s (horizontalLinear x)) t) t :=
    ((ha.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt
  have hdw := hw.hasDerivWithinAt ht (horizontalLinear x)
  have hdu := (planeInclusion.hasFDerivAt.comp_hasDerivWithinAt t hda.hasDerivWithinAt).add
    (hdw.smul_const (basis 2))
  change HasDerivWithinAt (fun s => triangularVelocity a w (s, x)) _ (Ici 0) t at hdu
  exact hdu.derivWithin (uniqueDiffOn_Ici (0 : ℝ) t ht)

theorem triangularVelocity_plane_equation {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    initialTimeDerivative (triangularVelocity a w) t x +
      advection (fun y => triangularVelocity a w (t, y)) x =
      ν • laplacian (fun y => triangularVelocity a w (t, y)) x + triangularForce ν a h (t, x) := by
  have has : ContDiff ℝ ∞ (a t) := ha.comp (contDiff_const.prodMk contDiff_id)
  have hws : ContDiff ℝ ∞ (w t) := (hw t ht).slice_smooth ⟨ht, le_rfl⟩
  rw [hw.initialTimeDerivative ha ht,
    show (fun y => triangularVelocity a w (t, y)) = triangularLift (a t) (w t) from rfl,
    triangularLift_advection has hws, triangularLift_laplacian has hws]
  simp only [triangularLift, triangularForce, planarResidual, scalarGenerator,
    map_add, map_sub, map_smul, smul_add, smul_smul]
  module

theorem triangularVelocity_plane_divergence {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hdiv : ∀ t x, PlanarHamiltonian.divergence (a t) x = 0)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    divergence (fun y => triangularVelocity a w (t, y)) x = 0 := by
  have has : ContDiff ℝ ∞ (a t) := ha.comp (contDiff_const.prodMk contDiff_id)
  rw [show (fun y => triangularVelocity a w (t, y)) = triangularLift (a t) (w t) from rfl,
    triangularLift_divergence has
      ((hw t ht).slice_smooth ⟨ht, le_rfl⟩)]
  exact hdiv t _

theorem triangularVelocity_plane_initial {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w) (ha : ∀ x, a 0 x = 0) (x : Space) :
    triangularVelocity a w (0, x) = 0 := by
  have hz := congrFun (hw 0 le_rfl).initial (horizontalLinear x)
  simp [triangularVelocity, triangularLift, ha, hz]

theorem triangularVelocity_third (a : ℝ → Plane → Plane) (w : ℝ → Plane → ℝ)
    (t : ℝ) (x : Space) : triangularVelocity a w (t, x) 2 = w t (horizontalLinear x) := by
  simp [triangularVelocity, triangularLift, planeInclusion, basis]

/-- Normalized integration over the period-one coordinate gives exactly
    the scalar half-plane observation used in the construction. -/
theorem triangularVelocity_halfPlane_integral (a : ℝ → Plane → Plane)
    (w : ℝ → Plane → ℝ) (t : ℝ) :
    (∫ X in ExpandingDetector.upperHalfPlane, ∫ z in Icc (0 : ℝ) 1,
      triangularVelocity a w (t, atHeight X z) 2) =
      ∫ X in ExpandingDetector.upperHalfPlane, w t X := by
  simp only [triangularVelocity_third, horizontalLinear_eq, atHeight_horizontal,
    setIntegral_const, smul_eq_mul]
  norm_num [Measure.real, Real.volume_Icc]

end ForcedComputation.VelocityDetector

end

end OAI
