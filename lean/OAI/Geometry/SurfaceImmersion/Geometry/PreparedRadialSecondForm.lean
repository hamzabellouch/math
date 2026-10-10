import OAI.Geometry.SurfaceImmersion.Atlas.SphericalCoordinateSecondForm
import OAI.Geometry.SurfaceImmersion.Primitive.PureRadialCrossing
import OAI.Geometry.Immersion.ClosedSurface.ImmersionJets

namespace OAI

/-! The exact pure-radial second form at a prepared spherical point, in
the same coordinates used by the ordered boundary invariant. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4
open RealModes SmallModes SphericalJets

def scaledSphereCoordinates (F : Plane → Space) (r : ℝ) : RField 4 :=
  spaceCoordinates ∘ (fun y => r • F y) ∘ planeCoordinates.symm

lemma sphereCoordinates_firstDerivative {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (x v : SmallModes.Base) :
    coordDeriv v (spaceCoordinates ∘ F ∘ planeCoordinates.symm) x =
      spaceCoordinates (fderiv ℝ F (planeCoordinates.symm x) (planeCoordinates.symm v)) := by
  simp only [coordDeriv,fderiv_comp x spaceCoordinates.differentiableAt
    ((hF.differentiable (by simp) _).comp _ planeCoordinates.symm.differentiableAt),
    spaceCoordinates.fderiv,fderiv_comp x (hF.differentiable (by simp) _)
      planeCoordinates.symm.differentiableAt,planeCoordinates.symm.fderiv,
    ContinuousLinearMap.comp_apply]
  rfl

lemma scaled_flat_spherical_secondForm {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) {r : ℝ} (hr : r ≠ 0) (x : SmallModes.Base)
    (hflat : ∀ v w, sphericalSecondForm F (planeCoordinates.symm x) v w = 0)
    (hD : NormalFrame.gramDet (coordDeriv dx (scaledSphereCoordinates F r) x)
      (coordDeriv dy (scaledSphereCoordinates F r) x) ≠ 0) (v w : SmallModes.Base) :
    realSecondForm (scaledSphereCoordinates F r) v w x =
      (r⁻¹*(coordDeriv v (scaledSphereCoordinates F r) x ⬝ᵥ
        coordDeriv w (scaledSphereCoordinates F r) x)) •
          spaceCoordinates (-F (planeCoordinates.symm x)) := by
  have hs : ContDiff ℝ ∞ (fun y => r • F y) := hF.const_smul r
  have hd : ∀ u, coordDeriv u (scaledSphereCoordinates F r) x =
      spaceCoordinates (fderiv ℝ (fun y => r • F y) (planeCoordinates.symm x) (planeCoordinates.symm u)) :=
    fun u => sphereCoordinates_firstDerivative hs x u
  have hD' := hD
  rw [hd dx,hd dy] at hD'
  change realSecondForm (spaceCoordinates ∘ (fun y => r • F y) ∘ planeCoordinates.symm) v w x = _
  rw [spherical_secondForm_coordinates hs x v w hD',scaled_spherical_radial_form hF hr,
    hflat,smul_zero,zero_add,map_smul,hd v,hd w,spaceCoordinates_dot]

lemma scaled_flat_spherical_crossing {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) {r : ℝ} (hr : 0 < r) (x : SmallModes.Base)
    (hunit : ‖F (planeCoordinates.symm x)‖ = 1)
    (hflat : ∀ v w, sphericalSecondForm F (planeCoordinates.symm x) v w = 0)
    (hI : Function.Injective (fderiv ℝ (scaledSphereCoordinates F r) x))
    {v w : SmallModes.Base} (hv : v ≠ 0) (hw : w ≠ 0) :
    0 < VelocityFrame.orderedCrossing (scaledSphereCoordinates F r) v w x ((r⁻¹)^2) := by
  have hn : spaceCoordinates (-F (planeCoordinates.symm x)) ⬝ᵥ
      spaceCoordinates (-F (planeCoordinates.symm x)) = 1 := by
    rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,norm_neg,hunit]
    norm_num
  have hD := gramDet_ne_zero_of_injective _ hI
  have hnv : coordDeriv v (scaledSphereCoordinates F r) x ≠ 0 := by
    intro hz
    exact hv (hI (by simpa only [coordDeriv,map_zero] using hz))
  have hnw : coordDeriv w (scaledSphereCoordinates F r) x ≠ 0 := by
    intro hz
    exact hw (hI (by simpa only [coordDeriv,map_zero] using hz))
  exact (VelocityFrame.orderedCrossing_pure_radial x v w _ hr hn hnv hnw
    (scaled_flat_spherical_secondForm hF hr.ne' x hflat hD v v)
    (scaled_flat_spherical_secondForm hF hr.ne' x hflat hD v w)).2

end ClosedSurfaceR4

end

end OAI
