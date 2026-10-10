import OAI.Geometry.SurfaceImmersion.Geometry.RealNormalProjectionBridge

namespace OAI

/-! Linear chart coordinates preserve the actual second normal projection. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4
open RealModes SmallModes

lemma spherical_secondForm_coordinates {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (x v w : SmallModes.Base)
    (hD : NormalFrame.gramDet
      (spaceCoordinates (fderiv ℝ F (planeCoordinates.symm x) (planeCoordinates.symm dx)))
      (spaceCoordinates (fderiv ℝ F (planeCoordinates.symm x) (planeCoordinates.symm dy))) ≠ 0) :
    realSecondForm (spaceCoordinates ∘ F ∘ planeCoordinates.symm) v w x =
      spaceCoordinates (SphericalJets.secondForm F (planeCoordinates.symm x)
        (planeCoordinates.symm v) (planeCoordinates.symm w)) := by
  let e := planeCoordinates.symm.toContinuousLinearMap
  let L := (fderiv ℝ F (e x)).comp e
  have hfirst (z u : SmallModes.Base) :
      coordDeriv u (spaceCoordinates ∘ F ∘ planeCoordinates.symm) z =
        spaceCoordinates (fderiv ℝ F (e z) (e u)) := by
    simp only [coordDeriv,fderiv_comp z spaceCoordinates.differentiableAt
      ((hF.differentiable (by simp) _).comp _ planeCoordinates.symm.differentiableAt),
      spaceCoordinates.fderiv,fderiv_comp z (hF.differentiable (by simp) _)
        planeCoordinates.symm.differentiableAt,planeCoordinates.symm.fderiv,
      ContinuousLinearMap.comp_apply]
    rfl
  have hsecond : coordDeriv v (coordDeriv w (spaceCoordinates ∘ F ∘ planeCoordinates.symm)) x =
      spaceCoordinates (fderiv ℝ (fderiv ℝ F) (e x) (e v) (e w)) := by
    have he : coordDeriv w (spaceCoordinates ∘ F ∘ planeCoordinates.symm) =
        spaceCoordinates ∘ (fun z => fderiv ℝ F z (e w)) ∘ planeCoordinates.symm := by
      funext z
      exact hfirst z w
    rw [he]
    have hd := ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (e x))
    rw [coordDeriv,fderiv_comp x spaceCoordinates.differentiableAt,
      spaceCoordinates.fderiv]
    · have hcomp : fderiv ℝ ((fun z => fderiv ℝ F z (e w)) ∘ planeCoordinates.symm) x =
          (fderiv ℝ (fun z => fderiv ℝ F z (e w)) (e x)).comp e :=
        ((hd.clm_apply (differentiableAt_const (e w))).hasFDerivAt.comp x e.hasFDerivAt).fderiv
      rw [hcomp]
      simp only [ContinuousLinearMap.comp_apply]
      rw [SphericalJets.derivative_apply hF]
      rfl
    · exact (hd.clm_apply (differentiableAt_const (e w))).comp x planeCoordinates.symm.differentiableAt
  have hr : LinearMap.range L.toLinearMap = LinearMap.range (fderiv ℝ F (e x)).toLinearMap := by
    ext z
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨e u,rfl⟩
    · rintro ⟨u,rfl⟩
      refine ⟨planeCoordinates u,?_⟩
      change fderiv ℝ F (e x) (planeCoordinates.symm (planeCoordinates u)) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
      rfl
  rw [realSecondForm,hfirst x dx,hfirst x dy,hsecond]
  have hp := realNormalPart_starProjection L
    (fderiv ℝ (fderiv ℝ F) (e x) (e v) (e w)) hD
  simp only [hr] at hp
  exact hp

end ClosedSurfaceR4

end

end OAI
