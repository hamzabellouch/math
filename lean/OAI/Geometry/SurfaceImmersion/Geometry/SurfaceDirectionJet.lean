import OAI.Geometry.SurfaceImmersion.Whitney.ProjectionCrosscapJet

namespace OAI

/-! The derivative-direction map of an actual three-dimensional surface,
and its relation to the unweighted projection jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def surfaceDirection (f : Base → ProjectionTarget 3) (b : Bool)
    (z : Base × ℝ) : ProjectionTarget 3 := fderiv ℝ f z.1 (tangentRay b z.2)

def surfaceDirectionLinearization (f : Base → ProjectionTarget 3) (b : Bool)
    (z : Base × ℝ) : Base × ℝ →L[ℝ] ProjectionTarget 3 :=
  (fderiv ℝ f z.1).comp ((ContinuousLinearMap.snd ℝ Base ℝ).smulRight (tangentRayVelocity b)) +
    ((fderiv ℝ (fderiv ℝ f) z.1).comp (ContinuousLinearMap.fst ℝ Base ℝ)).flip
      (tangentRay b z.2)

lemma surfaceDirection_smooth {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) : ContDiff ℝ ∞ (surfaceDirection f b) := by
  exact ((hf.fderiv_right (m := ∞) (by simp)).comp contDiff_fst).clm_apply
    ((tangentRay_smooth b).comp contDiff_snd)

lemma surfaceDirection_hasFDerivAt {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (z : Base × ℝ) :
    HasFDerivAt (surfaceDirection f b) (surfaceDirectionLinearization f b z) z := by
  exact ((((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z.1).hasFDerivAt.comp z
    hasFDerivAt_fst).clm_apply
      ((tangentRay_hasDerivAt b z.2).hasFDerivAt.comp z hasFDerivAt_snd))

lemma surfaceDirection_projected {Φ : Base → ProjectionTarget 3 × ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (a : ProjectionTarget 3) (b : Bool) (z : Base × ℝ) :
    surfaceDirection (graphProjection a ∘ Φ) b z =
      graphProjection a (fderiv ℝ Φ z.1 (tangentRay b z.2)) := by
  rw [surfaceDirection,fderiv_comp z.1 (graphProjection a).differentiableAt
    (hΦ.differentiable (by simp) z.1),(graphProjection a).fderiv]
  rfl

lemma surfaceDirection_projected_fderiv {Φ : Base → ProjectionTarget 3 × ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (a : ProjectionTarget 3) (b : Bool) (z : Base × ℝ) :
    fderiv ℝ (surfaceDirection (graphProjection a ∘ Φ) b) z =
      projectedCrosscapJet Φ a b z.1 z.2 := by
  have hd := (graphProjection a).hasFDerivAt.comp z
    (hasFDerivAt_tangent_direction (hΦ.fderiv_right (m := ∞) (by simp)) b z)
  have he : surfaceDirection (graphProjection a ∘ Φ) b =
      graphProjection a ∘ (fun w : Base × ℝ => fderiv ℝ Φ w.1 (tangentRay b w.2)) := by
    funext w
    exact surfaceDirection_projected hΦ a b w
  rw [he,hd.fderiv]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
