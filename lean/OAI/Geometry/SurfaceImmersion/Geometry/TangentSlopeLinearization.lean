import OAI.Geometry.SurfaceImmersion.Geometry.ProjectionSlopeDifferential

namespace OAI

/-! Exact linearization of the projective tangent-direction map. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {n : ℕ}

def directionJetLinearization
    (H : Base → Base →L[ℝ] ProjectionTarget n × ℝ) (b : Bool) (z : Base × ℝ) :
    Base × ℝ →L[ℝ] ProjectionTarget n × ℝ :=
  (H z.1).comp ((ContinuousLinearMap.snd ℝ Base ℝ).smulRight (tangentRayVelocity b)) +
    ((fderiv ℝ H z.1).comp (ContinuousLinearMap.fst ℝ Base ℝ)).flip (tangentRay b z.2)

@[simp] lemma directionJetLinearization_apply
    (H : Base → Base →L[ℝ] ProjectionTarget n × ℝ) (b : Bool) (z w : Base × ℝ) :
    directionJetLinearization H b z w =
      w.2 • H z.1 (tangentRayVelocity b) +
        fderiv ℝ H z.1 w.1 (tangentRay b z.2) := by
  change H z.1 (w.2 • tangentRayVelocity b) +
    fderiv ℝ H z.1 w.1 (tangentRay b z.2) = _
  rw [map_smul]

lemma hasFDerivAt_tangent_direction
    {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    (hH : ContDiff ℝ ∞ H) (b : Bool) (z : Base × ℝ) :
    HasFDerivAt (fun w : Base × ℝ => H w.1 (tangentRay b w.2))
      (directionJetLinearization H b z) z := by
  have h := ((hH.differentiable (by simp) z.1).hasFDerivAt.comp z
    hasFDerivAt_fst).clm_apply
      ((tangentRay_hasDerivAt b z.2).hasFDerivAt.comp z hasFDerivAt_snd)
  exact h

theorem tangentSlope_fderiv
    {H : Base → Base →L[ℝ] ProjectionTarget n × ℝ}
    (hH : ContDiff ℝ ∞ H) (a : ProjectionTarget n) (b : Bool) (z : Base × ℝ)
    (hz : z ∈ tangentSlopeDomain H b) (ha : tangentSlope H b z = a) :
    fderiv ℝ (tangentSlope H b) z =
      (H z.1 (tangentRay b z.2)).2⁻¹ •
        (graphProjection a).comp (directionJetLinearization H b z) := by
  have he : (H z.1 (tangentRay b z.2)).1 =
      (H z.1 (tangentRay b z.2)).2 • a := by
    rw [← ha]
    change (H z.1 (tangentRay b z.2)).1 =
      (H z.1 (tangentRay b z.2)).2 •
        ((H z.1 (tangentRay b z.2)).2⁻¹ • (H z.1 (tangentRay b z.2)).1)
    rw [smul_smul,mul_inv_cancel₀ hz,one_smul]
  exact (hasFDerivAt_graph_slope (hasFDerivAt_tangent_direction hH b z) a hz he).fderiv

theorem regular_tangentSlope_linearization_bijective
    {H : Base → Base →L[ℝ] ProjectionTarget 3 × ℝ}
    (hH : ContDiff ℝ ∞ H) (a : ProjectionTarget 3) (b : Bool) (z : Base × ℝ)
    (hz : z ∈ tangentSlopeDomain H b) (ha : tangentSlope H b z = a)
    (hreg : Function.Surjective (fderiv ℝ (tangentSlope H b) z)) :
    Function.Bijective ((graphProjection a).comp (directionJetLinearization H b z)) := by
  have hs : Function.Surjective ((graphProjection a).comp (directionJetLinearization H b z)) := by
    intro y
    obtain ⟨w,hw⟩ := hreg ((H z.1 (tangentRay b z.2)).2⁻¹ • y)
    rw [tangentSlope_fderiv hH a b z hz ha] at hw
    refine ⟨w,?_⟩
    exact (smul_right_injective _ (inv_ne_zero hz)) hw
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mpr hs,hs⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
