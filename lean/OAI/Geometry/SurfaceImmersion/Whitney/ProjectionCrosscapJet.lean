import OAI.Geometry.SurfaceImmersion.Geometry.ProjectionLocalRepresentatives

namespace OAI

/-! The nondegenerate second-jet condition at a singularity of a regular
three-dimensional projection. This concerns the original unweighted
coordinate representative, not merely the weighted atlas derivative. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def projectedCrosscapJet (Φ : Base → ProjectionTarget 3 × ℝ)
    (a : ProjectionTarget 3) (b : Bool) (x : Base) (t : ℝ) :
    Base × ℝ →L[ℝ] ProjectionTarget 3 :=
  (graphProjection a).comp (directionJetLinearization (fderiv ℝ Φ) b (x,t))

lemma projectedCrosscapJet_apply (Φ : Base → ProjectionTarget 3 × ℝ)
    (a : ProjectionTarget 3) (b : Bool) (x : Base) (t : ℝ) (v : Base) (s : ℝ) :
    projectedCrosscapJet Φ a b x t (v,s) =
      graphProjection a (s • fderiv ℝ Φ x (tangentRayVelocity b) +
        fderiv ℝ (fderiv ℝ Φ) x v (tangentRay b t)) := by
  rw [projectedCrosscapJet,ContinuousLinearMap.comp_apply,directionJetLinearization_apply]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem regular_projection_crosscap_jet {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F)
    (i : A.centers) {Φ : Base → ProjectionTarget 3 × ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) {x : Base} (hx : x ∈ A.coordinateCore i)
    (he : Φ =ᶠ[𝓝 x] F ∘ (chart (i : M)).symm)
    (a : ProjectionTarget 3) (b : Bool) (t : ℝ)
    (hz : (x,t) ∈ tangentSlopeDomain (A.projectionJet F i) b)
    (ha : tangentSlope (A.projectionJet F i) b (x,t) = a)
    (hreg : Function.Surjective (fderiv ℝ (tangentSlope (A.projectionJet F i) b) (x,t))) :
    graphProjection a (fderiv ℝ Φ x (tangentRay b t)) = 0 ∧
      Function.Bijective (projectedCrosscapJet Φ a b x t) := by
  let w := localizedWeight (i : M) (A.weight i)
  have hw : ContDiff ℝ ∞ w :=
    localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
  have hw0 : (w x)^2 ≠ 0 := pow_ne_zero 2 (A.localizedWeight_ne_zero_on_core i hx)
  have hK := A.projectionJet_representative_germ i hΦ hx he
  have hzeroK : graphProjection a (A.projectionJet F i x (tangentRay b t)) = 0 := by
    rw [← ha]
    change (A.projectionJet F i x (tangentRay b t)).1 -
      (A.projectionJet F i x (tangentRay b t)).2 •
        ((A.projectionJet F i x (tangentRay b t)).2⁻¹ •
          (A.projectionJet F i x (tangentRay b t)).1) = 0
    rw [smul_smul,mul_inv_cancel₀ hz,one_smul,sub_self]
  have hzero : graphProjection a (fderiv ℝ Φ x (tangentRay b t)) = 0 := by
    rw [hK.self_of_nhds] at hzeroK
    change graphProjection a ((w x)^2 • fderiv ℝ Φ x (tangentRay b t)) = 0 at hzeroK
    rw [map_smul] at hzeroK
    exact (smul_eq_zero.mp hzeroK).resolve_left hw0
  refine ⟨hzero,?_⟩
  exact regular_weighted_directionJet (hΦ.fderiv_right (m := ∞) (by simp))
    (hw.pow 2) a b x t hw0 hK hzero
    (regular_tangentSlope_linearization_bijective (A.projectionJet_smooth hF i)
      a b (x,t) hz ha hreg)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
