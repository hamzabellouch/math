import OAI.Geometry.SurfaceImmersion.Whitney.ProjectionCrosscapJet

namespace OAI

/-! Every singular point of a regular projection has a compact direction
parameter and the nondegenerate unweighted crosscap jet. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem singular_projection_direction {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) F p))
    (a : ProjectionTarget 3) (p : M)
    (hp : ¬ Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (graphProjection a ∘ F) p)) :
    ∃ (i : A.centers) (b : Bool) (t : ℝ), p ∈ A.weightCore i ∧ t ∈ Icc (-1 : ℝ) 1 ∧
      (chart (i : M) p,t) ∈ tangentSlopeDomain (A.projectionJet F i) b ∧
      tangentSlope (A.projectionJet F i) b (chart (i : M) p,t) = a := by
  classical
  have hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (graphProjection a ∘ F) :=
    (graphProjection a).contDiff.contMDiff.comp hF
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  let x := chart (i : M) p
  have hx : x ∈ A.coordinateCore i := mem_image_of_mem _ hi
  have hbad : ¬ Function.Injective ((graphProjection a).comp (A.projectionJet F i x)) := by
    intro hinj
    have hnew : Function.Injective (weightedJet (localizedWeight (i : M) (A.weight i))
        (localize (i : M) (A.weight i) (graphProjection a ∘ F)) x) := by
      rw [localize_clm,weightedJet_comp _ _
        ((localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).differentiable
          (by simp) x)]
      exact hinj
    have hImm := (localized_weightedJet_injective_iff (hg.of_le (by simp)) (i : M)
      (A.weight_smooth i) (A.weight_support i) (A.coordinateCore_target i hx)
      (A.coordinateCore_weight_nonzero i hx)).mp hnew
    apply hp
    change Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3)
      (graphProjection a ∘ F) ((chart (i : M)).symm (chart (i : M) p))) at hImm
    rwa [(chart (i : M)).left_inv (A.weightCore_source i hi)] at hImm
  have hjet : Function.Injective (A.projectionJet F i x) :=
    (localized_weightedJet_injective_iff (hF.of_le (by simp)) (i : M)
      (A.weight_smooth i) (A.weight_support i) (A.coordinateCore_target i hx)
      (A.coordinateCore_weight_nonzero i hx)).mpr (hI _)
  obtain ⟨b,t,ht,hker⟩ := exists_bounded_tangentRay_in_kernel _ hbad
  have hfst : (A.projectionJet F i x (tangentRay b t)).1 =
      (A.projectionJet F i x (tangentRay b t)).2 • a := sub_eq_zero.mp hker
  have hlast : (A.projectionJet F i x (tangentRay b t)).2 ≠ 0 := by
    intro hz
    have he0 : A.projectionJet F i x (tangentRay b t) = A.projectionJet F i x 0 := by
      rw [map_zero]
      apply Prod.ext
      · change (A.projectionJet F i x (tangentRay b t)).1 = 0
        simpa only [hz,zero_smul] using hfst
      · exact hz
    exact tangentRay_ne_zero b t (hjet he0)
  refine ⟨i,b,t,hi,ht,hlast,?_⟩
  change (A.projectionJet F i x (tangentRay b t)).2⁻¹ •
    (A.projectionJet F i x (tangentRay b t)).1 = a
  rw [hfst,smul_smul,inv_mul_cancel₀ hlast,one_smul]

theorem singular_projection_crosscap_jet {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) F p))
    (a : ProjectionTarget 3)
    (hreg : ∀ i b z, z ∈ tangentSlopeDomain (A.projectionJet F i) b →
      tangentSlope (A.projectionJet F i) b z = a →
      Function.Surjective (fderiv ℝ (tangentSlope (A.projectionJet F i) b) z))
    (p : M) (hp : ¬ Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (graphProjection a ∘ F) p)) :
    ∃ (i : A.centers) (b : Bool) (t : ℝ) (Φ : Base → ProjectionTarget 3 × ℝ),
      p ∈ A.weightCore i ∧ t ∈ Icc (-1 : ℝ) 1 ∧ ContDiff ℝ ∞ Φ ∧
      Φ =ᶠ[𝓝 (chart (i : M) p)] F ∘ (chart (i : M)).symm ∧
      graphProjection a (fderiv ℝ Φ (chart (i : M) p) (tangentRay b t)) = 0 ∧
      Function.Bijective (projectedCrosscapJet Φ a b (chart (i : M) p) t) := by
  obtain ⟨i,b,t,hi,ht,hdom,hval⟩ := A.singular_projection_direction hF hI a p hp
  obtain ⟨Φ,hΦ,hgerm⟩ := A.exists_projection_representatives hF
  have hx : chart (i : M) p ∈ A.coordinateCore i := mem_image_of_mem _ hi
  have hres := A.regular_projection_crosscap_jet hF i (hΦ i) hx (hgerm i _ hx)
    a b t hdom hval (hreg i b _ hdom hval)
  exact ⟨i,b,t,Φ i,hi,ht,hΦ i,hgerm i _ hx,hres⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
