import OAI.Geometry.SurfaceImmersion.Geometry.RegularProjectionParameter
import OAI.Geometry.SurfaceImmersion.Geometry.BoundedProjectionDirections
import OAI.Geometry.SurfaceImmersion.Whitney.EuclideanImmersionReduction

namespace OAI

/-! An actual smooth map of every compact surface into three-space with
only finitely many singular points. The regularity of its direction
parameter maps is retained for the subsequent local analysis. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def projectionJet (F : M → ProjectionTarget 3 × ℝ) (i : A.centers) :
    Base → Base →L[ℝ] ProjectionTarget 3 × ℝ :=
  weightedJet (localizedWeight (i : M) (A.weight i)) (localize (i : M) (A.weight i) F)

lemma projectionJet_smooth {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F) (i : A.centers) :
    ContDiff ℝ ∞ (A.projectionJet F i) :=
  weightedJet_smooth
    (localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i))
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF)

theorem finite_singular_projection {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) F p))
    (a : ProjectionTarget 3)
    (hreg : ∀ i b z, z ∈ tangentSlopeDomain (A.projectionJet F i) b →
      tangentSlope (A.projectionJet F i) b z = a →
      Function.Surjective (fderiv ℝ (tangentSlope (A.projectionJet F i) b) z)) :
    {p | ¬ Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (graphProjection a ∘ F) p)}.Finite := by
  classical
  have hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (graphProjection a ∘ F) :=
    (graphProjection a).contDiff.contMDiff.comp hF
  have hji (i : A.centers) (x : Base) (hx : x ∈ A.coordinateCore i) :
      Function.Injective (A.projectionJet F i x) :=
    (localized_weightedJet_injective_iff (hF.of_le (by simp)) (i : M)
      (A.weight_smooth i) (A.weight_support i) (A.coordinateCore_target i hx)
      (A.coordinateCore_weight_nonzero i hx)).mpr (hI _)
  let D (i : A.centers) (b : Bool) :=
    compactProjectionDirections a (A.projectionJet F i) (A.coordinateCore i) b
  have hD (i : A.centers) (b : Bool) : (D i b).Finite :=
    finite_compact_projection_directions (A.projectionJet_smooth hF i)
      (A.coordinateCore_compact i) (hji i) a b (hreg i b)
  have hfinite : (⋃ i : A.centers, ⋃ b : Bool,
      (fun z : Base × ℝ => (chart (i : M)).symm z.1) '' D i b).Finite :=
    Set.finite_iUnion (fun i => Set.finite_iUnion (fun b => (hD i b).image _))
  apply hfinite.subset
  intro p hp
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
  obtain ⟨b,t,ht,hker⟩ := exists_bounded_tangentRay_in_kernel _ hbad
  apply mem_iUnion.mpr
  refine ⟨i,mem_iUnion.mpr ⟨b,?_⟩⟩
  refine ⟨(x,t),⟨⟨hx,ht⟩,hker⟩,?_⟩
  exact (chart (i : M)).left_inv (A.weightCore_source i hi)

theorem exists_finite_singular_projection {F : M → ProjectionTarget 3 × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3 × ℝ) F p)) :
    ∃ a : ProjectionTarget 3,
      (∀ i b z, z ∈ tangentSlopeDomain (A.projectionJet F i) b →
        tangentSlope (A.projectionJet F i) b z = a →
        Function.Surjective (fderiv ℝ (tangentSlope (A.projectionJet F i) b) z)) ∧
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (graphProjection a ∘ F) ∧
      {p | ¬ Function.Injective
        (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (graphProjection a ∘ F) p)}.Finite := by
  obtain ⟨a,_ha,hreg⟩ := exists_regular_projection_parameter
    (A.projectionJet F) (A.projectionJet_smooth hF) univ isOpen_univ Set.univ_nonempty
  exact ⟨a,hreg,(graphProjection a).contDiff.contMDiff.comp hF,
    A.finite_singular_projection hF hI a hreg⟩

end SmoothingAtlas

variable [T2Space M]

theorem exists_smooth_three_map_finite_singular :
    ∃ f : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f ∧
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite := by
  obtain ⟨A⟩ := exists_smoothingAtlas (M := M)
  obtain ⟨F,hF,hI⟩ := exists_smooth_euclidean_four_immersion (M := M)
  let e : ProjectionTarget 4 ≃L[ℝ] ProjectionTarget 3 × ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨he,heI⟩ := smooth_immersion_postcompose e.toContinuousLinearMap e.injective hF hI
  obtain ⟨a,_hreg,hg,hfin⟩ := A.exists_finite_singular_projection he heI
  exact ⟨graphProjection a ∘ (e ∘ F),hg,hfin⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
