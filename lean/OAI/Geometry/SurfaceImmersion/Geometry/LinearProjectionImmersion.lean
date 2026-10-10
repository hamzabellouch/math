import OAI.Geometry.SurfaceImmersion.Geometry.GenericProjectionParameter
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLinearMapBounds
import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionApproximation

namespace OAI

/-! A smooth compact surface immersion in E × R projects to an immersion
in E when E is a Euclidean space of dimension at least four. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma weightedJet_comp {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (w : Base → ℝ) {l : Base → V} {x : Base}
    (hl : DifferentiableAt ℝ l x) :
    weightedJet w (L ∘ l) x = L.comp (weightedJet w l x) := by
  unfold weightedJet
  rw [fderiv_comp x L.differentiableAt hl,L.fderiv]
  ext v
  simp only [ContinuousLinearMap.comp_apply,sub_apply,
    smul_apply,ContinuousLinearMap.smulRight_apply,
    Function.comp_apply,map_sub,map_smul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

theorem SmoothingAtlas.exists_projected_immersion (A : SmoothingAtlas M)
    {n : ℕ} (hn : 4 ≤ n)
    {F : M → ProjectionTarget n × ℝ}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget n × ℝ) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv planeModel 𝓘(ℝ,ProjectionTarget n × ℝ) F p)) :
    ∃ a : ProjectionTarget n,
      ContMDiff planeModel 𝓘(ℝ,ProjectionTarget n) ∞ (graphProjection a ∘ F) ∧
      ∀ p, Function.Injective
        (mfderiv planeModel 𝓘(ℝ,ProjectionTarget n) (graphProjection a ∘ F) p) := by
  classical
  let H (i : A.centers) : Base → Base →L[ℝ] ProjectionTarget n × ℝ :=
    weightedJet (localizedWeight (i : M) (A.weight i))
      (localize (i : M) (A.weight i) F)
  have hH (i : A.centers) : ContDiff ℝ ∞ (H i) :=
    weightedJet_smooth
      (localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i))
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF)
  obtain ⟨a,_ha,ha⟩ := exists_common_projection_parameter hn H hH univ isOpen_univ
    (Set.univ_nonempty : (univ : Set (ProjectionTarget n)).Nonempty)
  have hg : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget n) ∞ (graphProjection a ∘ F) :=
    (graphProjection a).contDiff.contMDiff.comp hF
  refine ⟨a,hg,?_⟩
  intro p
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  let x := chart (i : M) p
  have hx : x ∈ A.coordinateCore i := mem_image_of_mem _ hi
  have hxT := A.coordinateCore_target i hx
  have hw := A.coordinateCore_weight_nonzero i hx
  have hf' := hF.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hHinj : Function.Injective (H i x) :=
    (localized_weightedJet_injective_iff hf' (i : M) (A.weight_smooth i)
      (A.weight_support i) hxT hw).mpr (hI _)
  have hproj := ha i x hHinj
  have hnew : Function.Injective (weightedJet (localizedWeight (i : M) (A.weight i))
      (localize (i : M) (A.weight i) (graphProjection a ∘ F)) x) := by
    rw [localize_clm,weightedJet_comp _ _
      ((localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).differentiable
        (by simp) x)]
    exact hproj
  have hgI := (localized_weightedJet_injective_iff (hg.of_le (by simp)) (i : M)
    (A.weight_smooth i) (A.weight_support i) hxT hw).mp hnew
  change Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget n)
    (graphProjection a ∘ F) ((chart (i : M)).symm (chart (i : M) p))) at hgI
  rwa [(chart (i : M)).left_inv (A.weightCore_source i hi)] at hgI

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
