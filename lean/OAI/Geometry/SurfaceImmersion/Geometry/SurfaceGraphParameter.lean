import OAI.Geometry.SurfaceImmersion.Geometry.NonzeroGermDiffeomorphism
import OAI.Geometry.SurfaceImmersion.Geometry.CommonSurfaceCurveGraphs

namespace OAI

/-! Smooth inverse parameters for actual graph branches in a surface chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem surface_graph_parameter {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U)
    (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (g : ℝ → ℝ) (hgraph : ∀ u ∈ U, γ u ∈ c.source ∧
      c (γ u) = ![c (γ u) 0,g (c (γ u) 0)])
    {s : ℝ} (hs : s ∈ U) (hd : deriv (fun u => c (γ u) 0) s ≠ 0) :
    ∃ (e : ℝ ≃ₜ ℝ) (W : Set ℝ),
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (StrictMono e ∨ StrictAnti e) ∧ IsOpen W ∧ s ∈ W ∧ W ⊆ U ∧
      (∀ u ∈ W, e u = c (γ u) 0) ∧
      IsOpen (e '' W) ∧ e s ∈ e '' W ∧
      (∀ x ∈ e '' W, ![x,g x] ∈ c.target ∧
        c.symm ![x,g x] = γ (e.symm x)) := by
  have hcoord : ContDiffOn ℝ ∞ (fun u => c (γ u) 0) U :=
    (contDiff_apply ℝ ℝ 0).comp_contDiffOn
      (hcs.comp hγ (fun u hu => (hgraph u hu).1)).contDiffOn
  obtain ⟨e,he,hei,hem,hee⟩ := nonzero_local_germ_diffeomorphism hU hcoord hs hd
  obtain ⟨V,hV,hsV,hVe⟩ := mem_nhds_iff.mp hee
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hsV
  have hsW : s ∈ W := ⟨hs,hVe⟩
  refine ⟨e,W,he,hei,hem,hW,hsW,inter_subset_left,?_,e.isOpenMap _ hW,
    mem_image_of_mem e hsW,?_⟩
  · intro u hu
    exact hV hu.2
  · rintro x ⟨u,hu,rfl⟩
    have heq : c (γ u) = ![e u,g (e u)] := by
      rw [hV hu.2]
      exact (hgraph u hu.1).2
    refine ⟨heq ▸ c.map_source (hgraph u hu.1).1,?_⟩
    rw [e.symm_apply_apply,← heq,c.left_inv (hgraph u hu.1).1]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
