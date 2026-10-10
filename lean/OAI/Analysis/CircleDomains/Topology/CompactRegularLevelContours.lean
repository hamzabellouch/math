import OAI.Analysis.CircleDomains.Selection.RegularLevelPeriodicParametrization

namespace OAI

/-! Finite smooth contour decomposition of the actual compact regular level,
proved by complete tangent flows instead of one-manifold classification. -/
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma compact_regular_level_circle_contours {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ∞ f) (ht : IsPlanarRegularValue f t)
    (hc : IsCompact {z | f z = t}) :
    Finite (ConnectedComponents {z // f z = t}) ∧
      ∃ γ : ConnectedComponents {z // f z = t} → Circle → ℂ,
        (∀ c, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ c) ∧ Topology.IsEmbedding (γ c)) ∧
        Pairwise (fun c d => Disjoint (range (γ c)) (range (γ d))) ∧
        (⋃ c, range (γ c)) = {z | f z = t} := by
  classical
  let M := {z : ℂ // f z = t}
  let x (c : ConnectedComponents M) : M :=
    Classical.choose (ConnectedComponents.surjective_coe c)
  have hx (c : ConnectedComponents M) : ConnectedComponents.mk (x c) = c :=
    Classical.choose_spec (ConnectedComponents.surjective_coe c)
  have hex (c : ConnectedComponents M) := exists_smooth_circle_of_compact_regular_level hf ht hc (x c)
  choose γ hγ using hex
  have hm (c : ConnectedComponents M) {z : ℂ} (hz : z ∈ range (γ c)) :
      ∃ w : M, w.val = z ∧ ConnectedComponents.mk w = c := by
    rw [hγ c |>.2.2] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact ⟨w,rfl,(ConnectedComponents.coe_eq_coe'.mpr hw).trans (hx c)⟩
  refine ⟨finite_connectedComponents_regularLevel hf ht hc,γ,fun c => ⟨(hγ c).1, (hγ c).2.1⟩,?_,?_⟩
  · intro c d hcd
    apply Set.disjoint_left.mpr
    intro z hzc hzd
    obtain ⟨u,hu,huc⟩ := hm c hzc
    obtain ⟨v,hv,hvd⟩ := hm d hzd
    have huv : u = v := Subtype.ext (hu.trans hv.symm)
    exact hcd (huc.symm.trans (huv ▸ hvd))
  · ext z
    constructor
    · intro hz
      obtain ⟨c,hzc⟩ := mem_iUnion.mp hz
      obtain ⟨w,rfl,_⟩ := hm c hzc
      exact w.property
    · intro hz
      let w : M := ⟨z,hz⟩
      let c := ConnectedComponents.mk w
      apply mem_iUnion.mpr
      refine ⟨c,?_⟩
      rw [(hγ c).2.2]
      refine ⟨w,?_,rfl⟩
      apply ConnectedComponents.coe_eq_coe'.mp
      exact (hx c).symm

end CircleDomainRigidity

end

end OAI
