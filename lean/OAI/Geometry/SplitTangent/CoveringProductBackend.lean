import Mathlib

namespace OAI

/-! Covering Product Backend. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace CoveringProductBackend
variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

 

theorem covering_bijective [ConnectedSpace E] [SimplyConnectedSpace B]
    [LocallyPathConnectedSpace B] {f : E → B} (hf : IsCoveringMap f) :
    Function.Bijective f := by
  let e₀ : E := Classical.arbitrary E
  obtain ⟨g,hg,_⟩ := hf.existsUnique_continuousMap_lifts (ContinuousMap.id B) (f e₀) e₀ rfl
  have hr : ∀ b, f (g b)=b := fun b => congrFun hg.2 b
  have he : g ∘ f = id := by
    apply hf.eq_of_comp_eq (g.continuous.comp hf.continuous) continuous_id
    · funext a
      exact hr (f a)
    · exact hg.1
  have hl : ∀ a, g (f a)=a := fun a => congrFun he a
  exact ⟨Function.LeftInverse.injective hl,Function.RightInverse.surjective hr⟩

 

theorem compact_local_homeomorph_bijective [ConnectedSpace E] [CompactSpace E]
    [T2Space E] [T2Space B] [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    {f : E → B} (hf : IsLocalHomeomorph f) : Function.Bijective f :=
  covering_bijective (isLocalHomeomorph_iff_isCoveringMap.mp hf)

end CoveringProductBackend

namespace CoveringProductBackend
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

theorem simplyConnected_product [SimplyConnectedSpace A] [SimplyConnectedSpace B] :
    SimplyConnectedSpace (A × B) := by
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨inferInstance,?_⟩
  intro x y p q
  obtain ⟨h₁⟩ := SimplyConnectedSpace.paths_homotopic
    (p.map continuous_fst) (q.map continuous_fst)
  obtain ⟨h₂⟩ := SimplyConnectedSpace.paths_homotopic
    (p.map continuous_snd) (q.map continuous_snd)
  have hp : (p.map continuous_fst).prod (p.map continuous_snd)=p := by ext t <;> rfl
  have hq : (q.map continuous_fst).prod (q.map continuous_snd)=q := by ext t <;> rfl
  exact ⟨by simpa only [hp,hq] using Path.Homotopic.prodHomotopy h₁ h₂⟩

end CoveringProductBackend

end

end OAI
