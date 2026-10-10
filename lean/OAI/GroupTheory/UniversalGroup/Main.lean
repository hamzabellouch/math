import OAI.GroupTheory.UniversalGroup.UniverseTransport

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct
open Set Metric Topology

namespace UniversalFInfinity
noncomputable section
universe u

theorem universal_group_of_type_FInfinity :
    ∃ (H : Type u) (groupH : Group H),
      @HasTypeFInfinity H groupH ∧
      ∀ (G : Type u) [Group G] [Group.IsFinitelyPresented G],
        ∃ φ : G →* H, Function.Injective φ := by
  obtain ⟨U,gU,fpU,i,hi⟩ := Higman.NormalWords.embeds_presentation
    RecursiveUniversalThree.enumerator RecursiveUniversalThree.enumerator_primrec.to_comp
  let : Group U := gU
  let : Group.IsFinitelyPresented U := fpU
  have hU : ConcreteEnvelopes.IsUniversal U := by
    intro V _ _
    obtain ⟨j,hj⟩ := RecursiveUniversalThree.universal (G := V)
    exact ⟨i.comp j,hi.comp hj⟩
  obtain ⟨k,hk,hk_inj⟩ := ConcreteEnvelopes.self_maps U hU
  let : Fact (Function.Injective (k (.inl ConcreteEnvelopes.P₂.identity))) := ⟨hk_inj⟩
  let : TopologicalSpace U := ⊥
  let : DiscreteTopology U := ⟨rfl⟩
  let f := k (.inl ConcreteEnvelopes.P₂.identity)
  let H₀ := AscendingTorus.Torus f
  let : TopologicalSpace H₀ := ⊥
  let : DiscreteTopology H₀ := ⟨rfl⟩
  refine ⟨ULift.{u} H₀,inferInstance,?_,?_⟩
  · exact Brown.geometric_lifted_of_uniform
      (TorusGeometry.diagram_milnor_uniform_nullhomotopy k hk)
  · intro G _ _
    obtain ⟨j,hj⟩ := RecursiveUniversalThree.universal (G := G)
    refine ⟨MulEquiv.ulift.symm.toMonoidHom.comp ((AscendingTorus.of f).comp (i.comp j)),?_⟩
    exact MulEquiv.ulift.symm.injective.comp ((AscendingTorus.of_injective f hk_inj).comp
      (hi.comp hj))
end
end UniversalFInfinity

end OAI
