import OAI.Computability.DegreeRigidity.Constructibility.UniformOrdinalDefinitionName
import OAI.Computability.DegreeRigidity.SetModels.InternalOrderIsoTransport

namespace OAI

namespace TuringRigidity.RelativeConstructible
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem uniform_ordinal_definition_symmetric (M c : ZFSet.{0})
    [OrderTop (Conditions c)] (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{0}) (hX : X ∈ M)
    (φ : ElementaryModel.SentenceForm) :
    ∃ f : Name (Conditions c), f.encode (label c) ∈ M ∧
      (∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        f.val G.carrier = definedSubset
          (level (groundReals (genericExtensionSet M c G.carrier)) δ)
            φ (fun _ : Fin φ.bound => X)) ∧
      ∀ w ∈ M, ∀ e : Conditions c ≃o Conditions c,
        (∀ p q, ZFSet.pair (label c p) (label c q) ∈ w ↔ q = e p) →
        ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
          f.val (AutomorphismName.mapFilter e G).carrier = f.val G.carrier := by
  obtain ⟨f,hf,hfv⟩ := uniform_ordinal_definition_name M hM hT hc
    (InternalCollapse.orderSet_mem M hM hT hc) (InternalCollapse.orderSet_pair c) δ hδ X hX φ
  have hall (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
      f.val G.carrier = definedSubset
        (level (groundReals (genericExtensionSet M c G.carrier)) δ)
          φ (fun _ : Fin φ.bound => X) := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact hfv G hG (G.upper le_top hp)
  refine ⟨f,hf,hall,?_⟩
  intro w hw e he G hG
  have hGe := InternalOrderIsoTransport.map_ground_generic M c c w hM hT hc hc hw e he G hG
  rw [hall _ hGe,hall G hG,InternalOrderIsoTransport.extension_eq M c c w hM hT hc hc hw e he G hG]

end TuringRigidity.RelativeConstructible

end OAI
