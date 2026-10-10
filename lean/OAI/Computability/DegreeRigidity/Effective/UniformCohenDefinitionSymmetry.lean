import OAI.Computability.DegreeRigidity.Constructibility.UniformDefinitionSymmetry
import OAI.Computability.DegreeRigidity.CohenForcing.InternalCohenHomogeneity
import OAI.Computability.DegreeRigidity.CohenForcing.CohenNiceNameConstruction

namespace OAI

namespace TuringRigidity.RelativeConstructible
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem uniform_cohen_definition_symmetric (M A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{0}) (hX : X ∈ M)
    (φ : ElementaryModel.SentenceForm) :
    ∃ f : Name (Conditions (conditions A)), f.encode (label (conditions A)) ∈ M ∧
      (∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        f.val G.carrier = definedSubset
          (level (groundReals (genericExtensionSet M (conditions A) G.carrier)) δ)
            φ (fun _ : Fin φ.bound => X)) ∧
      (∀ B ∈ M, ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        f.val (AutomorphismName.mapFilter (InternalCohenBitFlip.flipIso A B) G).carrier =
          f.val G.carrier) ∧
      (∀ p q : Conditions (conditions A), ∃ B ∈ M, ∃ r,
        r ≤ InternalCohenBitFlip.flipIso A B p ∧ r ≤ q) := by
  have hc := conditions_mem M A hM hT hA
  obtain ⟨f,hf,hfv,hinv⟩ := uniform_ordinal_definition_symmetric M (conditions A)
    hM hT hc δ hδ X hX φ
  refine ⟨f,hf,hfv,?_,?_⟩
  · intro B hB G hG
    exact hinv (InternalCohenBitFlip.flipGraph A B)
      (InternalCohenBitFlip.flipGraph_mem M A B hM hT hA hB)
      (InternalCohenBitFlip.flipIso A B) (InternalCohenBitFlip.flipGraph_spec A B) G hG
  · intro p q
    refine ⟨InternalCohenBitFlip.matchingSet A (label _ p) (label _ q),
      InternalCohenBitFlip.matchingSet_mem M A _ _ hM hT hA
        (hM _ hc _ (label_mem _ p)) (hM _ hc _ (label_mem _ q)),
      InternalCohenBitFlip.matching_common_extension A p q⟩

end TuringRigidity.RelativeConstructible

end OAI
