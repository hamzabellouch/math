import OAI.Computability.DegreeRigidity.Constructibility.UniformOrdinalStageName
import OAI.Computability.DegreeRigidity.Constructibility.UniformDefinedSubsetName

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
open AtomicForcing BoundedForcing
universe u

theorem uniform_ordinal_definition_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (δ : Ordinal.{u}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{u}) (hX : X ∈ M) (φ : SentenceForm) :
    ∃ f : Name (Conditions c), f.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        f.val G.carrier = definedSubset
          (level (groundReals (genericExtensionSet M c G.carrier)) δ)
            φ (fun _ : Fin φ.bound => X) := by
  obtain ⟨A,hA,hAv⟩ := uniform_ordinal_level_name M hM hT hc hoM ho δ hδ
  obtain ⟨f,hf,hfv⟩ := uniform_checked_definition_name M hM hT hc hoM ho A hA X hX φ
  exact ⟨f,hf,fun G hG ht => by rw [hfv G hG ht,hAv G hG ht]⟩

end TuringRigidity.RelativeConstructible

end OAI
