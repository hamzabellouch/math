import OAI.Computability.DegreeRigidity.Constructibility.RelativePersistentExtension
import OAI.Computability.DegreeRigidity.Representation.CommonGenericModels

namespace OAI

namespace TuringRigidity.FullSetForcing
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions RecursiveNames CountableForcing AtomicForcing
universe u

theorem persistent_extension_name (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (htop : ⊤ ∈ G.carrier)
    (I : CountableIdeal) (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc hoM ho G hG htop
    let J := modelIdeal E hE hTE
    ∃ hIJ : I.carrier ⊆ J.carrier, ∃ σ : J ≃o J,
      Extends hIJ ρ σ ∧ Persistent J σ ∧
      ∃ t : Name (Conditions c), t.encode (label c) ∈ M ∧ t.val G.carrier = automorphismSet σ := by
  intro E hE hTE J
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier htop
  have hIJ : I.carrier ⊆ J.carrier := by
    intro d hd
    obtain ⟨A,hA,rfl⟩ := hIM hd
    refine ⟨A,?_,rfl⟩
    change realCode A ∈ E
    exact hME hA
  obtain ⟨σ,he,hσ,hσE⟩ := RelativeConstructible.persistent_extension_in_model E hE hTE I ρ hρ hz hIJ
  obtain ⟨t,ht,hval⟩ := (mem_extensionSet M c G.carrier _).mp hσE
  exact ⟨hIJ,σ,he,hσ,t,ht,hval⟩

theorem model_automorphism_output_name (M c : ZFSet.{u}) [Countable (Conditions M)]
    (G : Set (Conditions c))
    (hE : Transitive (genericExtensionSet M c G)) (hTE : SourceT (genericExtensionSet M c G))
    (σ : modelIdeal (genericExtensionSet M c G) hE hTE ≃o
      modelIdeal (genericExtensionSet M c G) hE hTE)
    (A : Oracle) (hA : A ∈ modelReals (genericExtensionSet M c G)) :
    ∃ B : Oracle, ∃ t : Name (Conditions c),
      t.encode (label c) ∈ M ∧ t.val G = realCode B ∧
      degree B = (σ ⟨degree A,⟨A,hA,rfl⟩⟩).val := by
  obtain ⟨B,hB,hdegree⟩ := (σ ⟨degree A,⟨A,hA,rfl⟩⟩).property
  obtain ⟨t,ht,hval⟩ := (mem_extensionSet M c G (realCode B)).mp hB
  exact ⟨B,t,ht,hval,hdegree⟩

end TuringRigidity.FullSetForcing

end OAI
