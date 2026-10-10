import OAI.Computability.DegreeRigidity.Constructibility.OneRealConstructionDefinition
import OAI.Computability.DegreeRigidity.Constructibility.PersistentConstruction

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding PersistentRestrictions OrdinalCoding
universe u

theorem persistent_graph_one_real_definition (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT)
    (hρ : Persistent (modelIdeal M hM hT) ρ) :
    ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
      δ.toZFSet ∈ M ∧ P ∈ modelReals M ∧ p.bound ≤ 2 ∧
      realCode P ∈ level (groundReals M) δ ∧
      automorphismSet ρ = definedSubset (level (groundReals M) δ) p
        (fun _ : Fin p.bound => realCode P) := by
  obtain ⟨t,P,hP,hi,ht,hval⟩ := persistent_graph_construction M hM hT ρ hρ
  obtain ⟨p,hbound,hdef⟩ := t.cofinal_one_real_definition
  obtain ⟨β,_,_,_,hidx,hreal,hset⟩ := hdef M hM hT P hP ht hi 0 (internal_ordinal_zero M hM hT)
  exact ⟨heightDomainIndex (paddedCode t.ordinalVector β),P,p,hidx,hP,hbound,hreal,hval ▸ hset⟩

theorem persistent_extension_one_real_definition (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hIM : I.carrier ⊆ (modelIdeal M hM hT).carrier) :
    ∃ σ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
      Extends hIM ρ σ ∧ Persistent (modelIdeal M hM hT) σ ∧
      ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
        δ.toZFSet ∈ M ∧ P ∈ modelReals M ∧ p.bound ≤ 2 ∧
        realCode P ∈ level (groundReals M) δ ∧
        automorphismSet σ = definedSubset (level (groundReals M) δ) p
          (fun _ : Fin p.bound => realCode P) := by
  obtain ⟨σ,he,hσ,_⟩ := persistent_extension_construction M hM hT I ρ hρ hz hIM
  exact ⟨σ,he,hσ,persistent_graph_one_real_definition M hM hT σ hσ⟩

end TuringRigidity.RelativeConstructible

end OAI
