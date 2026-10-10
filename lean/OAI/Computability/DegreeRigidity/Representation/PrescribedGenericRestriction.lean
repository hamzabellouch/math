import OAI.Computability.DegreeRigidity.Representation.PrescribedModelRestriction

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions ArithmeticTree CountableForcing
universe u

theorem modelIdeal_inclusion (M N : ZFSet.{u})
    [Countable (Conditions M)] [Countable (Conditions N)]
    (hM : Transitive M) (hTM : SourceT M) (hN : Transitive N) (hTN : SourceT N)
    (hMN : M ⊆ N) : (modelIdeal M hM hTM).carrier ⊆ (modelIdeal N hN hTN).carrier := by
  rintro d ⟨A,hA,rfl⟩
  refine ⟨A,?_,rfl⟩
  change realCode A ∈ N
  exact hMN hA

theorem prescribed_restrictions_coherent (π : Degree ≃o Degree) (I J : CountableIdeal)
    (ρ : I ≃o I) (σ : J ≃o J) (hρ : RestrictsTo π I ρ) (hσ : RestrictsTo π J σ)
    (d : Degree) (hi : d ∈ I.carrier) (hj : d ∈ J.carrier) :
    (ρ ⟨d,hi⟩).val = (σ ⟨d,hj⟩).val := (hρ ⟨d,hi⟩).symm.trans (hσ ⟨d,hj⟩)

theorem prescribed_restrictions_extend (π : Degree ≃o Degree) (I J : CountableIdeal)
    (ρ : I ≃o I) (σ : J ≃o J) (hρ : RestrictsTo π I ρ) (hσ : RestrictsTo π J σ)
    (hIJ : I.carrier ⊆ J.carrier) : Extends hIJ ρ σ := by
  intro d
  exact (prescribed_restrictions_coherent π I J ρ σ hρ hσ d.val d.property (hIJ d.property)).symm

theorem prescribed_supermodel_extension (π : Degree ≃o Degree) (M N : ZFSet.{u})
    [Countable (Conditions M)] [Countable (Conditions N)]
    (hM : Transitive M) (hTM : SourceT M) (hN : Transitive N) (hTN : SourceT N)
    (hMN : M ⊆ N)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hTM).carrier)
    (ρ : modelIdeal M hM hTM ≃o modelIdeal M hM hTM) (hρ : RestrictsTo π _ ρ) :
    ∃ σ : modelIdeal N hN hTN ≃o modelIdeal N hN hTN,
      RestrictsTo π _ σ ∧ Extends (modelIdeal_inclusion M N hM hTM hN hTN hMN) ρ σ ∧
      Persistent _ σ ∧ automorphismSet σ ∈ relativeModel N (groundReals N) ∧
      SetGenericallyPersistent N _ σ := by
  have hIJ := modelIdeal_inclusion M N hM hTM hN hTN hMN
  obtain ⟨σ,hr,hp,hd,hg⟩ := prescribed_model_restriction π N hN hTN (hIJ himages)
  exact ⟨σ,hr,prescribed_restrictions_extend π _ _ ρ σ hρ hr hIJ,hp,hd,hg⟩

theorem prescribed_generic_extension (π : Degree ≃o Degree)
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (ho : o ∈ M)
    (hos : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (ht : ⊤ ∈ G.carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc ho hos G hG ht
    ∃ σ : modelIdeal E hE hTE ≃o modelIdeal E hE hTE,
      RestrictsTo π _ σ ∧
      (∀ d, ∀ hd : d ∈ (modelIdeal M hM hT).carrier,
        ∀ he : d ∈ (modelIdeal E hE hTE).carrier, (σ ⟨d,he⟩).val = (ρ ⟨d,hd⟩).val) ∧
      Persistent _ σ ∧ automorphismSet σ ∈ relativeModel E (groundReals E) ∧
      SetGenericallyPersistent E _ σ := by
  intro E hE hTE
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  obtain ⟨σ,hr,_,hp,hd,hg⟩ := prescribed_supermodel_extension π M E hM hT hE hTE hME himages ρ hρ
  exact ⟨σ,hr,fun d hi hj => (prescribed_restrictions_coherent π _ _ ρ σ hρ hr d hi hj).symm,
    hp,hd,hg⟩

end TuringRigidity.RelativeConstructible

end OAI
