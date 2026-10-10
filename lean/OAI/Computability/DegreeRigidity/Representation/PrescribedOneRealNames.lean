import OAI.Computability.DegreeRigidity.Representation.PrescribedGenericRestriction
import OAI.Computability.DegreeRigidity.Representation.GenericOneRealNames
import OAI.Computability.DegreeRigidity.SetModels.NoNewOrdinals

namespace OAI

namespace TuringRigidity.FullSetForcing
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions RecursiveNames CountableForcing AtomicForcing RelativeConstructible ArithmeticTree
universe u

theorem prescribed_one_real_names (π : Degree ≃o Degree)
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (ho : o ∈ M)
    (hos : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (ht : ⊤ ∈ G.carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ) :
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT hc ho hos G hG ht
    let J := modelIdeal E hE hTE
    ∃ hIJ : (modelIdeal M hM hT).carrier ⊆ J.carrier, ∃ σ : J ≃o J,
      RestrictsTo π J σ ∧ Extends hIJ ρ σ ∧ SetGenericallyPersistent E J σ ∧
      ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
        δ.toZFSet ∈ M ∧ P ∈ modelReals E ∧ p.bound ≤ 2 ∧
        realCode P ∈ level (groundReals E) δ ∧
        automorphismSet σ = definedSubset (level (groundReals E) δ) p
          (fun _ : Fin p.bound => realCode P) ∧
        ∃ f a : Name (Conditions c),
          f.encode (label c) ∈ M ∧ a.encode (label c) ∈ M ∧
          f.val G.carrier = automorphismSet σ ∧ a.val G.carrier = realCode P := by
  intro E hE hTE J
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  have hIJ := modelIdeal_inclusion M E hM hT hE hTE hME
  obtain ⟨σ,hr,he,hp,hd,hg⟩ := prescribed_supermodel_extension π M E hM hT hE hTE hME himages ρ hρ
  obtain ⟨δ,P,p,hδ,hP,hpB,hPL,hdef⟩ := persistent_graph_one_real_definition E hE hTE σ hp
  have hδM := extension_ordinal_ground M c hM hT G.carrier δ hδ
  obtain ⟨f,hf,hfv⟩ := (mem_extensionSet M c G.carrier _).mp (relativeModel_subset E _ hd)
  obtain ⟨a,ha,hav⟩ := (mem_extensionSet M c G.carrier (realCode P)).mp hP
  exact ⟨hIJ,σ,hr,he,hg,δ,P,p,hδM,hP,hpB,hPL,hdef,f,a,hf,ha,hfv,hav⟩

theorem prescribed_output_name (π : Degree ≃o Degree)
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (ho : o ∈ M)
    (hos : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (ht : ⊤ ∈ G.carrier)
    (A : Oracle) (hA : A ∈ modelReals (genericExtensionSet M c G.carrier)) :
    ∃ B : Oracle, ∃ t : Name (Conditions c),
      t.encode (label c) ∈ M ∧ t.val G.carrier = realCode B ∧ degree B = π (degree A) := by
  have hE := genericExtensionSet_transitive M c hM G.carrier
  have hTE := extension_sourceT M hM hT hc ho hos G hG ht
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  obtain ⟨σ,hr,_,_,_⟩ := prescribed_model_restriction π _ hE hTE
    (modelIdeal_inclusion M _ hM hT hE hTE hME himages)
  obtain ⟨B,t,ht,hv,hd⟩ := model_automorphism_output_name M c G.carrier hE hTE σ A hA
  exact ⟨B,t,ht,hv,hd.trans (hr ⟨degree A,⟨A,hA,rfl⟩⟩).symm⟩

end TuringRigidity.FullSetForcing

end OAI
