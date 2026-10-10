import OAI.Computability.DegreeRigidity.Constructibility.PersistentOneRealDefinition
import OAI.Computability.DegreeRigidity.Syntax.SetSatisfactionBounded
import OAI.Computability.DegreeRigidity.Constructibility.PersistentExtensionName

namespace OAI

namespace TuringRigidity.FullSetForcing
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions RecursiveNames CountableForcing AtomicForcing RelativeConstructible
universe u

theorem persistent_extension_one_real_names
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
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
      ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
        δ.toZFSet ∈ E ∧ P ∈ modelReals E ∧ p.bound ≤ 2 ∧
        realCode P ∈ level (groundReals E) δ ∧
        automorphismSet σ = definedSubset (level (groundReals E) δ) p
          (fun _ : Fin p.bound => realCode P) ∧
        ∃ r d a l f : Name (Conditions c),
          r.encode (label c) ∈ M ∧ d.encode (label c) ∈ M ∧
          a.encode (label c) ∈ M ∧ l.encode (label c) ∈ M ∧ f.encode (label c) ∈ M ∧
          r.val G.carrier = groundReals E ∧ d.val G.carrier = δ.toZFSet ∧
          a.val G.carrier = realCode P ∧ l.val G.carrier = level (groundReals E) δ ∧
          f.val G.carrier = automorphismSet σ := by
  intro E hE hTE J
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier htop
  have hIJ : I.carrier ⊆ J.carrier := by
    intro d hd
    obtain ⟨A,hA,rfl⟩ := hIM hd
    refine ⟨A,?_,rfl⟩
    change realCode A ∈ E
    exact hME hA
  obtain ⟨σ,he,hσ,δ,P,p,hδ,hP,hp,hPL,hdef⟩ :=
    persistent_extension_one_real_definition E hE hTE I ρ hρ hz hIJ
  have hrE := groundReals_mem E hE hTE
  have hlE := level_mem E _ hE hTE hrE δ hδ
  have hfE : automorphismSet σ ∈ E := by
    rw [hdef]
    exact definedSubset_mem E _ hE hTE.separation.finitePrefix.bounded hlE p
      (fun _ => realCode P) (fun _ => hPL) (by omega)
  obtain ⟨r,hr,hvr⟩ := (mem_extensionSet M c G.carrier _).mp hrE
  obtain ⟨d,hd,hvd⟩ := (mem_extensionSet M c G.carrier _).mp hδ
  obtain ⟨a,ha,hva⟩ := (mem_extensionSet M c G.carrier (realCode P)).mp hP
  obtain ⟨l,hl,hvl⟩ := (mem_extensionSet M c G.carrier _).mp hlE
  obtain ⟨f,hf,hvf⟩ := (mem_extensionSet M c G.carrier _).mp hfE
  exact ⟨hIJ,σ,he,hσ,δ,P,p,hδ,hP,hp,hPL,hdef,r,d,a,l,f,
    hr,hd,ha,hl,hf,hvr,hvd,hva,hvl,hvf⟩

end TuringRigidity.FullSetForcing

end OAI
