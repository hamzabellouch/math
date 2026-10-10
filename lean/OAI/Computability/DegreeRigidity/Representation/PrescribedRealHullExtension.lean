import OAI.Computability.DegreeRigidity.Representation.OriginalRealUniformExtension
import OAI.Computability.DegreeRigidity.Representation.OwnDegreeExtensionMeaning
import OAI.Computability.DegreeRigidity.Representation.PrescribedOneRealNames

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing BoundedForcing
open CohenGroundPoset InternalCountableOrdinals ElementaryModel SetDegreeDecoding PersistentRestrictions
open FullSetForcing OriginalRealDefinitionTransport
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem prescribed_real_hull_extension (π : Degree ≃o Degree)
    (M K : ZFSet.{0}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : GroundGeneric M G) :
    let c := conditions (ZFSet.prod K ZFSet.omega)
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT (manyColumn_internal M K hM hT hK.2.1).1
      (manyColumn_internal M K hM hT hK.2.1).2 (InternalCollapse.orderSet_pair c)
        G hG (G.upper le_top G.nonempty.choose_spec)
    let I := modelIdeal M hM hT
    let J := modelIdeal E hE hTE
    ∃ (δ : Ordinal.{0}) (P : Oracle) (φ : SentenceForm),
      δ.toZFSet ∈ M ∧ φ.bound ≤ 2 ∧ P ∈ modelReals E ∧
      let N := RealGeneratedModel.hull M (realCode P)
      RealGeneratedModel.Contains M (realCode P) N ∧ (N : Set ZFSet.{0}).Countable ∧
        ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
          (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
            fX.val H.carrier = definedSubset
              (level (groundReals (genericExtensionSet N c H.carrier)) δ)
                φ (fun _ : Fin φ.bound => realCode P) ∧
            OwnDegreeExtension (genericExtensionSet N c H.carrier)
              (idealSet I) (automorphismSet ρ) (fX.val H.carrier)) ∧
          ∃ GX : GenericFilter (Conditions c), GroundGeneric N GX ∧
            genericExtensionSet N c GX.carrier = E ∧
            ∃ σ : J ≃o J, RestrictsTo π J σ ∧ fX.val GX.carrier = automorphismSet σ := by
  intro c E hE hTE I J
  have hc := (manyColumn_internal M K hM hT hK.2.1).1
  have ho := (manyColumn_internal M K hM hT hK.2.1).2
  have ht : (⊤ : Conditions c) ∈ G.carrier := G.upper le_top G.nonempty.choose_spec
  have hI : idealSet I ∈ M := relativeModel_subset M _ (ground_idealSet_mem_relativeModel M hM hT)
  have hρM : automorphismSet ρ ∈ M := relativeModel_subset M _
    (persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ
      (persistent_of_global_restriction π I ρ hρ))
  have hct : (M : Set ZFSet.{0}).Countable := by
    apply (Set.countable_range (label M)).mono
    intro x hx; exact label_surjective M hx
  obtain ⟨hIJ,σ,hr,he,_,δ,P,φ,hδ,hP,hφ,hPL,hdef,f,a,hf,ha,hfv,hav⟩ :=
    prescribed_one_real_names π M hM hT himages hc ho (InternalCollapse.orderSet_pair c) G hG ht ρ hρ
  have hreal : a.val G.carrier ⊆ ZFSet.omega := hav.symm ▸ realCode_subset P
  have hX : a.val G.carrier ∈ level (groundReals E) δ := hav.symm ▸ hPL
  have hdef' : f.val G.carrier = definedSubset (level (groundReals E) δ) φ
      (fun _ : Fin φ.bound => a.val G.carrier) := by
    rw [hav,hfv]; exact hdef
  have hext : OwnDegreeExtension E (idealSet I) (automorphismSet ρ) (f.val G.carrier) :=
    (own_degree_extension_iff E hE hTE I ρ _).mpr ⟨hIJ,σ,hfv.symm,he⟩
  obtain ⟨hN,hNct,fX,hfX,hall,GX,hGX,hExt,hval⟩ :=
    original_uniform_extension M K (idealSet I) (automorphismSet ρ) hM hT hct hK hI hρM
      a f ha hf G hG hreal δ hδ φ hX hdef' hext
  rw [hav] at hN hNct hfX hall hGX hExt
  exact ⟨δ,P,φ,hδ,hφ,hP,hN,hNct,fX,hfX,hall,GX,hGX,hExt,σ,hr,hval.trans hfv⟩

end TuringRigidity.RelativeConstructible

end OAI
