import OAI.Computability.DegreeRigidity.Representation.PrescribedUnrestrictedGroundProgram
import OAI.Computability.DegreeRigidity.Representation.OwnProgramValue
import OAI.Computability.DegreeRigidity.CohenForcing.CohenProgramTotality

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing BoundedForcing
open CohenGroundPoset InternalCountableOrdinals ElementaryModel SetDegreeDecoding PersistentRestrictions
open FullSetForcing CohenColumnRealName OracleJump TableIndices IndexMatrix
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem prescribed_oracle_value (π : Degree ≃o Degree)
    (M K a : ZFSet.{0}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (ha : a ∈ K)
    (himages : π (degree (jump FixedArithmetic.zero)) ⊔
      π.symm (degree (jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    let c := poset K
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT (manyColumn_internal M K hM hT hK.2.1).1
      (manyColumn_internal M K hM hT hK.2.1).2 (InternalCollapse.orderSet_pair c)
        G hG (G.upper le_top G.nonempty.choose_spec)
    let I := modelIdeal M hM hT
    let J := modelIdeal E hE hTE
    ∃ (δ : Ordinal.{0}) (P : Oracle) (φ : SentenceForm) (R : Oracle),
      δ.toZFSet ∈ M ∧ φ.bound ≤ 2 ∧ P ∈ modelReals E ∧
      realCode R ∈ M ∧ degree R = π.symm (degree (jump FixedArithmetic.zero)) ∧
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
            (∃ σ : J ≃o J, RestrictsTo π J σ ∧ fX.val GX.carrier = automorphismSet σ) ∧
            ∃ (A₀ : Oracle) (p : OracleCode),
              (realName K a).val GX.carrier = realCode A₀ ∧
              (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
                ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
                  OwnProgramAt (genericExtensionSet N c H.carrier) (fX.val H.carrier)
                    p (iterate R 5) A) ∧
              (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
                genericExtensionSet N c H.carrier = E →
                ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
                  GenericIdentity.Total p (iterate R 5) A ∧
                    degree (GenericIdentity.value p (iterate R 5) A) = π (degree A)) ∧
              ∃ D : ℕ → List Bool → Prop, (∀ n, FiniteShuffle.DenseOpen (D n)) ∧
                (∀ A, ShuffleRequirements.GenericFor D A → GenericIdentity.Total p (iterate R 5) A) ∧
                ContinuousOn (GenericIdentity.value p (iterate R 5))
                  {A | ShuffleRequirements.GenericFor D A} := by
  intro c E hE hTE I J
  obtain ⟨δ,P,φ,R,hδ,hφ,hP,hRM,hR,hN,hNct,fX,hfX,hall,GX,hGX,hExt,hσ,A₀,d,hA₀,hprog⟩ :=
    prescribed_unrestricted_ground_program π M K a hM hT hK ha himages ρ hρ G hG
  let N := RealGeneratedModel.hull M (realCode P)
  obtain ⟨p,hp⟩ := own_program_of_table d
  have hown : ∀ H : GenericFilter (Conditions c), GroundGeneric N H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
        OwnProgramAt (genericExtensionSet N c H.carrier) (fX.val H.carrier) p (iterate R 5) A := by
    intro H hH A hv
    exact hp _ _ _ _ (hprog H hH A hv)
  refine ⟨δ,P,φ,R,hδ,hφ,hP,hRM,hR,hN,hNct,fX,hfX,hall,GX,hGX,hExt,hσ,A₀,p,hA₀,hown,?_,?_⟩
  · intro H hH he A hv
    obtain ⟨σ,hσπ,hσf⟩ := hσ
    have hfEq := defined_value_extension_eq N c δ (realCode P) φ fX
      (fun H hH => (hall H hH).1) H GX hH hGX (he.trans hExt.symm)
    have hA := hown H hH A hv
    rw [he,hfEq,hσf] at hA
    exact hA.prescribed E J σ π hσπ p (iterate R 5) A
  · exact column_program_generic_totality N K a hN.1 hN.2.1 (hN.2.2.1 hK.2.1) ha GX hGX
      p (iterate R 5) (fun H hH A hv => (hown H hH A hv).1)

end TuringRigidity.RelativeConstructible

end OAI
