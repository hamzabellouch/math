import OAI.Computability.DegreeRigidity.Representation.RealHullPrescribedTruth
import OAI.Computability.DegreeRigidity.Representation.PrescribedOracleValue

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals ElementaryModel PersistentRestrictions
open GenericIdentity OracleJump
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem prescribed_arithmetic_generic_program (π : Degree ≃o Degree)
    (M K : ZFSet.{0}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K)
    (himages : π (degree (jump FixedArithmetic.zero)) ⊔
      π.symm (degree (jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    ∃ (R : Oracle) (p : OracleCode), realCode R ∈ M ∧
      degree R = π.symm (degree (jump FixedArithmetic.zero)) ∧
      (∀ H : Oracle, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) H →
        SourceEquation p (iterate R 5) (GenericTruth.triple H)) ∧
      (∃ D : ArithmeticPrefixForcing.PrefixPredicate, ArithmeticPrefixForcing.ArithmeticPrefix D ∧
        (∀ n, FiniteShuffle.DenseOpen (D (fun _ => iterate R 5) n)) ∧
        ∀ H : Oracle, ShuffleRequirements.GenericFor (D (fun _ => iterate R 5)) H →
          SourceEquation p (iterate R 5) (GenericTruth.triple H)) ∧
      (∀ Y : Oracle, realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
        ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) Y →
          RepresentsAt π p (iterate R 5) Y) ∧
      ∃ D : ℕ → List Bool → Prop, (∀ n, FiniteShuffle.DenseOpen (D n)) ∧
        (∀ A, ShuffleRequirements.GenericFor D A → Total p (iterate R 5) A) ∧
        ContinuousOn (value p (iterate R 5)) {A | ShuffleRequirements.GenericFor D A} := by
  obtain ⟨a,ha⟩ := InternalCountableOrdinals.nonempty M K hK
  obtain ⟨δ,X,φ,R,hδ,hφ,hX,hRM,hR,hN,hNct,fX,hfX,hall,GX,hGX,hExt,hσ,A₀,p,hA₀,hown,hsem,hcont⟩ :=
    prescribed_oracle_value π M K a hM hT hK ha himages ρ hρ G hG
  have hP := sourceT_real_iterate _ hN.1 hN.2.1 (hN.2.2.1 hRM) 5
  obtain ⟨_,ht,hfinite,hrep⟩ := real_hull_prescribed_transfer M K a hM hT hK ha G hG
    X hX π p (iterate R 5) hP hsem
  exact ⟨R,p,hRM,hR,ht,hfinite,hrep,hcont⟩

end TuringRigidity.RelativeConstructible

end OAI
