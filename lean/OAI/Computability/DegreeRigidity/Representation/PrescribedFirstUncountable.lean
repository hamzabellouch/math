import OAI.Computability.DegreeRigidity.SetModels.ValidFirstUncountable
import OAI.Computability.DegreeRigidity.Representation.PrescribedCoveringModel

namespace OAI

namespace TuringRigidity.PrescribedFirstUncountable
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible SetDegreeDecoding
open PersistentRestrictions ArithmeticTree

theorem prescribed_covering_model_with_omega_one (π : Degree ≃o Degree) (A : ℕ → Oracle) :
    ∃ M : ZFSet.{0}, ∃ hM : Transitive M, ∃ hT : SourceT M,
      ∃ hcount : Countable (Conditions M),
        letI := hcount
        Valid M ∧ (∃ K, InternalCountableOrdinals.FirstUncountable M K) ∧ (∀ n, A n ∈ modelReals M) ∧
        (π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
          π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier) ∧
        ∃ ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
          RestrictsTo π _ ρ ∧ Persistent _ ρ ∧
          automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
          SetGenericallyPersistent M _ ρ := by
  obtain ⟨M,hM,hT,hcount,hV,hA,hi,hρ⟩ := prescribed_covering_model.{0} π A
  have hK := ValidFirstUncountable.firstUncountable_exists M hM hV ⟨realCode (A 0),hA 0⟩
  exact ⟨M,hM,hT,hcount,hV,hK,hA,hi,hρ⟩

end TuringRigidity.PrescribedFirstUncountable

end OAI
