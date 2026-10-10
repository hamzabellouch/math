import OAI.Computability.DegreeRigidity.Representation.GlobalJumpRestriction
import OAI.Computability.DegreeRigidity.Representation.GenericDescentDefinition

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions ArithmeticTree
universe u

theorem prescribed_model_restriction (π : Degree ≃o Degree)
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier) :
    ∃ ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
      RestrictsTo π _ ρ ∧ Persistent _ ρ ∧
      automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
      SetGenericallyPersistent M _ ρ := by
  obtain ⟨ρ,hr,hp⟩ := PersistentLocality.global_jump_restriction π _
    (modelIdeal_jump M hM hT) himages
  have hd := persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hp
  have hI := relativeModel_subset M _ (ground_idealSet_mem_relativeModel M hM hT)
  have hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ (modelIdeal M hM hT).carrier :=
    ⟨_,sourceT_real_jump M hM hT (sourceT_zero_real M hM hT),rfl⟩
  exact ⟨ρ,hr,hp,hd,(setGenericallyPersistent_iff M hM hT _ hI ρ
    (relativeModel_subset M _ hd) hz).mpr hp⟩

theorem prescribed_restriction_unique (π : Degree ≃o Degree) (I : CountableIdeal)
    (ρ σ : I ≃o I) (hρ : RestrictsTo π I ρ) (hσ : RestrictsTo π I σ) : ρ = σ := by
  apply DFunLike.ext
  intro x
  exact Subtype.ext ((hρ x).symm.trans (hσ x))

theorem prescribed_model_one_real_definition (π : Degree ≃o Degree)
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier) :
    ∃ ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
      RestrictsTo π _ ρ ∧ SetGenericallyPersistent M _ ρ ∧
      automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
      ∃ (δ : Ordinal.{u}) (P : Oracle) (p : SentenceForm),
        δ.toZFSet ∈ M ∧ P ∈ modelReals M ∧ p.bound ≤ 2 ∧
        realCode P ∈ level (groundReals M) δ ∧
        automorphismSet ρ = definedSubset (level (groundReals M) δ) p
          (fun _ : Fin p.bound => realCode P) := by
  obtain ⟨ρ,hr,hp,hd,hg⟩ := prescribed_model_restriction π M hM hT himages
  exact ⟨ρ,hr,hg,hd,persistent_graph_one_real_definition M hM hT ρ hp⟩

end TuringRigidity.RelativeConstructible

end OAI
