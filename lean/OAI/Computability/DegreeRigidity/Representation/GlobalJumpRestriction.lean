import OAI.Computability.DegreeRigidity.Constructibility.PersistentLocality

namespace OAI


namespace TuringRigidity.PersistentLocality
open IdealInterpretation IdealLocality PersistentRestrictions OracleJump

def fullIdeal : DegreeIdeal :=
  ⟨Set.univ,⟨⊥,Set.mem_univ _⟩,fun _ _ => Set.mem_univ _,fun _ _ => Set.mem_univ _⟩

def fullEquiv : Degree ≃o fullIdeal where
  toFun a := ⟨a,Set.mem_univ _⟩
  invFun a := a.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem global_jump_restriction (π : Degree ≃o Degree) (J : CountableIdeal)
    (hjump : JumpClosed (ideal J))
    (himages : π (degree (jump FixedArithmetic.zero)) ⊔
      π.symm (degree (jump FixedArithmetic.zero)) ∈ J.carrier) :
    ∃ ρ : J ≃o J, RestrictsTo π J ρ ∧ Persistent J ρ := by
  let τ : fullIdeal ≃o fullIdeal := fullEquiv.symm.trans (π.trans fullEquiv)
  let z : fullIdeal := fullEquiv (degree (jump FixedArithmetic.zero))
  obtain ⟨σ,hσ⟩ := source_4_1_4 τ z rfl
    (J := ideal J) (fun _ _ => Set.mem_univ _) hjump himages
  let ρ := unlift σ
  have hρ : RestrictsTo π J ρ := by
    intro x
    exact (hσ ⟨x.val,x.property⟩).symm
  exact ⟨ρ,hρ,persistent_of_global_restriction π J ρ hρ⟩

end TuringRigidity.PersistentLocality

end OAI
