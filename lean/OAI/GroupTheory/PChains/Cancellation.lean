import OAI.GroupTheory.PChains.Basic
import OAI.GroupTheory.PChains.FinsetCancellation
import OAI.Combinatorics.Order.StrictChains

namespace OAI

/-! Cancellation by a normal p-subgroup, the supporting lemma
`lem:pcore-cancellation` of OpenAI, *The Blockwise Alperin Weight Conjecture*. -/

namespace PCoreCancellation

variable {X : Type*} [Group X] [Fintype X]

noncomputable local instance : Fintype (Subgroup X) :=
  Fintype.ofInjective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective

/-- Strict enumeration identifies actual subgroup chains with the corresponding
strict chains of nontrivial p-subgroups normalized by `J`. -/
noncomputable def chainEquiv (p : ℕ) (J : Subgroup X) :
    Chain p J ≃ FiniteChain.StrictChain (Allowed p J) where
  toFun l := ⟨l.val, l.property.1, fun Q hQ =>
    ⟨(l.property.2.1 Q hQ).1, (l.property.2.1 Q hQ).2,
      (stabilizer_condition J l.val).mp l.property.2.2 Q hQ⟩⟩
  invFun l := ⟨l.val, l.property.1,
    (fun Q hQ => ⟨(l.property.2 Q hQ).1, (l.property.2 Q hQ).2.1⟩),
    (stabilizer_condition J l.val).mpr
      (fun Q hQ => (l.property.2 Q hQ).2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A nontrivial p-core forces cancellation over strictly increasing lists of
nontrivial p-subgroups normalized by `J`. -/
theorem strict_list_pcore_cancellation (p : ℕ) [Fact p.Prime] (J : Subgroup X)
    (hc : pCore p J ≠ ⊥) :
    (∑ l : FiniteChain.StrictChain (Allowed p J), (-1 : ℤ) ^ l.val.length) = 0 := by
  classical
  rw [FiniteChain.strict_list_weight_eq]
  exact pcore_cancellation p J hc

/-- The signed sum over strict p-subgroup chains beginning at the trivial
subgroup and stabilized by `J` vanishes when the p-core of `J` is nontrivial. -/
theorem cancellation (p : ℕ) [Fact p.Prime] (J : Subgroup X)
    (hc : pCore p J ≠ ⊥) :
    (∑ l : Chain p J, (-1 : ℤ) ^ l.val.length) = 0 := by
  classical
  have he : (∑ l : Chain p J, (-1 : ℤ) ^ l.val.length) =
      ∑ l : FiniteChain.StrictChain (Allowed p J), (-1 : ℤ) ^ l.val.length := by
    apply Fintype.sum_equiv (chainEquiv p J)
    intro l
    rfl
  rw [he]
  exact strict_list_pcore_cancellation p J hc

theorem weight_eq_zero (p : ℕ) [Fact p.Prime] (J : Subgroup X)
    (hc : pCore p J ≠ ⊥) : weight p J = 0 :=
  cancellation p J hc

end PCoreCancellation

end OAI
