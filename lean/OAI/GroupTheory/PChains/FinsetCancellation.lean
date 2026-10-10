import OAI.GroupTheory.PChains.Core
import OAI.Combinatorics.Order.ChainToggle

namespace OAI

/-! Alternating cancellation over finite chains of p-subgroups normalized by `J`. -/

namespace PCoreCancellation

open FiniteChain

variable {X : Type*} [Group X] [Fintype X]

noncomputable local instance : Fintype (Subgroup X) :=
  Fintype.ofInjective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective

/-- A p-subgroup normalized by `J`. -/
def Allowed (p : ℕ) (J Q : Subgroup X) : Prop :=
  IsPGroup p Q ∧ J ≤ Subgroup.normalizer (Q : Set X)

/-- The signed sum over chains of nontrivial p-subgroups normalized by `J`,
with the trivial subgroup understood as the first term of each chain. -/
noncomputable def chainWeight (p : ℕ) (J : Subgroup X) : ℤ := by
  classical
  exact ∑ s ∈ chains (Allowed p J), (-1 : ℤ) ^ s.card

theorem cancellation_of_normal_p_subgroup {p : ℕ} [Fact p.Prime]
    {J P : Subgroup X} (hP : NormalPIn p J P) (hne : P ≠ ⊥) :
    chainWeight p J = 0 := by
  classical
  unfold chainWeight
  apply alternating_chain_sum_zero (P := P) hne
  · exact (normalPIn_bot p J).2.symm
  · intro Q hQ
    constructor
    · exact hQ.1.to_sup_of_normal_left' hP.2.2 (hP.1.trans hQ.2)
    · exact (le_inf hQ.2 hP.2.1).trans
        (Subgroup.inf_normalizer_le_normalizer_sup Q P)

/-- A nontrivial p-core makes the alternating chain sum vanish. -/
theorem pcore_cancellation (p : ℕ) [Fact p.Prime] (J : Subgroup X)
    (hc : pCore p J ≠ ⊥) : chainWeight p J = 0 := by
  obtain ⟨P, hP, hne⟩ := exists_normal_p_subgroup hc
  exact cancellation_of_normal_p_subgroup hP hne

end PCoreCancellation

end OAI
