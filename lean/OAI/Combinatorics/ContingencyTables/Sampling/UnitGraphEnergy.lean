import OAI.Combinatorics.ContingencyTables.Transport.MetropolisChain

namespace OAI

/-! # Energy of the unit-weight local-proposal chain -/

namespace ContingencyTables.MetropolisChain

open scoped BigOperators Classical
open CommonBasesFPRAS

noncomputable section
variable {X : Type*} [Fintype X] [Nonempty X]

lemma unit_chain_energy (Adj : X → X → Prop) (hsym : ∀ x y,Adj x y ↔ Adj y x)
    (β : ℝ) (hβ : 0 ≤ β) (D : ℕ) (hdegree : ∀ x,(Finset.univ.filter (Adj x)).card ≤ D)
    (hproposal : (D:ℝ)*β ≤ 1/2) (H : X → ℝ) :
    (chain (fun _ => 1) (fun _ => by norm_num) Adj hsym β hβ D hdegree hproposal).energy H=
      (β/(Fintype.card X:ℝ))*((∑ x,∑ y,if Adj x y then (H x-H y)^2 else 0)/2) := by
  unfold chain
  rw [FiniteChain.ofMoves_energy]
  simp only [move,div_self (one_ne_zero : (1:ℝ)≠0),min_self,mul_one,
    normalizer,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hterm (x y : X) :
      (1/(Fintype.card X:ℝ))*(if Adj x y then β else 0)*(H x-H y)^2=
      (β/(Fintype.card X:ℝ))*(if Adj x y then (H x-H y)^2 else 0) := by
    split_ifs <;> ring
  simp_rw [hterm,←Finset.mul_sum]
  ring

end
end ContingencyTables.MetropolisChain

end OAI
