import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniversalCoefficientStability
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteBracketWords

namespace OAI

/-! # Restricting the universal BCH polynomial to the nilpotency class -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem rightNestedWord_depth {I : Type*} (d : ℕ) (w : Fin (d + 1) → I) :
    bracketWordDepth (rightNestedWord d w) = d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [rightNestedWord, bracketWordDepth, ih, Nat.zero_max]

theorem universalDynkinPolynomial_truncate {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {c d n : ℕ} (h : c ≤ d)
    (hc : LieModule.lowerCentralSeries ℝ L L c = ⊥) (X : Fin n → L) :
    finiteDynkinPolynomial (universalDynkinCoefficients d n) X =
      finiteDynkinPolynomial (universalDynkinCoefficients c n) X := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold finiteDynkinPolynomial
  rw [Fin.sum_univ_add]
  trans (∑ e : Fin c, ∑ w : Fin (e.val + 1) → Fin n,
    universalDynkinCoefficients c n e w • evalBracketWord X (rightNestedWord e.val w)) + 0
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro w _
      have he := universalDynkinCoefficients_stable (n := n) (Nat.le_add_right c k) e w
      change universalDynkinCoefficients (c + k) n (e.castLE (Nat.le_add_right c k)) w •
        evalBracketWord X (rightNestedWord e.val w) = _
      rw [← he]
    · apply Finset.sum_eq_zero
      intro e _
      apply Finset.sum_eq_zero
      intro w _
      rw [evalBracketWord_eq_zero_of_depth X hc (rightNestedWord _ w) (by
        rw [rightNestedWord_depth]
        exact Nat.le_add_right c e.val), smul_zero]
  · exact add_zero _

end PolycyclicRecognition

end

end OAI
