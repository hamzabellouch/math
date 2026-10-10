import OAI.Combinatorics.ContingencyTables.Transport.IntegerMarginal

namespace OAI

/-!
# The actual weighted integer pair estimate

For first-paper transport the pair display has total B+1 and capacity B,
so only the interior matrices are valid. The potential identity uses
exactly those matrices and the actual cumulative cross entries; it never
assumes an endpoint matrix signature.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The D'=B+1 weighted estimate for the actual raw integer removal forms.
The required balance is the zero total signed cross flow at the pair. -/
theorem weighted_pair_potential
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ) (z : I → ℕ) (v : I → ℝ)
    (hsig : ∀ j, 0 < j → j < M →
      OnePositiveDirection (integerRemovalMatrix F (profile z j (M-j))).toBilin')
    (hpos : ∀ j, 0 < j → j < M → 0 < F (profile z (j-1) (M-1-j)))
    (hbalance : pairCumulative (cross F M z) v M = 0) :
    2*(∑ j ∈ Finset.range (M+1), innerWeight F M z j *
      pairCoefficient (cross F M z) (innerWeight F M z) v j ^ 2) ≤
      -(∑ j ∈ Finset.range (M+1), (j:ℝ)*((M:ℝ)-j)*
        (pairMatrix F M z j).toBilin' (old v) (old v)) := by
  apply balancedPair_weighted_potential M (fun j => (pairMatrix F M z j).toBilin') old
    (Pi.single (.inr false) 1) (Pi.single (.inr true) 1) (cross F M z) (innerWeight F M z) v
  · intro j _ _ x y
    exact (matrix_bilin_symm _ (integerRemoval_symm _ _)).eq x y
  · exact hsig
  · simp [innerWeight]
  · simp [innerWeight]
  · intro j hj0 hjM
    have ht : 0 < j ∧ j < M := ⟨hj0,hjM⟩
    simpa only [innerWeight,ite_eq_left ht] using hpos j hj0 hjM
  · exact hbalance
  · intro j _ hjM; simpa using pairMatrix_aa F M z j hjM.le
  · intro j _ hjM; simpa using pairMatrix_bb F M z j hjM.le
  · intro j _ hjM; simpa using pairMatrix_ab F M z j hjM.le
  · intro j _ hjM; exact cross_a F M z j hjM.le v
  · intro j _ hjM; exact cross_b F M z j hjM.le v

end ContingencyTables.IntegerWeightedTransport

end OAI
