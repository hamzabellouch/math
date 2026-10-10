import OAI.Computability.LoopMatching.Model

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

open scoped BigOperators

namespace LoopMatching

theorem loopVertices_card_le {n : ℕ} (M : PartialMatching n) :
    (loopVertices M).card ≤ n := by
  classical
  simpa using Finset.card_le_card (Finset.subset_univ (loopVertices M))

theorem countWithLoops_eq_zero_of_lt (G : Input) {j : ℕ} (hj : G.n < j) :
    countWithLoops G j = 0 := by
  classical
  unfold countWithLoops
  apply Finset.sum_eq_zero
  intro M hM
  have hne : (loopVertices M).card ≠ j := by
    intro heq
    have hle := loopVertices_card_le M
    rw [heq] at hle
    exact (Nat.not_le_of_gt hj) hle
  simp only [hne, ↓reduceIte]

theorem count_eq_sum_countWithLoops (G : Input) :
    count G = ∑ j ∈ Finset.range (G.n + 1), countWithLoops G j := by
  classical
  unfold count countWithLoops
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M hM
  symm
  calc
    _ = (if (loopVertices M).card = (loopVertices M).card then weight G M else 0) := by
      apply Finset.sum_eq_single (loopVertices M).card
      · intro j hj hne
        simp only [Ne.symm hne, ↓reduceIte]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr
          (Nat.lt_succ_of_le (loopVertices_card_le M)))).elim
    _ = weight G M := ite_eq_left rfl

theorem weight_eq_zero_of_loopMultiplicity_eq_zero (G : Input)
    (M : PartialMatching G.n) (v : Fin G.n)
    (hv : v ∈ loopVertices M) (hzero : loopMultiplicity G v = 0) :
    weight G M = 0 := by
  classical
  unfold weight
  rw [Finset.prod_eq_zero hv hzero, mul_zero]

theorem weight_eq_zero_of_multiplicity_eq_zero (G : Input)
    (M : PartialMatching G.n) (e : BinaryMatching.Pair G.n)
    (he : e ∈ M.val) (hzero : BinaryMatching.multiplicity G.ordinary e = 0) :
    weight G M = 0 := by
  classical
  unfold weight
  rw [Finset.prod_eq_zero he hzero, zero_mul]

theorem count_eq_zero_of_forall_weight_eq_zero (G : Input)
    (hzero : ∀ M : PartialMatching G.n, weight G M = 0) : count G = 0 := by
  classical
  unfold count
  exact Finset.sum_eq_zero (fun M _ => hzero M)

end LoopMatching

end OAI
