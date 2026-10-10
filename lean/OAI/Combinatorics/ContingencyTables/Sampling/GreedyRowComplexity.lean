import OAI.Combinatorics.ContingencyTables.Sampling.GreedyRowMachine
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialLists

namespace OAI

/-! # Polynomial binary cost of a greedy row pass -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_cellMinimum : PolynomialTime minimum := by
  unfold minimum
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_first polynomial_second)

lemma polynomial_rowCell : PolynomialTime rowCellRealizer := by
  have hA : PolynomialTime (composition
      (second (A := ℕ) (B := RowAccumulator)) first) :=
    polynomial_composition polynomial_second polynomial_first
  have hC : PolynomialTime (first (A := ℕ) (B := RowAccumulator)) := polynomial_first
  have hQ := polynomial_composition (polynomial_pair hA hC) polynomial_cellMinimum
  have hX : PolynomialTime (composition
      (composition (second (A := ℕ) (B := RowAccumulator)) second) first) :=
    polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_first
  have hY : PolynomialTime (composition
      (composition (second (A := ℕ) (B := RowAccumulator)) second) second) :=
    polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_second
  unfold rowCellRealizer
  exact polynomial_congr _ (polynomial_pair
    (polynomial_composition (polynomial_pair hA hQ) polynomial_subtract)
    (polynomial_pair (polynomial_composition (polynomial_pair hQ hX) polynomial_listCons)
      (polynomial_composition
        (polynomial_pair (polynomial_composition (polynomial_pair hC hQ) polynomial_subtract) hY)
        polynomial_listCons)))

/-- No entry produced by a row pass exceeds its original column bound;
the binary list sizes therefore grow by only a constant factor. -/
lemma listSplitRow_bounds (a : ℕ) (cs : List ℕ) :
    (listSplitRow a cs).1≤a ∧
    weight (listSplitRow a cs).2.1≤4*weight cs ∧
    weight (listSplitRow a cs).2.2≤4*weight cs := by
  induction cs generalizing a with
  | nil => simp [listSplitRow,weight_nil]
  | cons c cs ih =>
    have ht := ih (a-min a c)
    have hq := weight_nat_small (min_le_right a c)
    have hc := weight_nat_small (Nat.sub_le c (min a c))
    simp only [listSplitRow,weight_cons]
    exact ⟨ht.1.trans (Nat.sub_le _ _),by omega,by omega⟩

lemma polynomial_rowFold : PolynomialTime (fold rowCellRealizer) := by
  apply polynomial_fold polynomial_rowCell (12*X+10)
  rintro cs ⟨a,xs,ys⟩ pre post he
  have ht := listSplitRow_bounds a pre
  have ha := weight_nat_small ht.1
  have hpre := weight_prefix he
  have hx := weight_append (listSplitRow a pre).2.1.reverse xs
  have hy := weight_append (listSplitRow a pre).2.2.reverse ys
  rw [weight_reverse] at hx hy
  rw [fold_rowCell]
  simp only [weight_prod,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

theorem polynomial_rowSplit : PolynomialTime rowSplitRealizer := by
  unfold rowSplitRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition
  · apply polynomial_composition
    · exact polynomial_pair polynomial_second
        (polynomial_pair polynomial_first (polynomial_constant ([],[])))
    · exact polynomial_rowFold
  · exact polynomial_pair polynomial_first (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
        polynomial_reverse)
      (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
        polynomial_reverse))

end ContingencyTables.GreedyFeasibleTable

end OAI
