import OAI.NumberTheory.Ostmann.Construction.WordTransferReplay

namespace OAI

/-! # Exact expression counts for the concrete transfer template -/

namespace Ostmann.WordTransferTemplate

variable {σ : Type*} {n : ℕ}

theorem branching_leafCount (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) :
    (template.branching t hn).leafCount = 2 ^ n := by
  induction template with
  | leaf word => rfl
  | @node n d l r hl hr =>
    simp only [branching, BranchingWordHistory.leafCount, hl, hr]
    rw [pow_succ]
    omega

theorem branching_nodeCount (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) :
    (template.branching t hn).nodeCount = 2 ^ n - 1 := by
  induction template with
  | leaf word => rfl
  | @node n d l r hl hr =>
    simp only [branching, BranchingWordHistory.nodeCount, hl, hr]
    have h := Nat.one_le_two_pow (n := n)
    rw [pow_succ]
    omega

theorem branching_leafFormulas_length (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ((template.branching t hn).formulaLeaves env).length = 2 ^ n := by
  rw [BranchingWordHistory.formulaLeaves_length, branching_leafCount]

theorem branching_pivotFormulas_length (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ((template.branching t hn).pivotFormulas env).length = 2 ^ n - 1 := by
  rw [BranchingWordHistory.pivotFormulas_length, branching_nodeCount]

end Ostmann.WordTransferTemplate

end OAI
