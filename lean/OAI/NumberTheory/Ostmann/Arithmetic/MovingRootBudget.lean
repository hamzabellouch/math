import OAI.NumberTheory.Ostmann.Arithmetic.MovingTopCells

namespace OAI

/-! # Finite root budgets for the exact moving arithmetic support -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingNodeGuard_cost (CL CR : ℕ) (s v w : ℤ) (hs : s ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) :
    (movingNodeGuard CL CR s v w hs childBound pivotBound L R).pivot.cost = L.cost + R.cost + 6 ∧
    (movingNodeGuard CL CR s v w hs childBound pivotBound L R).rightProduct.cost = R.cost + 2 := by
  simp [movingNodeGuard, wordTransferGuard, wordTransferStep, movingNodeWord,
    HistoryPivotStep.formula, HistoryFormula.bind, HistoryFormula.listProduct, HistoryFormula.cost]
  omega

theorem MovingSlotData.formulaNodes_cost {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (L R : HistoryFormula Bool)
    (D : ℕ) (hL : L.cost ≤ D) (hR : R.cost ≤ D) :
    ∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R,
      max f.guard.pivot.cost f.guard.rightProduct.cost ≤ 2 ^ n * (D + 6) := by
  induction T generalizing L R D with
  | leaf => simp [formulaNodes]
  | @node n s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    let G := step.giantFormula value hf.1 (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R
    have hG : G.cost ≤ 2 * D + 4 := by
      dsimp [G, MovingSlotReversal.giantFormula, HistoryFormula.cost]
      omega
    have hd : D ≤ 2 * D + 4 := by omega
    have hl := ihL hf.2.1 G L (2 * D + 4) hG (hL.trans hd)
    have hr := ihR hf.2.2 G R (2 * D + 4) hG (hR.trans hd)
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have he : 2 ^ n * (2 * D + 4 + 6) ≤ 2 ^ (n + 1) * (D + 6) := by
      rw [pow_succ]; nlinarith
    intro f hmem
    rcases List.mem_cons.mp hmem with h | h
    · subst f
      have hc := movingNodeGuard_cost (MovingSlotReversal.naturalProduct value CL)
        (MovingSlotReversal.naturalProduct value CR) s left.frequency right.frequency hf.1
        (childBound (n + 1)) (pivotBound (n + 1)) L R
      apply max_le
      · rw [hc.1]
        rw [pow_succ]
        nlinarith
      · rw [hc.2]
        rw [pow_succ]
        nlinarith
    · rcases List.mem_append.mp h with h | h
      · exact (hl f h).trans he
      · exact (hr f h).trans he

/-- A uniform explicit bound for the number of real arithmetic cut points.
It is independent of the values of both top giants and of the prime cutoffs. -/
theorem movingTopRootCuts_card {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR : ℕ) :
    (movingTopRootCuts value hvalue childBound pivotBound T hf XR).card ≤
      (2 ^ n - 1) * (3 * (7 * 2 ^ n)) := by
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  have hcost := T.formulaNodes_cost value hvalue childBound pivotBound hf
    (.prime false) (.prime true) 1 (by rfl) (by rfl)
  have hdegree (f : MovingFormulaNode) (hf : f ∈ nodes) (j : Fin 3) :
      (f.guard.polynomials (topGiantInput 0 XR) false j).natDegree ≤ 7 * 2 ^ n := by
    apply (f.guard.polynomials_degree _ _ j).trans
    simpa only [Nat.reduceAdd, mul_comm] using hcost f hf
  apply (movingArithmeticRootCuts_card nodes (topGiantInput 0 XR) false).trans
  calc
    _ ≤ ∑ _f ∈ nodes.toFinset, 3 * (7 * 2 ^ n) := by
      apply Finset.sum_le_sum
      intro f hf
      calc
        _ ≤ ∑ _j : Fin 3, 7 * 2 ^ n := Finset.sum_le_sum (fun j _ => hdegree f (List.mem_toFinset.mp hf) j)
        _ = _ := by simp
    _ = nodes.toFinset.card * (3 * (7 * 2 ^ n)) := by simp
    _ ≤ nodes.length * (3 * (7 * 2 ^ n)) := Nat.mul_le_mul_right _ (List.toFinset_card_le nodes)
    _ = _ := by rw [MovingSlotData.formulaNodes_length]

end Ostmann

end OAI
