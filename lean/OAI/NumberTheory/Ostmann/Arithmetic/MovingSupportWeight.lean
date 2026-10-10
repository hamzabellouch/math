import OAI.NumberTheory.Ostmann.Arithmetic.MovingTopCells

namespace OAI

/-! # Separating the exact arithmetic indicator from the recursive weight -/

namespace Ostmann
open scoped Classical

/-- Evaluation along the forced integer pivots with just the arithmetic
indicators removed. The same leaf and node factors remain. -/
noncomputable def movingUnrestrictedWeight {σ : Type*} (value : σ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → ℂ
  | _, .leaf s regular, XL, XR => F ⟨0, .leaf s regular, XL, XR⟩ s
  | n + 1, .node s CL CR u left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
      (extra ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency : ℂ) *
        movingUnrestrictedWeight value F extra left p XL *
        star (movingUnrestrictedWeight value F extra right p XR)

noncomputable def movingArithmeticIndicator {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) : ℂ :=
  if T.ArithmeticSupport value childBound pivotBound XL XR then 1 else 0

theorem movingSlotWeight_arithmeticSupport {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ)
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t ≠ 0) :
    T.ArithmeticSupport value childBound pivotBound XL XR := by
  let a := topGiantInput XL XR
  have hL : (HistoryFormula.prime false).value (fun b => (a b : ℚ)) = (XL : ℚ) := by
    simp [a, topGiantInput]
  have hR : (HistoryFormula.prime true).value (fun b => (a b : ℚ)) = (XR : ℚ) := by
    simp [a, topGiantInput]
  exact (T.formulaNodes_iff value hvalue childBound pivotBound hf XL XR _ _ a hL hR).mp
    (movingSlotWeight_formulaNodes value hvalue childBound pivotBound F extra T t hT hf
      XL XR _ _ a hL hR hw)

/-- The support indicator itself forces the exact positive integer recursion. -/
theorem MovingSlotData.ArithmeticSupport.integral {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (hsupport : T.ArithmeticSupport value childBound pivotBound XL XR) :
    T.Integral value XL XR := by
  induction T generalizing XL XR with
  | leaf => trivial
  | @node n s CL CR u left right ihL ihR =>
    obtain ⟨Q, hQ, hdiv, hleft, hright⟩ := hsupport
    let U := MovingSlotReversal.naturalProduct value u
    let step := MovingSlotData.step s CL CR u left right false
    have hU : 0 < U := Nat.pos_of_ne_zero (MovingSlotReversal.naturalProduct_ne_zero value hvalue u)
    have hp : step.naturalPivot value XL XR = Q / U := by
      change reconstructedPivot _ s / U = Q / U
      congr 1
      apply reconstructedPivot_of_eq _ _ hQ.root_ne_zero Q
      simpa only [step, MovingSlotData.step, Nat.mul_one, movingSlotSystem,
        MovingSlotState.leftProduct, MovingSlotState.rightProduct] using hQ.relation
    have hQeq : Q = U * (Q / U) := (Nat.mul_div_cancel' hdiv).symm
    change (step.IntegralAt value (XL, XR) ∧ _ ∧ _)
    refine ⟨?_, ?_, ?_⟩
    · change 0 < step.naturalPivot value XL XR ∧ _
      rw [hp]
      refine ⟨Nat.div_pos (Nat.le_of_dvd hQ.pivot_pos hdiv) hU, ?_⟩
      change left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
        right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ) =
          s * ((U * (Q / U) : ℕ) : ℤ)
      rw [← hQeq]
      exact hQ.relation
    · rw [hp]
      exact ihL _ _ hleft
    · rw [hp]
      exact ihR _ _ hright

/-- On the derived support every guard evaluates to one, so only the original
leaf weights and extra node factors remain. -/
theorem movingSlotWeight_eq_unrestricted {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (XL XR : ℕ) (hsupport : T.ArithmeticSupport value childBound pivotBound XL XR) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
        movingUnrestrictedWeight value F extra T XL XR := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR with
  | leaf s regular =>
    have hs : s = t := hT
    simp only [recursiveTransferWeight, movingUnrestrictedWeight, hs]
  | @node n s CL CR u left right ihL ihR =>
    obtain ⟨Q, hQ, hdiv, hleft, hright⟩ := hsupport
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    let U := MovingSlotReversal.naturalProduct value u
    let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
    have hU : 0 < U := Nat.pos_of_ne_zero (MovingSlotReversal.naturalProduct_ne_zero value hvalue u)
    have hQ' : ValidTransferNode sys x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) Q := by
      simpa only [← hT.1, ← hT.2.1.root, ← hT.2.2.root] using hQ
    have hp : Q / U = p := by
      rw [← hQ'.historyPivot_eq]
      simp only [historyPivot, sys, movingSlotSystem, MovingSlotState.leftProduct,
        MovingSlotState.rightProduct, x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root,
        p, MovingSlotReversal.naturalPivot, MovingSlotData.step, movingGiantPivot, Nat.mul_one, U]
    have hc : cutoff x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) =
        extra x s left.frequency right.frequency := by
      change (if 0 < U ∧ U ∣ historyPivot sys x t.1 _ _ then _ else 0) = _
      rw [hQ'.historyPivot_eq, ite_eq_left ⟨hU, hdiv⟩]
      simp only [← hT.1, ← hT.2.1.root, ← hT.2.2.root]
    rw [recursiveTransferWeight_node sys F cutoff n x t Q hQ', hc]
    change (extra x s left.frequency right.frequency : ℂ) *
      recursiveTransferWeight sys F cutoff n ⟨n, left, Q / U, XL⟩ t.2.1 *
      star (recursiveTransferWeight sys F cutoff n ⟨n, right, Q / U, XR⟩ t.2.2) = _
    rw [ihL t.2.1 hT.2.1 (Q / U) XL hleft, ihR t.2.2 hT.2.2 (Q / U) XR hright, hp]
    rfl

/-- This factorization includes every zero-support term; it is suitable for
weighted prime sums without conditioning away the original arithmetic tests. -/
theorem movingSlotWeight_indicator_factor {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t =
        movingArithmeticIndicator value childBound pivotBound T XL XR *
          movingUnrestrictedWeight value F extra T XL XR := by
  by_cases hs : T.ArithmeticSupport value childBound pivotBound XL XR
  · rw [movingArithmeticIndicator, ite_eq_left hs, one_mul]
    exact movingSlotWeight_eq_unrestricted value hvalue childBound pivotBound F extra T t hT XL XR hs
  · rw [movingArithmeticIndicator, ite_eq_right hs, zero_mul]
    by_contra hn
    exact hs (movingSlotWeight_arithmeticSupport value hvalue childBound pivotBound F extra T t hT hf XL XR hn)

theorem movingArithmeticIndicator_cells {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL YL XR : ℕ)
    (hres : (XL : ℤ) ≡ (YL : ℤ) [ZMOD movingTopPeriod value hvalue childBound pivotBound T hf])
    (hcell : rootCellCode (movingTopRootCuts value hvalue childBound pivotBound T hf XR) (XL : ℝ) =
      rootCellCode (movingTopRootCuts value hvalue childBound pivotBound T hf XR) (YL : ℝ)) :
    movingArithmeticIndicator value childBound pivotBound T XL XR =
      movingArithmeticIndicator value childBound pivotBound T YL XR := by
  unfold movingArithmeticIndicator
  rw [moving_top_support_cells value hvalue childBound pivotBound T hf XL YL XR hres hcell]

end Ostmann

end OAI
