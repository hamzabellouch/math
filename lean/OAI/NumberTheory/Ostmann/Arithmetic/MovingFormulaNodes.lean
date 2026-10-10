import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantFormulas

namespace OAI

/-! # All rational node formulas of the concrete moving sampler -/

namespace Ostmann
open scoped Classical

structure MovingFormulaNode where
  guard : WordTransferGuard Bool
  newGiant : HistoryFormula Bool

noncomputable def MovingSlotData.formulaNodes {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) :
    {n : ℕ} → (T : MovingSlotData σ n) → T.Frequencies (· ≠ 0) →
      HistoryFormula Bool → HistoryFormula Bool → List MovingFormulaNode
  | _, .leaf _ _, _, _, _ => []
  | n + 1, .node s CL CR u left right, hf, L, R =>
      let step := MovingSlotData.step s CL CR u left right false
      let P := step.giantFormula value hf.1
        (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R
      { guard := movingNodeGuard (MovingSlotReversal.naturalProduct value CL)
          (MovingSlotReversal.naturalProduct value CR) s left.frequency right.frequency hf.1
          (childBound (n + 1)) (pivotBound (n + 1)) L R
        newGiant := P } ::
        (left.formulaNodes value hvalue childBound pivotBound hf.2.1 P L ++
          right.formulaNodes value hvalue childBound pivotBound hf.2.2 P R)

theorem MovingSlotData.formulaNodes_length {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (L R : HistoryFormula Bool) :
    (T.formulaNodes value hvalue childBound pivotBound hf L R).length = 2 ^ n - 1 := by
  induction T generalizing L R with
  | leaf s regular => rfl
  | @node n s CL CR u left right ihL ihR =>
    simp only [formulaNodes, List.length_cons, List.length_append, ihL, ihR, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

/-- Every node formula is constructed before the top giants are evaluated.
Nonzero original coefficients imply all its exact arithmetic guard and
compensation-integrality tests, including both recursive branches. -/
theorem movingSlotWeight_formulaNodes {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ)
    (extra : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) (L R : HistoryFormula Bool) (a : Bool → ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ))
    (hw : recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound extra) n ⟨n, T, XL, XR⟩ t ≠ 0) :
    ∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R,
      f.guard.ValidAt a ∧ f.newGiant.IntegralAt a := by
  let sys := movingSlotSystem value childBound pivotBound
  let cutoff := movingSlotCutoff value childBound pivotBound extra
  induction T generalizing XL XR L R with
  | leaf s regular => simp [MovingSlotData.formulaNodes]
  | @node n s CL CR u left right ihL ihR =>
    let x : MovingSlotState σ := ⟨n + 1, .node s CL CR u left right, XL, XR⟩
    let step := MovingSlotData.step s CL CR u left right false
    let p := step.naturalPivot value XL XR
    let G := step.giantFormula value hf.1
      (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R
    have hI := movingSlotWeight_nonzero_integral value childBound pivotBound F extra
      (.node s CL CR u left right) t hT XL XR hw
    have hG : G.value (fun b => (a b : ℚ)) = (p : ℚ) :=
      step.giantFormula_value value hf.1 (MovingSlotReversal.naturalProduct_ne_zero value hvalue u)
        L R a XL XR hL hR hI.1
    have hGI : G.IntegralAt a := ⟨(p : ℤ), by simpa only [Int.cast_natCast] using hG⟩
    obtain ⟨Q, hQ, _, _⟩ := recursiveTransferWeight_nonzero_valid sys F cutoff (n + 1) x t hw
    have hQ' : ValidTransferNode sys x s left.frequency right.frequency Q := by
      simpa only [← hT.1, ← hT.2.1.root, ← hT.2.2.root] using hQ
    have hg := (movingNodeGuard_iff value childBound pivotBound s CL CR u left right hf.1
      XL XR L R a hL hR).mpr ⟨Q, hQ'⟩
    have hQp : Q / MovingSlotReversal.naturalProduct value u = p := by
      rw [← hQ.historyPivot_eq]
      simp only [historyPivot, sys, movingSlotSystem, MovingSlotState.leftProduct,
        MovingSlotState.rightProduct, x, ← hT.1, ← hT.2.1.root, ← hT.2.2.root,
        p, step, MovingSlotReversal.naturalPivot, MovingSlotData.step, movingGiantPivot, Nat.mul_one]
    have hnode := recursiveTransferWeight_node sys F cutoff n x t Q hQ
    have hnL : recursiveTransferWeight sys F cutoff n ⟨n, left, p, XL⟩ t.2.1 ≠ 0 := by
      intro hz
      apply hw
      rw [hnode]
      change (cutoff x t.1 _ _ : ℂ) * recursiveTransferWeight sys F cutoff n
        ⟨n, left, Q / _, XL⟩ t.2.1 * _ = 0
      rw [hQp, hz, mul_zero, zero_mul]
    have hnR : recursiveTransferWeight sys F cutoff n ⟨n, right, p, XR⟩ t.2.2 ≠ 0 := by
      intro hz
      apply hw
      rw [hnode]
      change _ * star (recursiveTransferWeight sys F cutoff n ⟨n, right, Q / _, XR⟩ t.2.2) = 0
      rw [hQp, hz, star_zero, mul_zero]
    have hl := ihL t.2.1 hT.2.1 hf.2.1 p XL G L hG hL hnL
    have hr := ihR t.2.2 hT.2.2 hf.2.2 p XR G R hG hR hnR
    intro f hmem
    rcases List.mem_cons.mp hmem with h | h
    · subst f
      exact ⟨hg, hGI⟩
    · rcases List.mem_append.mp h with h | h
      · exact hl f h
      · exact hr f h

end Ostmann

end OAI
