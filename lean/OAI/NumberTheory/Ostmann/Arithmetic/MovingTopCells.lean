import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportCells

namespace OAI

/-! # Actual top-giant residue cells for the moving arithmetic support -/

namespace Ostmann
open scoped Classical

theorem MovingSlotData.formulaNodes_frequencies {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (L R : HistoryFormula Bool) :
    ∀ f ∈ T.formulaNodes value hvalue childBound pivotBound hf L R,
      f.guard.right ≠ 0 ∧ f.guard.root ≠ 0 := by
  induction T generalizing L R with
  | leaf s regular => simp [formulaNodes]
  | node s CL CR u left right ihL ihR =>
    intro f hmem
    rcases List.mem_cons.mp hmem with h | h
    · subst f
      exact ⟨hf.2.2.root, hf.1⟩
    · rcases List.mem_append.mp h with h | h
      · exact ihL hf.2.1 _ _ f h
      · exact ihR hf.2.2 _ _ f h

def topGiantInput (XL XR : ℕ) (b : Bool) : ℤ := if b then XR else XL

/-- The period depends only on the fixed small data and frequencies. -/
noncomputable def movingTopPeriod {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) : ℕ :=
  movingArithmeticPeriod (T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true))

theorem movingTopPeriod_pos {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) :
    0 < movingTopPeriod value hvalue childBound pivotBound T hf :=
  movingArithmeticPeriod_pos _ (T.formulaNodes_frequencies value hvalue childBound pivotBound hf _ _)

noncomputable def movingTopRootCuts {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR : ℕ) : Finset ℝ :=
  movingArithmeticRootCuts
    (T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true))
    (topGiantInput 0 XR) false

/-- With the other giant fixed, the original arithmetic support is constant
on the constructed residue and root cells. This also covers empty depth. -/
theorem moving_top_support_cells {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL YL XR : ℕ)
    (hres : (XL : ℤ) ≡ (YL : ℤ) [ZMOD movingTopPeriod value hvalue childBound pivotBound T hf])
    (hcell : rootCellCode (movingTopRootCuts value hvalue childBound pivotBound T hf XR) (XL : ℝ) =
      rootCellCode (movingTopRootCuts value hvalue childBound pivotBound T hf XR) (YL : ℝ)) :
    T.ArithmeticSupport value childBound pivotBound XL XR ↔
      T.ArithmeticSupport value childBound pivotBound YL XR := by
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  let a := topGiantInput 0 XR
  have hin (Z : ℕ) : movingGiantUpdate a false (Z : ℤ) = topGiantInput Z XR := by
    funext b
    cases b <;> simp [movingGiantUpdate, Function.update, a, topGiantInput]
  have hmod : ∀ i, movingGiantUpdate a false (XL : ℤ) i ≡
      movingGiantUpdate a false (YL : ℤ) i [ZMOD movingArithmeticPeriod nodes] := by
    intro i
    rw [hin, hin]
    cases i
    · exact hres
    · exact Int.ModEq.refl _
  have hh := movingFormulaNodes_holds_invariant nodes a false XL YL hmod hcell
  rw [hin, hin] at hh
  have hleft := T.formulaNodes_iff value hvalue childBound pivotBound hf XL XR
    (.prime false) (.prime true) (topGiantInput XL XR)
    (by simp [topGiantInput]) (by simp [topGiantInput])
  have hright := T.formulaNodes_iff value hvalue childBound pivotBound hf YL XR
    (.prime false) (.prime true) (topGiantInput YL XR)
    (by simp [topGiantInput]) (by simp [topGiantInput])
  exact hleft.symm.trans (hh.trans hright)

end Ostmann

end OAI
