import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierSupported
import OAI.NumberTheory.Ostmann.Construction.WordTransferGuardPolynomial

namespace OAI

/-! # Polynomial and residue tests for the actual moving-giant node -/

namespace Ostmann
open scoped Classical

def movingNodeWord (childBound pivotBound : ℕ) : WordTransferNode Bool where
  target := false
  left := [false]
  right := [true]
  childBound := childBound
  pivotBound := pivotBound

/-- The two word entries are the complete current child products, including
all regular factors. The reconstructed pivot here is the composite u*p. -/
noncomputable def movingNodeGuard (CL CR : ℕ) (s v w : ℤ) (hs : s ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) : WordTransferGuard Bool :=
  wordTransferGuard (movingNodeWord childBound pivotBound) s v w hs
    (fun b => if b then .product R (.external CR) else .product L (.external CL))

/-- Identification with the original validity predicate, before any
arithmetic restriction is removed. -/
theorem movingNodeGuard_iff {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (s : ℤ) (CL CR u : List σ)
    (left right : MovingSlotData σ n) (hs : s ≠ 0) (XL XR : ℕ)
    (L R : HistoryFormula Bool) (a : Bool → ℤ)
    (hL : L.value (fun b => (a b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (a b : ℚ)) = (XR : ℚ)) :
    (movingNodeGuard (MovingSlotReversal.naturalProduct value CL)
      (MovingSlotReversal.naturalProduct value CR) s left.frequency right.frequency hs
      (childBound (n + 1)) (pivotBound (n + 1)) L R).ValidAt a ↔
    ∃ P, ValidTransferNode (movingSlotSystem value childBound pivotBound)
      ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency P := by
  let d := movingNodeWord (childBound (n + 1)) (pivotBound (n + 1))
  let env : Bool → HistoryFormula Bool := fun b =>
    if b then .product R (.external (MovingSlotReversal.naturalProduct value CR))
    else .product L (.external (MovingSlotReversal.naturalProduct value CL))
  let x : Bool → ℕ := fun b => if b then XR * MovingSlotReversal.naturalProduct value CR
    else XL * MovingSlotReversal.naturalProduct value CL
  have henv (b : Bool) : (env b).value (fun j => (a j : ℚ)) = (x b : ℚ) := by
    cases b <;> simp only [env, x, Bool.false_eq_true, ite_false, ite_true,
      HistoryFormula.value_product, HistoryFormula.value_external, hL, hR,
      Nat.cast_mul, Int.cast_natCast]
  have hh := wordTransferGuard_iff d (.leaf []) (.leaf []) s left.frequency right.frequency hs env a x henv
  change (wordTransferGuard d s left.frequency right.frequency hs env).ValidAt a ↔ _
  rw [hh]
  apply exists_congr
  intro P
  have hpL : wordTransferLeft ((WordTransferTemplate.node d (.leaf []) (.leaf [])).state x) =
      XL * MovingSlotReversal.naturalProduct value CL := by simp [wordTransferLeft, WordTransferTemplate.state, d, movingNodeWord, x]
  have hpR : wordTransferRight ((WordTransferTemplate.node d (.leaf []) (.leaf [])).state x) =
      XR * MovingSlotReversal.naturalProduct value CR := by simp [wordTransferRight, WordTransferTemplate.state, d, movingNodeWord, x]
  constructor <;> intro h
  · exact ⟨h.root_ne_zero, by simpa only [wordTransferSystem, hpR, movingSlotSystem, MovingSlotState.rightProduct] using h.root_unit,
      by simpa only [wordTransferSystem, hpL, hpR, movingSlotSystem, MovingSlotState.leftProduct, MovingSlotState.rightProduct] using h.relation,
      h.pivot_pos, h.pivot_bound, h.left_bound, h.right_bound,
      by simpa only [wordTransferSystem, hpR, movingSlotSystem, MovingSlotState.rightProduct, wordTransferPivotBound, wordTransferChildBound, WordTransferTemplate.state, d, movingNodeWord, wordTransferRight, x, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Bool.true_eq, ite_true, Nat.mul_one] using h.range_gap, h.pivot_unit⟩
  · exact ⟨h.root_ne_zero, by simpa only [wordTransferSystem, hpR, movingSlotSystem, MovingSlotState.rightProduct] using h.root_unit,
      by simpa only [wordTransferSystem, hpL, hpR, movingSlotSystem, MovingSlotState.leftProduct, MovingSlotState.rightProduct] using h.relation,
      h.pivot_pos, h.pivot_bound, h.left_bound, h.right_bound,
      by simpa only [wordTransferSystem, hpR, movingSlotSystem, MovingSlotState.rightProduct, wordTransferPivotBound, wordTransferChildBound, WordTransferTemplate.state, d, movingNodeWord, wordTransferRight, x, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Bool.true_eq, ite_true, Nat.mul_one] using h.range_gap, h.pivot_unit⟩

/-- At an actual moving node all non-residue validity tests are exactly
three polynomial inequalities in the chosen top giant coordinate. -/
theorem movingNodeGuard_polynomials {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (s : ℤ) (CL CR u : List σ)
    (left right : MovingSlotData σ n) (hs : s ≠ 0) (XL XR : ℕ)
    (L R : HistoryFormula Bool) (a : Bool → ℤ) (coord : Bool) (z : ℤ)
    (hL : L.value (fun b => (Function.update a coord z b : ℚ)) = (XL : ℚ))
    (hR : R.value (fun b => (Function.update a coord z b : ℚ)) = (XR : ℚ)) :
    let g := movingNodeGuard (MovingSlotReversal.naturalProduct value CL)
      (MovingSlotReversal.naturalProduct value CR) s left.frequency right.frequency hs
      (childBound (n + 1)) (pivotBound (n + 1)) L R
    (g.residueAt (Function.update a coord z) ∧ g.frequencyBounds ∧
      ∀ j, 0 ≤ (g.polynomials a coord j).eval (z : ℝ)) ↔
    ∃ P, ValidTransferNode (movingSlotSystem value childBound pivotBound)
      ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency P := by
  let g := movingNodeGuard (MovingSlotReversal.naturalProduct value CL)
    (MovingSlotReversal.naturalProduct value CR) s left.frequency right.frequency hs
    (childBound (n + 1)) (pivotBound (n + 1)) L R
  have hh := movingNodeGuard_iff value childBound pivotBound s CL CR u left right hs XL XR L R
    (Function.update a coord z) hL hR
  have hp := (g.validAt_polynomials a coord z).symm
  have hu : @Function.update Bool (fun _ => ℤ) instDecidableEqBool a coord z =
      @Function.update Bool (fun _ => ℤ) (fun x y => Classical.propDecidable (x = y)) a coord z := by
    funext b
    by_cases hb : b = coord <;> simp [Function.update, hb]
  rw [← hu] at hp
  exact hp.trans hh

end Ostmann

end OAI
