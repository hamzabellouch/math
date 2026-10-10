import OAI.NumberTheory.Ostmann.Arithmetic.MovingRealWindows
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRootBudget

namespace OAI

/-! # Residue-independent cells for either real giant coordinate -/

namespace Ostmann
open scoped Classical BigOperators

def movingRealPair (coord : Bool) (fixed z : ℝ) : Bool → ℝ :=
  if coord then topGiantReal fixed z else topGiantReal z fixed

theorem movingRealPair_update (coord : Bool) (fixed z : ℝ) :
    movingRealPair coord fixed z = movingRealUpdate (topGiantReal fixed fixed) coord z := by
  funext b
  cases coord <;> cases b <;> simp [movingRealPair, movingRealUpdate, topGiantReal]

noncomputable def movingCoordinateLeft (coord : Bool) (fixed : ℝ) : Polynomial ℝ :=
  if coord then Polynomial.C fixed else Polynomial.X

noncomputable def movingCoordinateRight (coord : Bool) (fixed : ℝ) : Polynomial ℝ :=
  if coord then Polynomial.X else Polynomial.C fixed

theorem movingCoordinate_eval (coord : Bool) (fixed z : ℝ) :
    (movingCoordinateLeft coord fixed).eval z = movingRealPair coord fixed z false ∧
    (movingCoordinateRight coord fixed).eval z = movingRealPair coord fixed z true := by
  cases coord <;> simp [movingCoordinateLeft, movingCoordinateRight, movingRealPair, topGiantReal]

noncomputable def movingRealGateWeight {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ)
    (x : Bool → ℝ) : ℂ :=
  movingArchimedeanFlag nodes x * movingRealWindowFlag value T X lo hi (x false) (x true)

theorem movingRealGateWeight_norm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ)
    (x : Bool → ℝ) : ‖movingRealGateWeight value T nodes X lo hi x‖ ≤ 1 := by
  unfold movingRealGateWeight movingArchimedeanFlag movingRealWindowFlag
  split_ifs <;> norm_num

noncomputable def movingRealRootCuts {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ)
    (coord : Bool) (fixed : ℝ) : Finset ℝ :=
  movingArchimedeanRootCuts nodes (topGiantReal fixed fixed) coord ∪
    movingWindowRootCuts value T (movingCoordinateLeft coord fixed)
      (movingCoordinateRight coord fixed) X lo hi

theorem movingArchimedeanRootCuts_card (nodes : List MovingFormulaNode)
    (a : Bool → ℝ) (coord : Bool) :
    (movingArchimedeanRootCuts nodes a coord).card ≤
      ∑ f ∈ nodes.toFinset, ∑ j : Fin 3, (f.guard.realPolynomials a coord j).natDegree := by
  apply (Finset.card_biUnion_le).trans
  exact Finset.sum_le_sum fun f _ => polynomialRootCuts_card (f.guard.realPolynomials a coord)

theorem movingRealRootCuts_card {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (X lo hi : ℝ)
    (coord : Bool) (fixed : ℝ) :
    (movingRealRootCuts value T
      (T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true))
      X lo hi coord fixed).card ≤ (2 ^ n - 1) * (3 * (7 * 2 ^ n)) + 4 * 2 ^ n := by
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  have hcost := T.formulaNodes_cost value hvalue childBound pivotBound hf
    (.prime false) (.prime true) 1 (by rfl) (by rfl)
  have ha : (movingArchimedeanRootCuts nodes (topGiantReal fixed fixed) coord).card ≤
      (2 ^ n - 1) * (3 * (7 * 2 ^ n)) := by
    apply (movingArchimedeanRootCuts_card nodes _ coord).trans
    calc
      _ ≤ ∑ _f ∈ nodes.toFinset, 3 * (7 * 2 ^ n) := by
        apply Finset.sum_le_sum
        intro f hf
        calc
          _ ≤ ∑ _j : Fin 3, 7 * 2 ^ n := by
            apply Finset.sum_le_sum
            intro j _
            apply (f.guard.realPolynomials_degree _ _ j).trans
            simpa only [Nat.reduceAdd, mul_comm] using hcost f (List.mem_toFinset.mp hf)
          _ = _ := by simp
      _ = nodes.toFinset.card * (3 * (7 * 2 ^ n)) := by simp
      _ ≤ nodes.length * (3 * (7 * 2 ^ n)) :=
        Nat.mul_le_mul_right _ (List.toFinset_card_le nodes)
      _ = _ := by rw [MovingSlotData.formulaNodes_length]
  have hw := movingWindowRootCuts_card value T (movingCoordinateLeft coord fixed)
    (movingCoordinateRight coord fixed) X lo hi
    (by cases coord <;> simp [movingCoordinateLeft])
    (by cases coord <;> simp [movingCoordinateRight])
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add ha hw)

/-- These cells depend on the real fixed giant, never on residue representatives. -/
theorem movingRealGateWeight_rootCell {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ)
    (coord : Bool) (fixed x y : ℝ) (S : Finset ℝ)
    (hS : movingRealRootCuts value T nodes X lo hi coord fixed ⊆ S)
    (hcode : rootCellCode S x = rootCellCode S y) :
    movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed x) =
      movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed y) := by
  have ha := movingArchimedeanGate_rootCell nodes (topGiantReal fixed fixed) coord S
    (fun r hr => hS (Finset.mem_union_left _ hr)) x y hcode
  rw [← movingRealPair_update, ← movingRealPair_update] at ha
  have hw := movingPolynomialWindows_of_rootCell value T (movingCoordinateLeft coord fixed)
    (movingCoordinateRight coord fixed) X lo hi x y S
    (fun r hr => hS (Finset.mem_union_right _ hr)) hcode
  have hev (z : ℝ) (i : TreeLeafIndex n) :
      (movingLeafNormalizedPolynomial value T (movingCoordinateLeft coord fixed)
        (movingCoordinateRight coord fixed) X i).eval z =
      T.realLeafModuli value (movingRealPair coord fixed z false)
        (movingRealPair coord fixed z true) i / X := by
    rw [movingLeafNormalizedPolynomial_eval, T.leafPolynomials_real]
    rw [(movingCoordinate_eval coord fixed z).1, (movingCoordinate_eval coord fixed z).2]
  simp only [hev] at hw
  unfold movingRealGateWeight movingArchimedeanFlag movingRealWindowFlag
  simp only [ha, hw]

theorem movingSpectatorResidue_norm {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (g : ∀ i, ZMod (q i) → ℂ)
    (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (B : I → ℝ)
    (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : MovingSlotData σ n) (a b : ℤ) :
    ‖movingSpectatorResidue q value g D S T a b‖ ≤ ∏ i ∈ S, B i ^ (2 ^ n) := by
  unfold movingSpectatorResidue
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun i hi => movingSignedSpectator_norm value (g i) (D i) (B i) (hB i hi) (hg i hi) T a b)

end Ostmann

end OAI
