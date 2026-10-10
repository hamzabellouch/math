import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticCells

namespace OAI

/-! # Prime idealization with the literal moving arithmetic support retained -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

noncomputable def movingPrimeRootCuts {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR : ℕ)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) : Finset ℝ :=
  movingTopRootCuts value hvalue childBound pivotBound T hf XR ∪
    polynomialRootCuts (fun i => (F i).polynomial.derivative)

theorem movingPrimeRootCuts_card {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR : ℕ)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) :
    (movingPrimeRootCuts value hvalue childBound pivotBound T hf XR F).card ≤
      (movingTopRootCuts value hvalue childBound pivotBound T hf XR).card +
        ∑ i, (F i).polynomial.derivative.natDegree := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (polynomialRootCuts_card (fun i => (F i).polynomial.derivative)) _)

/-- The arithmetic gate in this statement is the original recursive gate.
Its idealization is derived on an explicitly bounded number of root cells. -/
theorem PublishedProgressionInput.moving_arithmetic_prime_comparison
    (P : PublishedProgressionInput) {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M Q : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hQ : 2 ≤ Q) (hq : 1 ≤ M) (hqQ : M ≤ Q) (ha : a.Coprime M)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) :
    ∃ (s : ℕ → ℝ) (N : ℕ) (d : ℕ → ℂ),
      Monotone s ∧ s 0 = u ∧ s N = v ∧
      N ≤ (movingTopRootCuts value hvalue childBound pivotBound T hf XR).card +
        (∑ i, (F i).polynomial.derivative.natDegree) + 1 ∧ (∀ j, ‖d j‖ ≤ 1) ∧
      ‖complexPrimeInterval M a u v
          (fun y => movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
            smoothPolynomialWeight F (Real.exp y)) -
        ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
          d j * smoothPolynomialWeight F (Real.exp y) *
            (selectedPrimeLogDensity P Q M a y : ℂ)‖ ≤
        ∑ j ∈ Finset.range N,
          (‖d j‖ * smoothPolynomialBudget F *
            (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
              Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
            2 * smoothPolynomialBudget F * Real.exp (-(s j))) := by
  let S := movingPrimeRootCuts value hvalue childBound pivotBound T hf XR F
  have hS : movingTopRootCuts value hvalue childBound pivotBound T hf XR ⊆ S :=
    Finset.subset_union_left
  have hroot : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S := by
    intro i r hr
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Multiset.mem_toFinset.mpr hr⟩)
  obtain ⟨s, N, d, hs, hs0, hsN, hN, hd, herr⟩ := P.root_cell_prime_comparison hQ hq hqQ ha
    u v hu huv hshort F S hroot
    (movingArithmeticCellValue value hvalue childBound pivotBound T hf XR a M S) 1
    (by norm_num) (movingArithmeticCellValue_norm value hvalue childBound pivotBound T hf XR a M S)
  refine ⟨s, N, d, hs, hs0, hsN, hN.trans ?_, hd, ?_⟩
  · exact Nat.add_le_add_right (movingPrimeRootCuts_card value hvalue childBound pivotBound T hf XR F) 1
  · rw [movingArithmeticPrimeInterval_cells value hvalue childBound pivotBound T hf XR a M S hM hS]
    simpa only [mul_one] using herr

end Ostmann

end OAI
