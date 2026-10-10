import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompleteCells
import OAI.NumberTheory.Ostmann.Arithmetic.MovingIntegerCells

namespace OAI

/-! # The full moving coefficient under the external integer law -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

theorem moving_windowed_integer_comparison {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hM0 : 0 < M) (u v G : ℝ) (huv : u ≤ v)
    {k : ℕ} (W : Fin k → ClippedPolynomialFactor) :
    let roots := movingCompleteRootCuts value hvalue childBound pivotBound T hf XR W X lo hi
    let C := ‖movingDataWeight F E T‖ * ∏ i ∈ S, B i ^ (2 ^ n)
    ∃ (s : ℕ → ℝ) (N : ℕ) (d : ℕ → ℂ),
      Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ roots.card + 1 ∧ (∀ j, ‖d j‖ ≤ C) ∧
      ‖complexIntegerInterval M a u v G (fun y =>
          (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
            movingWindowedSpectatorWeight q value F E X lo hi g D S T ⌊Real.exp y⌋₊ XR) *
              smoothPolynomialWeight W (Real.exp y)) -
        ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
          d j * smoothPolynomialWeight W (Real.exp y) * (integerLogDensity M G y : ℂ)‖ ≤
        4 * ((roots.card + 1 : ℕ) : ℝ) * C * smoothPolynomialBudget W * Real.exp (-G) := by
  let roots := movingCompleteRootCuts value hvalue childBound pivotBound T hf XR W X lo hi
  have hrootA : movingTopRootCuts value hvalue childBound pivotBound T hf XR ⊆ roots := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hrootW : movingWindowRootCuts value T Polynomial.X (Polynomial.C XR) X lo hi ⊆ roots :=
    Finset.subset_union_right
  have hroots : ∀ i r, r ∈ (W i).polynomial.derivative.roots → r ∈ roots := by
    intro i r hr
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Multiset.mem_toFinset.mpr hr⟩))
  have hC : 0 ≤ ‖movingDataWeight F E T‖ * ∏ i ∈ S, B i ^ (2 ^ n) := by
    apply mul_nonneg (norm_nonneg _)
    apply Finset.prod_nonneg
    intro i hi
    exact pow_nonneg (hB i hi) _
  exact moving_supported_integer_comparison value hvalue childBound pivotBound T hf XR a M
    hM hM0 u v G huv W roots hrootA hroots
    (fun XL => movingWindowedSpectatorWeight q value F E X lo hi g D S T XL XR) _ hC
    (fun XL _ => movingWindowedSpectatorWeight_norm q value F E X lo hi g D S B hB hg T XL XR)
    (fun XL YL hX hY hres hcode => movingWindowedSpectatorWeight_cells q value hvalue F E X lo hi
      g D S T hf XR M XL YL hMq roots hrootW
      (hX.integral value hvalue childBound pivotBound T XL XR)
      (hY.integral value hvalue childBound pivotBound T YL XR) hres hcode)

end Ostmann

end OAI
