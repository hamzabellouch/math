import OAI.NumberTheory.Ostmann.Arithmetic.MovingWindowedSpectators
import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticPrimeComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRootBudget

namespace OAI

/-! # Full moving coefficients on the common arithmetic and window cells -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

noncomputable def movingCompleteRootCuts {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR : ℕ)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) (X lo hi : ℝ) : Finset ℝ :=
  movingPrimeRootCuts value hvalue childBound pivotBound T hf XR F ∪
    movingWindowRootCuts value T Polynomial.X (Polynomial.C XR) X lo hi

theorem movingCompleteRootCuts_card {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR : ℕ)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) (X lo hi : ℝ) :
    (movingCompleteRootCuts value hvalue childBound pivotBound T hf XR F X lo hi).card ≤
      (2 ^ n - 1) * (3 * (7 * 2 ^ n)) + (∑ i, (F i).polynomial.derivative.natDegree) + 4 * 2 ^ n := by
  apply (Finset.card_union_le _ _).trans
  have hA := movingPrimeRootCuts_card value hvalue childBound pivotBound T hf XR F
  have hB := movingTopRootCuts_card value hvalue childBound pivotBound T hf XR
  have hW := movingWindowRootCuts_card value T Polynomial.X (Polynomial.C XR) X lo hi
    (by simp) (by simp)
  omega

/-- The only variable coefficient left after the full smooth factorization
is now a bounded, explicitly derived cell multiplier. -/
theorem PublishedProgressionInput.moving_windowed_prime_comparison
    (P : PublishedProgressionInput) {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) (g : ∀ i, ZMod (q i) → ℂ) (D : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (B : I → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hg : ∀ i ∈ S, ∀ z, ‖g i z‖ ≤ B i)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M Q : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hQ : 2 ≤ Q) (hq : 1 ≤ M) (hqQ : M ≤ Q) (ha : a.Coprime M)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    {k : ℕ} (W : Fin k → ClippedPolynomialFactor) :
    let roots := movingCompleteRootCuts value hvalue childBound pivotBound T hf XR W X lo hi
    let C := ‖movingDataWeight F E T‖ * ∏ i ∈ S, B i ^ (2 ^ n)
    ∃ (s : ℕ → ℝ) (N : ℕ) (d : ℕ → ℂ),
      Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ roots.card + 1 ∧ (∀ j, ‖d j‖ ≤ C) ∧
      ‖complexPrimeInterval M a u v (fun y =>
          (movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR *
            movingWindowedSpectatorWeight q value F E X lo hi g D S T ⌊Real.exp y⌋₊ XR) *
              smoothPolynomialWeight W (Real.exp y)) -
        ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
          d j * smoothPolynomialWeight W (Real.exp y) * (selectedPrimeLogDensity P Q M a y : ℂ)‖ ≤
        ∑ j ∈ Finset.range N,
          (‖d j‖ * smoothPolynomialBudget W *
            (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
              Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
            2 * C * smoothPolynomialBudget W * Real.exp (-(s j))) := by
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
  exact P.moving_supported_prime_comparison value hvalue childBound pivotBound T hf XR a M Q
    hM hQ hq hqQ ha u v hu huv hshort W roots hrootA hroots
    (fun XL => movingWindowedSpectatorWeight q value F E X lo hi g D S T XL XR) _ hC
    (fun XL _ => movingWindowedSpectatorWeight_norm q value F E X lo hi g D S B hB hg T XL XR)
    (fun XL YL hX hY hres hcode => movingWindowedSpectatorWeight_cells q value hvalue F E X lo hi
      g D S T hf XR M XL YL hMq roots hrootW
      (hX.integral value hvalue childBound pivotBound T XL XR)
      (hY.integral value hvalue childBound pivotBound T YL XR) hres hcode)

end Ostmann

end OAI
