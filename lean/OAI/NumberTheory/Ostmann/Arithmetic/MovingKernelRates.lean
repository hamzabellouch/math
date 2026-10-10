import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelSlices

namespace OAI

/-! # Uniform prime and integer comparisons for either real giant slice -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

def movingKernelRootBudget (n : ℕ) : ℕ :=
  (2 ^ n - 1) * (3 * (7 * 2 ^ n)) + 5 * 2 ^ n + 1

/-- The threshold depends on the fixed depth and numerical budget, not the
small-prime data, residue class, or other real giant. -/
theorem PublishedProgressionInput.moving_kernel_prime_rate (P : PublishedProgressionInput)
    {σ : Type*} (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
      (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (coord : Bool) (fixed : ℝ)
      (Q q a : ℕ), 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v : ℝ, Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      ∀ c : ℂ,
      let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
      let W := movingSmoothPolynomialFactors value T
        (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
        ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
      2 * ‖c‖ * smoothPolynomialBudget W ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖complexPrimeInterval q a u v (fun y => c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
        ∫ y in Set.Ioc u v, (c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
          (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [P.root_integral_prime_rate C d (movingKernelRootBudget n)] with L hL
  intro value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    coord fixed Q q a hQ hq hqQ ha hlog u v hu huv hshort c
  dsimp only
  intro hbudget
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  let W := movingSmoothPolynomialFactors value T (movingCoordinateLeft coord fixed)
    (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
  let w := fun x => c * movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed x)
  obtain ⟨S, hS, hroots, hconst⟩ := movingRealKernel_slice_root_data value hvalue childBound pivotBound
    T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip coord fixed
  have hw (x : ℝ) : ‖w x‖ ≤ ‖c‖ := by
    change ‖c * _‖ ≤ ‖c‖
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (movingRealGateWeight_norm value T nodes X lo hi _) (norm_nonneg c)
  have hc (x y : ℝ) (hcode : rootCellCode S x = rootCellCode S y) : w x = w y :=
    congrArg (c * ·) (hconst x y hcode)
  have he (z : ℝ) : w z * smoothPolynomialWeight W z =
      c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G
        (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) := by
    rw [movingRealKernel_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout]
    dsimp only [w, W]
    ring
  have h := hL Q q a hQ hq hqQ ha hlog u v hu huv hshort _ W S
    (by unfold movingKernelRootBudget; omega) hroots w ‖c‖ (norm_nonneg _) hw hc hbudget
  simpa only [he] using h

theorem moving_kernel_integer_bound {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (coord : Bool) (fixed : ℝ)
    (q a : ℕ) (hq : 0 < q) (u v J : ℝ) (huv : u ≤ v) (c : ℂ) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    let W := movingSmoothPolynomialFactors value T
      (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
    ‖complexIntegerInterval q a u v J (fun y => c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G
        (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
      ∫ y in Set.Ioc u v, (c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G
        (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
        (integerLogDensity q J y : ℂ)‖ ≤
      4 * (movingKernelRootBudget n : ℝ) * ‖c‖ * smoothPolynomialBudget W * Real.exp (-J) := by
  dsimp only
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  let W := movingSmoothPolynomialFactors value T (movingCoordinateLeft coord fixed)
    (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
  let w := fun x => c * movingRealGateWeight value T nodes X lo hi (movingRealPair coord fixed x)
  obtain ⟨S, hS, hroots, hconst⟩ := movingRealKernel_slice_root_data value hvalue childBound pivotBound
    T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip coord fixed
  have hw (x : ℝ) : ‖w x‖ ≤ ‖c‖ := by
    change ‖c * _‖ ≤ ‖c‖
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (movingRealGateWeight_norm value T nodes X lo hi _) (norm_nonneg c)
  have hc (x y : ℝ) (hcode : rootCellCode S x = rootCellCode S y) : w x = w y :=
    congrArg (c * ·) (hconst x y hcode)
  have he (z : ℝ) : w z * smoothPolynomialWeight W z =
      c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G
        (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) := by
    rw [movingRealKernel_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout]
    dsimp only [w, W]
    ring
  have h := root_integral_integer_bound q a hq u v J huv W S hroots w ‖c‖ (norm_nonneg _) hw hc
  simp only [he] at h
  apply h.trans
  have hK : ((S.card + 1 : ℕ) : ℝ) ≤ movingKernelRootBudget n := by
    exact_mod_cast (show S.card + 1 ≤ movingKernelRootBudget n by unfold movingKernelRootBudget; omega)
  gcongr
  exact smoothPolynomialBudget_nonneg W

end Ostmann

end OAI
