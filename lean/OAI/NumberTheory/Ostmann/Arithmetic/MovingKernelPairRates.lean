import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelPair

namespace OAI

/-! # Uniform prime and integer comparisons for either real giant slice -/

namespace Ostmann
universe u v
open Filter MeasureTheory
open scoped Classical BigOperators ComplexConjugate SchwartzMap

/-- The threshold depends on the fixed depth and numerical budget, not the
small-prime data, residue class, or other real giant. -/
theorem PublishedProgressionInput.moving_kernelPair_prime_rate_uniform (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
      (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (coord : Bool) (fixed : ℝ)
      (Q q a : ℕ), 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v : ℝ, Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      ∀ c : ℂ,
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      let W := pairedPolynomialFactors
        (movingSmoothPolynomialFactors value (T false) (movingCoordinateLeft coord fixed)
          (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
        (movingSmoothPolynomialFactors value (T true) (movingCoordinateLeft coord fixed)
          (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
      2 * ‖c‖ * smoothPolynomialBudget W ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖complexPrimeInterval q a u v (fun y => c * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
        ∫ y in Set.Ioc u v, (c * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
          (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [P.root_integral_prime_rate C d (2 * movingKernelRootBudget n)] with L hL
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    coord fixed Q q a hQ hq hqQ ha hlog u v hu huv hshort c
  dsimp only
  intro hbudget
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let W := pairedPolynomialFactors
    (movingSmoothPolynomialFactors value (T false) (movingCoordinateLeft coord fixed)
      (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
    (movingSmoothPolynomialFactors value (T true) (movingCoordinateLeft coord fixed)
      (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
  let gate := fun x => movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed x) *
    conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed x))
  let w := fun x => c * gate x
  obtain ⟨S, hS, hroots, hconst⟩ := movingRealKernelPair_slice_root_data value hvalue childBound pivotBound
    T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip coord fixed
  have hw (x : ℝ) : ‖w x‖ ≤ ‖c‖ := by
    change ‖c * _‖ ≤ ‖c‖
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (show ‖gate x‖ ≤ 1 from by
        dsimp only [gate]
        rw [norm_mul, Complex.norm_conj]
        exact (mul_le_mul
          (movingRealGateWeight_norm value (T false) (nodes false) X lo hi _)
          (movingRealGateWeight_norm value (T true) (nodes true) X lo hi _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)) (norm_nonneg c)
  have hc (x y : ℝ) (hcode : rootCellCode S x = rootCellCode S y) : w x = w y :=
    congrArg (c * ·) (hconst x y hcode)
  have he (z : ℝ) : w z * smoothPolynomialWeight W z =
      c * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
        (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) := by
    rw [movingRealKernelPair_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout]
    dsimp only [w, W, gate]
    ring
  have h := hL Q q a hQ hq hqQ ha hlog u v hu huv hshort _ W S
    hS hroots w ‖c‖ (norm_nonneg _) hw hc hbudget
  simpa only [he] using h

theorem PublishedProgressionInput.moving_kernelPair_prime_rate (P : PublishedProgressionInput)
    {σ : Type u} (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
      (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (coord : Bool) (fixed : ℝ)
      (Q q a : ℕ), 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v : ℝ, Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      ∀ c : ℂ,
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      let W := pairedPolynomialFactors
        (movingSmoothPolynomialFactors value (T false) (movingCoordinateLeft coord fixed)
          (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
        (movingSmoothPolynomialFactors value (T true) (movingCoordinateLeft coord fixed)
          (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
      2 * ‖c‖ * smoothPolynomialBudget W ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖complexPrimeInterval q a u v (fun y => c * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
        ∫ y in Set.Ioc u v, (c * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
          (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [P.moving_kernelPair_prime_rate_uniform n C d] with L hL
  exact hL σ

theorem moving_kernelPair_integer_bound {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (coord : Bool) (fixed : ℝ)
    (q a : ℕ) (hq : 0 < q) (u v J : ℝ) (huv : u ≤ v) (c : ℂ) :
    let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
    let W := pairedPolynomialFactors
      (movingSmoothPolynomialFactors value (T false) (movingCoordinateLeft coord fixed)
        (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
      (movingSmoothPolynomialFactors value (T true) (movingCoordinateLeft coord fixed)
        (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
    ‖complexIntegerInterval q a u v J (fun y => c * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
        (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
      ∫ y in Set.Ioc u v, (c * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
        (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
        (integerLogDensity q J y : ℂ)‖ ≤
      4 * ((2 * movingKernelRootBudget n : ℕ) : ℝ) * ‖c‖ * smoothPolynomialBudget W * Real.exp (-J) := by
  dsimp only
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let W := pairedPolynomialFactors
    (movingSmoothPolynomialFactors value (T false) (movingCoordinateLeft coord fixed)
      (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
    (movingSmoothPolynomialFactors value (T true) (movingCoordinateLeft coord fixed)
      (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
  let gate := fun x => movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed x) *
    conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed x))
  let w := fun x => c * gate x
  obtain ⟨S, hS, hroots, hconst⟩ := movingRealKernelPair_slice_root_data value hvalue childBound pivotBound
    T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip coord fixed
  have hw (x : ℝ) : ‖w x‖ ≤ ‖c‖ := by
    change ‖c * _‖ ≤ ‖c‖
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (show ‖gate x‖ ≤ 1 from by
        dsimp only [gate]
        rw [norm_mul, Complex.norm_conj]
        exact (mul_le_mul
          (movingRealGateWeight_norm value (T false) (nodes false) X lo hi _)
          (movingRealGateWeight_norm value (T true) (nodes true) X lo hi _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)) (norm_nonneg c)
  have hc (x y : ℝ) (hcode : rootCellCode S x = rootCellCode S y) : w x = w y :=
    congrArg (c * ·) (hconst x y hcode)
  have he (z : ℝ) : w z * smoothPolynomialWeight W z =
      c * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
        (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) := by
    rw [movingRealKernelPair_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout]
    dsimp only [w, W, gate]
    ring
  have h := root_integral_integer_bound q a hq u v J huv W S hroots w ‖c‖ (norm_nonneg _) hw hc
  simp only [he] at h
  apply h.trans
  have hK : ((S.card + 1 : ℕ) : ℝ) ≤ 2 * movingKernelRootBudget n := by
    exact_mod_cast hS
  gcongr
  exact smoothPolynomialBudget_nonneg W

end Ostmann

end OAI
