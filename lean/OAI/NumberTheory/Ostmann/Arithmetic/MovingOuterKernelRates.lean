import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterSlices

namespace OAI

/-! # Prime slice comparison with both outer priors and the diagonal ratio -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem PublishedProgressionInput.moving_outer_kernel_prime_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n)
      (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
      (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
      (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal coord : Bool) (fixed : ℝ)
      (Q q a : ℕ), 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v : ℝ, Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 → ∀ c : ℂ,
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
        ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
      2 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget W ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖complexPrimeInterval q a u v (fun y => c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G
          Jleft Jright diagonal (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
        ∫ y in Set.Ioc u v, (c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
          (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤ Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [P.root_integral_prime_rate C d (2 * movingKernelRootBudget n)] with L hL
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal coord fixed Q q a hQ hq hqQ ha hlog u v hu huv hshort c
  dsimp only
  intro hbudget
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
    ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
  let gate := fun x => movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed x) *
    conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed x))
  let w := fun x => c * (giantOuterScalar diagonal : ℂ) * gate x
  have hscalar : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  obtain ⟨S, hS, hroots, hconst⟩ := movingOuterKernel_slice_roots value hvalue childBound pivotBound
    T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal coord fixed
  have hw (x : ℝ) : ‖w x‖ ≤ ‖c‖ * giantOuterScalar diagonal := by
    have hg : ‖gate x‖ ≤ 1 := by
      dsimp only [gate]
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_mul (movingRealGateWeight_norm value (T false) (nodes false) X lo hi _)
        (movingRealGateWeight_norm value (T true) (nodes true) X lo hi _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    dsimp only [w]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hscalar]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) hscalar) hg
  have hc (x y : ℝ) (hcode : rootCellCode S x = rootCellCode S y) : w x = w y :=
    congrArg (c * (giantOuterScalar diagonal : ℂ) * ·) (hconst x y hcode)
  have he (z : ℝ) : w z * smoothPolynomialWeight W z =
      c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
        (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) := by
    rw [movingOuterKernel_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G
      Jleft Jright B D hB hD hφ hlip hout diagonal coord fixed z]
    dsimp only [w, W, gate, movingOuterPolynomialFactors]
    ring
  have h := hL Q q a hQ hq hqQ ha hlog u v hu huv hshort _ W S hS hroots w
    (‖c‖ * giantOuterScalar diagonal) (mul_nonneg (norm_nonneg _) hscalar) hw hc hbudget
  simpa only [he] using h

theorem moving_outer_kernel_integer_bound {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal coord : Bool) (fixed : ℝ)
    (q a : ℕ) (hq : 0 < q) (u v J : ℝ) (huv : u ≤ v) (c : ℂ) :
    let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
    let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
      ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
    ‖complexIntegerInterval q a u v J (fun y => c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G
        Jleft Jright diagonal (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
      ∫ y in Set.Ioc u v, (c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
        (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
        (integerLogDensity q J y : ℂ)‖ ≤
      4 * ((2 * movingKernelRootBudget n : ℕ) : ℝ) * (‖c‖ * giantOuterScalar diagonal) *
        smoothPolynomialBudget W * Real.exp (-J) := by
  dsimp only
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
    ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
  let gate := fun x => movingRealGateWeight value (T false) (nodes false) X lo hi (movingRealPair coord fixed x) *
    conj (movingRealGateWeight value (T true) (nodes true) X lo hi (movingRealPair coord fixed x))
  let w := fun x => c * (giantOuterScalar diagonal : ℂ) * gate x
  have hscalar : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  obtain ⟨S, hS, hroots, hconst⟩ := movingOuterKernel_slice_roots value hvalue childBound pivotBound
    T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal coord fixed
  have hw (x : ℝ) : ‖w x‖ ≤ ‖c‖ * giantOuterScalar diagonal := by
    have hg : ‖gate x‖ ≤ 1 := by
      dsimp only [gate]
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_mul (movingRealGateWeight_norm value (T false) (nodes false) X lo hi _)
        (movingRealGateWeight_norm value (T true) (nodes true) X lo hi _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    dsimp only [w]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hscalar]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) hscalar) hg
  have hc (x y : ℝ) (hcode : rootCellCode S x = rootCellCode S y) : w x = w y :=
    congrArg (c * (giantOuterScalar diagonal : ℂ) * ·) (hconst x y hcode)
  have he (z : ℝ) : w z * smoothPolynomialWeight W z =
      c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
        (movingRealPair coord fixed z false) (movingRealPair coord fixed z true) := by
    rw [movingOuterKernel_slice_polynomial value T nodes ψ X lo hi hlo hhi φ G
      Jleft Jright B D hB hD hφ hlip hout diagonal coord fixed z]
    dsimp only [w, W, gate, movingOuterPolynomialFactors]
    ring
  have h := root_integral_integer_bound q a hq u v J huv W S hroots w
    (‖c‖ * giantOuterScalar diagonal) (mul_nonneg (norm_nonneg _) hscalar) hw hc
  simp only [he] at h
  apply h.trans
  have hK : ((S.card + 1 : ℕ) : ℝ) ≤ ((2 * movingKernelRootBudget n : ℕ) : ℝ) := by exact_mod_cast hS
  have hn : 0 ≤ 4 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget W * Real.exp (-J) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (norm_nonneg _) hscalar))
      (smoothPolynomialBudget_nonneg W)) (Real.exp_pos _).le
  calc
    _ = ((S.card + 1 : ℕ) : ℝ) *
        (4 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget W * Real.exp (-J)) := by ring
    _ ≤ ((2 * movingKernelRootBudget n : ℕ) : ℝ) *
        (4 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget W * Real.exp (-J)) :=
      mul_le_mul_of_nonneg_right hK hn
    _ = _ := by ring

end Ostmann

end OAI
