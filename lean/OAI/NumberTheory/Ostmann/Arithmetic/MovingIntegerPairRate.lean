import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelPairRates

namespace OAI

/-! # Uniform integer comparison for a literal moving-kernel slice -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical SchwartzMap

theorem moving_pair_integer_error_rate (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ J A : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J →
      A ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      4 * (movingKernelRootBudget n : ℝ) * A * Real.exp (-J) ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [weighted_giant_atom_rate C d,
    constant_mul_double_exp_le (4 * (movingKernelRootBudget n : ℝ)) 1
      (13 / 1000) (125 / 10000) (by positivity) (by norm_num) (by norm_num) (by norm_num)]
    with L hA hK
  intro J A hJ hbudget
  calc
    _ = 4 * (movingKernelRootBudget n : ℝ) * (A * Real.exp (-J)) := by ring
    _ ≤ 4 * (movingKernelRootBudget n : ℝ) * Real.exp (-Real.exp ((13 / 1000 : ℝ) * L)) :=
      mul_le_mul_of_nonneg_left (hA J A hJ hbudget) (by positivity)
    _ ≤ _ := by simpa only [one_mul, neg_mul] using hK

theorem moving_kernelPair_integer_rate {σ : Type*} (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
      (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (coord : Bool) (fixed : ℝ)
      (q a : ℕ), 0 < q → ∀ u v J : ℝ, u ≤ v →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → ∀ c : ℂ,
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      let W := pairedPolynomialFactors
        (movingSmoothPolynomialFactors value (T false) (movingCoordinateLeft coord fixed)
          (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
        (movingSmoothPolynomialFactors value (T true) (movingCoordinateLeft coord fixed)
          (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
      2 * ‖c‖ * smoothPolynomialBudget W ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖complexIntegerInterval q a u v J (fun y => c * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
        ∫ y in Set.Ioc u v, (c * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
          (integerLogDensity q J y : ℂ)‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [moving_pair_integer_error_rate n C d] with L hL
  intro value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    coord fixed q a hq u v J huv hJ c
  dsimp only
  intro hbudget
  apply (moving_kernelPair_integer_bound value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip hout coord fixed q a hq u v J huv c).trans
  convert hL J _ hJ hbudget using 1
  push_cast
  ring

end Ostmann

end OAI
