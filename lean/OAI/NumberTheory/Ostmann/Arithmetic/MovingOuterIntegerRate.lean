import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterKernelRates
import OAI.NumberTheory.Ostmann.Arithmetic.MovingIntegerPairRate

namespace OAI

/-! # Integer slice rate with the original giant cutoff factors -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped Classical SchwartzMap

theorem moving_outer_kernel_integer_rate (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
      (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal coord : Bool) (fixed : ℝ)
      (q a : ℕ), 0 < q → ∀ u v J : ℝ, u ≤ v →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → ∀ c : ℂ,
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      let W := movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed)
        (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal
      2 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget W ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖complexIntegerInterval q a u v J (fun y => c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) -
        ∫ y in Set.Ioc u v, (c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal
          (movingRealPair coord fixed (Real.exp y) false) (movingRealPair coord fixed (Real.exp y) true)) *
          (integerLogDensity q J y : ℂ)‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [moving_pair_integer_error_rate n C d] with L hL
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal coord fixed q a hq u v J huv hJ c
  dsimp only
  intro hbudget
  apply (moving_outer_kernel_integer_bound value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi
    φ G Jleft Jright B D hB hD hφ hlip hout diagonal coord fixed q a hq u v J huv c).trans
  convert hL J _ hJ hbudget using 1
  push_cast
  ring

end Ostmann

end OAI
