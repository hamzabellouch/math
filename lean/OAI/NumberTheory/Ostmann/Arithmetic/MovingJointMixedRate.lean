import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelTransport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingIntegerKernelRate

namespace OAI

/-! # Joint integer–prime idealization of the literal moving kernel -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

/-- The original integer and prime sums are replaced jointly. The Page factors remain
inside their actual measures and the threshold is uniform in the small data. -/
theorem PublishedProgressionInput.moving_joint_mixed_rate (P : PublishedProgressionInput)
    {σ : Type*} (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ), T.Frequencies (fun s => |(s : ℝ)| ≤ V) →
      ∀ Q q a b : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q → b.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      ∀ c : ℂ,
      2 * ‖c‖ * (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
      ‖complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J (fun x =>
          c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y))) -
        ∫ x, ∫ y, c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
          ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) *
          (reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) + Real.exp (v - J)) := by
  filter_upwards [P.moving_kernel_prime_rate (σ := σ) n C d,
    moving_kernel_integer_rate (σ := σ) n C d, eventually_ge_atTop (0 : ℝ)] with L hL hI hL0
  intro value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout V hV
    Q q a b hQ hq hqQ hb hlog u v r s J hJ huv hshort hr hrs hrshort c hbudget
  dsimp only
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  let H := fun x y => c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
  let μ := integerGiantMeasure q J u v
  let ν := primeGiantMeasure P Q q b r s
  let err := Real.exp (-Real.exp ((125 / 10000 : ℝ) * L))
  have hr1 : 1 ≤ r := (Real.one_le_exp (by positivity)).trans hr
  have : IsFiniteMeasure μ := finite_integerGiantMeasure q J u v
  have : IsFiniteMeasure ν := finite_primeGiantMeasure P Q q b r s (by linarith)
  have hsmall (coord : Bool) (fixed : ℝ) :
      2 * ‖c‖ * smoothPolynomialBudget (movingSmoothPolynomialFactors value T
        (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi
        φ G B D hB hD hφ hlip) ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    exact (mul_le_mul_of_nonneg_left
      (movingSmoothPolynomialFactors_budget value T _ _ ψ X lo hi V hlo hhi hV
        φ G B D hB hD hφ hlip) (by positivity)).trans hbudget
  have hleft (y : ℝ) : ‖complexIntegerInterval q a u v J (fun x => H x y) - ∫ x, H x y ∂μ‖ ≤ err := by
    have h := hI value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      false (Real.exp y) q a (by omega) u v J huv hJ c (hsmall false (Real.exp y))
    rw [integerGiantMeasure_integral q J u v]
    simpa only [H, err, movingRealPair, Bool.false_eq_true, ite_false, topGiantReal, ite_true] using h
  have hright (x : ℝ) : ‖complexPrimeInterval q b r s (H x) - ∫ y, H x y ∂ν‖ ≤ err := by
    have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      true (Real.exp x) Q q b hQ hq hqQ hb hlog r s hr hrs hrshort c (hsmall true (Real.exp x))
    rw [primeGiantMeasure_integral P Q q b r s (by linarith)]
    simpa only [H, err, movingRealPair, Bool.false_eq_true, ite_false, topGiantReal, ite_true] using h
  have hpair := moving_kernel_mixed_transport value T nodes ψ X lo hi hlo hhi φ G B D
    hB hD hφ hlip hout c q a b u v r s J μ ν err err hleft hright
  have hmass : μ.real Set.univ ≤ Real.exp (v - J) :=
    integerGiantMeasure_mass_le q (by omega) J u v huv hshort
  apply hpair.trans
  have hmul := mul_le_mul_of_nonneg_left hmass (Real.exp_pos (-Real.exp ((125 / 10000 : ℝ) * L))).le
  dsimp only [err] at *
  nlinarith

end Ostmann

end OAI
