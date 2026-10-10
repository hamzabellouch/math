import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelTransport

namespace OAI

/-! # Joint prime-giant idealization of the literal moving kernel -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

/-- Both original prime sums are replaced jointly. The Page factors remain
inside their actual measures and the threshold is uniform in the small data. -/
theorem PublishedProgressionInput.moving_joint_prime_rate (P : PublishedProgressionInput)
    {σ : Type*} (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ), T.Frequencies (fun s => |(s : ℝ)| ≤ V) →
      ∀ Q q a b : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q → b.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      ∀ c : ℂ,
      2 * ‖c‖ * (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
      ‖complexPrimeInterval q b r s (fun y => complexPrimeInterval q a u v (fun x =>
          c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y))) -
        ∫ x, ∫ y, c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
          ∂primeGiantMeasure P Q q b r s ∂primeGiantMeasure P Q q a u v‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) *
          (reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) + 2) := by
  filter_upwards [P.moving_kernel_prime_rate (σ := σ) n C d, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout V hV
    Q q a b hQ hq hqQ ha hb hlog u v r s hu huv hshort hr hrs hrshort c hbudget
  dsimp only
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  let H := fun x y => c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
  let μ := primeGiantMeasure P Q q a u v
  let ν := primeGiantMeasure P Q q b r s
  let err := Real.exp (-Real.exp ((125 / 10000 : ℝ) * L))
  have hu1 : 1 ≤ u := (Real.one_le_exp (by positivity)).trans hu
  have hr1 : 1 ≤ r := (Real.one_le_exp (by positivity)).trans hr
  have : IsFiniteMeasure μ := finite_primeGiantMeasure P Q q a u v (by linarith)
  have : IsFiniteMeasure ν := finite_primeGiantMeasure P Q q b r s (by linarith)
  have hsmall (coord : Bool) (fixed : ℝ) :
      2 * ‖c‖ * smoothPolynomialBudget (movingSmoothPolynomialFactors value T
        (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed) ψ X lo hi hlo hhi
        φ G B D hB hD hφ hlip) ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    exact (mul_le_mul_of_nonneg_left
      (movingSmoothPolynomialFactors_budget value T _ _ ψ X lo hi V hlo hhi hV
        φ G B D hB hD hφ hlip) (by positivity)).trans hbudget
  have hleft (y : ℝ) : ‖complexPrimeInterval q a u v (fun x => H x y) - ∫ x, H x y ∂μ‖ ≤ err := by
    have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      false (Real.exp y) Q q a hQ hq hqQ ha hlog u v hu huv hshort c (hsmall false (Real.exp y))
    rw [primeGiantMeasure_integral P Q q a u v (by linarith)]
    simpa only [H, err, movingRealPair, Bool.false_eq_true, ite_false, topGiantReal, ite_true] using h
  have hright (x : ℝ) : ‖complexPrimeInterval q b r s (H x) - ∫ y, H x y ∂ν‖ ≤ err := by
    have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      true (Real.exp x) Q q b hQ hq hqQ hb hlog r s hr hrs hrshort c (hsmall true (Real.exp x))
    rw [primeGiantMeasure_integral P Q q b r s (by linarith)]
    simpa only [H, err, movingRealPair, Bool.false_eq_true, ite_false, topGiantReal, ite_true] using h
  have hpair := moving_kernel_pair_transport value T nodes ψ X lo hi hlo hhi φ G B D
    hB hD hφ hlip hout c q a b u v r s μ ν err err hleft hright
  have hmass : μ.real Set.univ ≤ 2 := primeGiantMeasure_mass_le_two P Q q a hq u v hu1 huv hshort
  apply hpair.trans
  have hmul := mul_le_mul_of_nonneg_left hmass (Real.exp_pos (-Real.exp ((125 / 10000 : ℝ) * L))).le
  dsimp only [err] at *
  nlinarith

end Ostmann

end OAI
