import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterKernelRates
import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelTransport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterIntegerRate

namespace OAI

/-! # Joint transport with the literal outer priors and diagonal reciprocal -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

noncomputable def movingOuterVariationBudget (ψ : 𝓢(ℝ, ℂ)) (V lo hi : ℝ) (n : ℕ)
    (B D : ℝ) (diagonal : Bool) : ℝ :=
  (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 *
    ((2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2))

theorem PublishedProgressionInput.moving_outer_joint_prime_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n)
      (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
      (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ),
      (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q a b : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q → b.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 → ∀ c : ℂ,
      2 * (‖c‖ * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖complexPrimeInterval q b r s (fun y => complexPrimeInterval q a u v (fun x =>
          c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y))) -
        ∫ x, ∫ y, c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
          ∂primeGiantMeasure P Q q b r s ∂primeGiantMeasure P Q q a u v‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) *
          (reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) + 2) := by
  filter_upwards [P.moving_outer_kernel_prime_rate n C d, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q a b hQ hq hqQ ha hb hlog u v r s hu huv hshort hr hrs hrshort c hbudget
  have hL := hL σ
  dsimp only
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let H := fun x y => c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
  let μ := primeGiantMeasure P Q q a u v
  let ν := primeGiantMeasure P Q q b r s
  let err := Real.exp (-Real.exp ((125 / 10000 : ℝ) * L))
  have hu1 : 1 ≤ u := (Real.one_le_exp (by positivity)).trans hu
  have hr1 : 1 ≤ r := (Real.one_le_exp (by positivity)).trans hr
  have : IsFiniteMeasure μ := finite_primeGiantMeasure P Q q a u v (by linarith)
  have : IsFiniteMeasure ν := finite_primeGiantMeasure P Q q b r s (by linarith)
  have hscalar : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hsmall (coord : Bool) (fixed : ℝ) :
      2 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget
        (movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
          ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal) ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) :=
    (mul_le_mul_of_nonneg_left (movingOuterPolynomialFactors_budget value T _ _ ψ X lo hi V hlo hhi hV
      φ G Jleft Jright B D hB hD hφ hlip diagonal) (by positivity)).trans hbudget
  have hleft (y : ℝ) : ‖complexPrimeInterval q a u v (fun x => H x y) - ∫ x, H x y ∂μ‖ ≤ err := by
    have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
      diagonal false (Real.exp y) Q q a hQ hq hqQ ha hlog u v hu huv hshort c (hsmall false (Real.exp y))
    rw [primeGiantMeasure_integral P Q q a u v (by linarith)]
    simpa only [H, err, movingRealPair, Bool.false_eq_true, ite_false, topGiantReal, ite_true] using h
  have hright (x : ℝ) : ‖complexPrimeInterval q b r s (H x) - ∫ y, H x y ∂ν‖ ≤ err := by
    have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
      diagonal true (Real.exp x) Q q b hQ hq hqQ hb hlog r s hr hrs hrshort c (hsmall true (Real.exp x))
    rw [primeGiantMeasure_integral P Q q b r s (by linarith)]
    simpa only [H, err, movingRealPair, Bool.false_eq_true, ite_false, topGiantReal, ite_true] using h
  have hmeas := measurable_exp_pair_mul
    (movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal)
    (measurable_movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal) c
  have hnorm (x y : ℝ) : ‖H x y‖ ≤ ‖c‖ *
      (((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 *
        (giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2))) := by
    dsimp only [H, movingOuterKernel]
    rw [norm_mul, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
    exact mul_le_mul (movingRealKernelPair_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ _ _)
      (giantOuterWeight_norm φ Jleft Jright B D hB hD hφ hlip hout diagonal _ _) (norm_nonneg _) (by positivity)
  have hpair := prime_pair_integral_transport q a b u v r s μ ν H hmeas _ hnorm err err hleft hright
  have hmass : μ.real Set.univ ≤ 2 := primeGiantMeasure_mass_le_two P Q q a hq u v hu1 huv hshort
  apply hpair.trans
  have hmul := mul_le_mul_of_nonneg_left hmass (Real.exp_pos (-Real.exp ((125 / 10000 : ℝ) * L))).le
  dsimp only [err] at *
  nlinarith

theorem PublishedProgressionInput.moving_outer_joint_mixed_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n)
      (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ))
      (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
      (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ),
      (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q a b : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q → b.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 → ∀ c : ℂ,
      2 * (‖c‖ * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J (fun x =>
          c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y))) -
        ∫ x, ∫ y, c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
          ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) *
          (reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) + Real.exp (v - J)) := by
  filter_upwards [P.moving_outer_kernel_prime_rate n C d, moving_outer_kernel_integer_rate n C d,
    eventually_ge_atTop (0 : ℝ)] with L hL hI hL0
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q a b hQ hq hqQ hb hlog u v r s J hJ huv hshort hr hrs hrshort c hbudget
  have hL := hL σ
  have hI := hI σ
  dsimp only
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let H := fun x y => c * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
  let μ := integerGiantMeasure q J u v
  let ν := primeGiantMeasure P Q q b r s
  let err := Real.exp (-Real.exp ((125 / 10000 : ℝ) * L))
  have hr1 : 1 ≤ r := (Real.one_le_exp (by positivity)).trans hr
  have : IsFiniteMeasure μ := finite_integerGiantMeasure q J u v
  have : IsFiniteMeasure ν := finite_primeGiantMeasure P Q q b r s (by linarith)
  have hscalar : 0 ≤ giantOuterScalar diagonal := by cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hsmall (coord : Bool) (fixed : ℝ) :
      2 * (‖c‖ * giantOuterScalar diagonal) * smoothPolynomialBudget
        (movingOuterPolynomialFactors value T (movingCoordinateLeft coord fixed) (movingCoordinateRight coord fixed)
          ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip diagonal) ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) :=
    (mul_le_mul_of_nonneg_left (movingOuterPolynomialFactors_budget value T _ _ ψ X lo hi V hlo hhi hV
      φ G Jleft Jright B D hB hD hφ hlip diagonal) (by positivity)).trans hbudget
  have hleft (y : ℝ) : ‖complexIntegerInterval q a u v J (fun x => H x y) - ∫ x, H x y ∂μ‖ ≤ err := by
    have h := hI value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
      diagonal false (Real.exp y) q a (by omega) u v J huv hJ c (hsmall false (Real.exp y))
    rw [integerGiantMeasure_integral q J u v]
    simpa only [H, err, movingRealPair, Bool.false_eq_true, ite_false, topGiantReal, ite_true] using h
  have hright (x : ℝ) : ‖complexPrimeInterval q b r s (H x) - ∫ y, H x y ∂ν‖ ≤ err := by
    have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
      diagonal true (Real.exp x) Q q b hQ hq hqQ hb hlog r s hr hrs hrshort c (hsmall true (Real.exp x))
    rw [primeGiantMeasure_integral P Q q b r s (by linarith)]
    simpa only [H, err, movingRealPair, Bool.false_eq_true, ite_false, topGiantReal, ite_true] using h
  have hmeas := measurable_exp_pair_mul
    (movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal)
    (measurable_movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal) c
  have hnorm (x y : ℝ) : ‖H x y‖ ≤ ‖c‖ *
      (((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 *
        (giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2))) := by
    dsimp only [H, movingOuterKernel]
    rw [norm_mul, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
    exact mul_le_mul (movingRealKernelPair_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ _ _)
      (giantOuterWeight_norm φ Jleft Jright B D hB hD hφ hlip hout diagonal _ _) (norm_nonneg _) (by positivity)
  have hpair := mixed_pair_integral_transport q a b u v r s J μ ν H hmeas _ hnorm err err hleft hright
  have hmass : μ.real Set.univ ≤ Real.exp (v - J) :=
    integerGiantMeasure_mass_le q (by omega) J u v huv hshort
  apply hpair.trans
  have hmul := mul_le_mul_of_nonneg_left hmass (Real.exp_pos (-Real.exp ((125 / 10000 : ℝ) * L))).le
  dsimp only [err] at *
  nlinarith

end Ostmann

end OAI
