import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterResidueComparison
import OAI.NumberTheory.Ostmann.Construction.GiantHaarIntegral

namespace OAI

/-! # The original outer-prior comparisons as corrected Haar integrals -/

namespace Ostmann
universe u
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_outer_prime_haar_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      (∀ a ∈ reducedResidues q, ∀ b ∈ reducedResidues q,
      2 * (‖c a b‖ * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      letI : NeZero q := ⟨by omega⟩
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖(∑ b ∈ reducedResidues q, ∑ a ∈ reducedResidues q,
          complexPrimeInterval q b r s (fun y => complexPrimeInterval q a u v (fun x =>
            c a b * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)))) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            correctedPrimePairAverage P Q q c x y / ((x : ℂ) * (y : ℂ)))‖ ≤
        Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_outer_prime_residue_sum_rate n C d,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q hQ hq hqQ hlog u v r s hu huv hshort hr hrs hrshort hqlog c hbudget
  have hL := hL σ
  have : NeZero q := ⟨by omega⟩
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let H := fun x y => movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
  have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D
    hB hD hφ hlip hout diagonal V hV Q q hQ hq hqQ hlog u v r s hu huv hshort hr hrs hrshort hqlog c hbudget
  dsimp only at h ⊢
  have hmeas : Measurable (Function.uncurry H) := by
    have hh := measurable_exp_pair_mul
      (movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal)
      (measurable_movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal) (1 : ℂ)
    simpa only [one_mul] using hh
  have hnorm (x y : ℝ) : ‖H x y‖ ≤
      (((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 *
        (giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2))) := by
    dsimp only [H, movingOuterKernel]
    rw [norm_mul]
    exact mul_le_mul (movingRealKernelPair_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ _ _)
      (giantOuterWeight_norm φ Jleft Jright B D hB hD hφ hlip hout diagonal _ _) (norm_nonneg _) (by positivity)
  have hu1 : 1 ≤ u := (Real.one_le_exp (by positivity)).trans hu
  have hr1 : 1 ≤ r := (Real.one_le_exp (by positivity)).trans hr
  rw [primeGiantMeasure_pair_haar_integral P Q q u v r s hu1 hr1 H hmeas _ hnorm c] at h
  exact h

theorem PublishedProgressionInput.moving_outer_mixed_haar_rate (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (Jleft Jright B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      (∀ a ∈ Finset.range q, ∀ b ∈ reducedResidues q,
      2 * (‖c a b‖ * giantOuterScalar diagonal) * movingOuterVariationBudget ψ V lo hi n B D diagonal ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      letI : NeZero q := ⟨by omega⟩
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖(∑ b ∈ reducedResidues q, ∑ a ∈ Finset.range q,
          complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J (fun x =>
            c a b * movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)))) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q q c y / (y : ℂ))‖ ≤
        Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_outer_mixed_residue_sum_rate n C d,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout
    diagonal V hV Q q hQ hq hqQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog c hbudget
  have hL := hL σ
  have : NeZero q := ⟨by omega⟩
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let H := fun x y => movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal (Real.exp x) (Real.exp y)
  have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G Jleft Jright B D
    hB hD hφ hlip hout diagonal V hV Q q hQ hq hqQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog c hbudget
  dsimp only at h ⊢
  have hmeas : Measurable (Function.uncurry H) := by
    have hh := measurable_exp_pair_mul
      (movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright diagonal)
      (measurable_movingOuterKernel value T nodes ψ X lo hi hlo hhi φ G Jleft Jright B D hB hD hφ hlip hout diagonal) (1 : ℂ)
    simpa only [one_mul] using hh
  have hnorm (x y : ℝ) : ‖H x y‖ ≤
      (((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 *
        (giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 * (if diagonal then 1 + Real.exp 2 else 2))) := by
    dsimp only [H, movingOuterKernel]
    rw [norm_mul]
    exact mul_le_mul (movingRealKernelPair_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ _ _)
      (giantOuterWeight_norm φ Jleft Jright B D hB hD hφ hlip hout diagonal _ _) (norm_nonneg _) (by positivity)
  have hr1 : 1 ≤ r := (Real.one_le_exp (by positivity)).trans hr
  rw [mixedGiantMeasure_pair_haar_integral P Q q u v r s J hr1 H hmeas _ hnorm c] at h
  exact h

end Ostmann

end OAI
