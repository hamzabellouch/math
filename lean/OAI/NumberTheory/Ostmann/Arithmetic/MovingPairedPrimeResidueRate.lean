import OAI.NumberTheory.Ostmann.Arithmetic.MovingJointPairRate
import OAI.NumberTheory.Ostmann.Arithmetic.PrimePairResidues
import OAI.NumberTheory.Ostmann.Construction.GiantResidueSumBound

namespace OAI

/-! # Simultaneous giant idealization summed over every unit residue pair -/

namespace Ostmann
universe u v
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_paired_prime_residue_sum_rate_uniform (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      (∀ a ∈ reducedResidues q, ∀ b ∈ reducedResidues q,
      2 * ‖c a b‖ * (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖(∑ b ∈ reducedResidues q, ∑ a ∈ reducedResidues q,
          complexPrimeInterval q b r s (fun y => complexPrimeInterval q a u v (fun x =>
            c a b * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)))) -
        (∑ b ∈ reducedResidues q, ∑ a ∈ reducedResidues q,
          ∫ x, ∫ y, c a b * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
            ∂primeGiantMeasure P Q q b r s ∂primeGiantMeasure P Q q a u v)‖ ≤
        Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_joint_kernelPair_prime_rate_uniform n C d,
    giant_residue_sum_error_rate (Real.exp 1 + 2) (by positivity)] with L hL hR
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout V hV
    Q q hQ hq hqQ hlog u v r s hu huv hshort hr hrs hrshort hqlog c hbudget
  dsimp only
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let err := Real.exp (-Real.exp ((125 / 10000 : ℝ) * L))
  have hm (b : ℕ) : reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) ≤ Real.exp 1 :=
    (reciprocalPrimeInterval_le_exp q b r s).trans (Real.exp_le_exp.mpr (by linarith))
  have hpoint (b : ℕ) (hb : b ∈ reducedResidues q) (a : ℕ) (ha : a ∈ reducedResidues q) :
      ‖complexPrimeInterval q b r s (fun y => complexPrimeInterval q a u v (fun x =>
          c a b * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y))) -
        ∫ x, ∫ y, c a b * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
          ∂primeGiantMeasure P Q q b r s ∂primeGiantMeasure P Q q a u v‖ ≤ err * (Real.exp 1 + 2) := by
    exact (hL σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout V hV
      Q q a b hQ hq hqQ (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hlog
      u v r s hu huv hshort hr hrs hrshort (c a b) (hbudget a ha b hb)).trans
      (mul_le_mul_of_nonneg_left (by linarith [hm b]) (Real.exp_pos _).le)
  apply (finite_pair_comparison (reducedResidues q) (reducedResidues q) _ _ _ hpoint).trans
  have hc : ((reducedResidues q).card : ℝ) ≤ q := Nat.cast_le.mpr (reducedResidues_card_le q)
  calc
    _ ≤ (q : ℝ) * q * (err * (Real.exp 1 + 2)) := by gcongr
    _ = (q : ℝ) ^ 2 * (Real.exp 1 + 2) * err := by ring
    _ ≤ _ := hR q (by omega) hqlog

theorem PublishedProgressionInput.moving_paired_prime_residue_sum_rate (P : PublishedProgressionInput)
    {σ : Type u} (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      (∀ a ∈ reducedResidues q, ∀ b ∈ reducedResidues q,
      2 * ‖c a b‖ * (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖(∑ b ∈ reducedResidues q, ∑ a ∈ reducedResidues q,
          complexPrimeInterval q b r s (fun y => complexPrimeInterval q a u v (fun x =>
            c a b * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)))) -
        (∑ b ∈ reducedResidues q, ∑ a ∈ reducedResidues q,
          ∫ x, ∫ y, c a b * movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
            ∂primeGiantMeasure P Q q b r s ∂primeGiantMeasure P Q q a u v)‖ ≤
        Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_paired_prime_residue_sum_rate_uniform n C d] with L hL
  exact hL σ

end Ostmann

end OAI
