import OAI.NumberTheory.Ostmann.Arithmetic.MovingJointMixedRate
import OAI.NumberTheory.Ostmann.Arithmetic.PrimePairResidues
import OAI.NumberTheory.Ostmann.Construction.GiantResidueSumBound

namespace OAI

/-! # Simultaneous giant idealization summed over every integer–unit residue pair -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_mixed_residue_sum_rate (P : PublishedProgressionInput)
    {σ : Type*} (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ), T.Frequencies (fun s => |(s : ℝ)| ≤ V) →
      ∀ Q q : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      (∀ a ∈ Finset.range q, ∀ b ∈ reducedResidues q,
      2 * ‖c a b‖ * (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
      ‖(∑ b ∈ reducedResidues q, ∑ a ∈ Finset.range q,
          complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J (fun x =>
            c a b * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)))) -
        (∑ b ∈ reducedResidues q, ∑ a ∈ Finset.range q,
          ∫ x, ∫ y, c a b * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
            ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v)‖ ≤
        Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_joint_mixed_rate (σ := σ) n C d,
    giant_residue_sum_error_rate (2 * Real.exp 1) (by positivity)] with L hL hR
  intro value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout V hV
    Q q hQ hq hqQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hqlog c hbudget
  dsimp only
  let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
  let err := Real.exp (-Real.exp ((125 / 10000 : ℝ) * L))
  have hm (b : ℕ) : reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) ≤ Real.exp 1 :=
    (reciprocalPrimeInterval_le_exp q b r s).trans (Real.exp_le_exp.mpr (by linarith))
  have hpoint (b : ℕ) (hb : b ∈ reducedResidues q) (a : ℕ) (ha : a ∈ Finset.range q) :
      ‖complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J (fun x =>
          c a b * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y))) -
        ∫ x, ∫ y, c a b * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
          ∂primeGiantMeasure P Q q b r s ∂integerGiantMeasure q J u v‖ ≤ err * (2 * Real.exp 1) := by
    exact (hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout V hV
      Q q a b hQ hq hqQ (Finset.mem_filter.mp hb).2 hlog
      u v r s J hJ huv hshort hr hrs hrshort (c a b) (hbudget a ha b hb)).trans
      (mul_le_mul_of_nonneg_left (by
        have hmass : Real.exp (v - J) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
        linarith [hm b]) (Real.exp_pos _).le)
  apply (finite_pair_comparison (reducedResidues q) (Finset.range q) _ _ _ hpoint).trans
  have hc : ((reducedResidues q).card : ℝ) ≤ q := Nat.cast_le.mpr (reducedResidues_card_le q)
  calc
    _ ≤ (q : ℝ) * q * (err * (2 * Real.exp 1)) := by
      simp only [Finset.card_range]
      gcongr
    _ = (q : ℝ) ^ 2 * (2 * Real.exp 1) * err := by ring
    _ ≤ _ := hR q (by omega) hqlog

end Ostmann

end OAI
