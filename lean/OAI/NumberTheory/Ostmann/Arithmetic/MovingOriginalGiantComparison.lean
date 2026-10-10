import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairedPrimeResidueRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairedMixedResidueRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalPairedFactor
import OAI.NumberTheory.Ostmann.Construction.GiantHaarIntegral
import OAI.NumberTheory.Ostmann.Construction.GiantModulusCutoff

namespace OAI

/-! # Joint giant idealization for the actual two-history coefficients -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators Classical ComplexConjugate SchwartzMap

theorem PublishedProgressionInput.moving_original_paired_prime_comparison
    (P : PublishedProgressionInput) {σ I : Type*} (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n)
      (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (t : Bool → FrequencyTree ℤ n)
      (_hT : ∀ b, (T b).Follows (t b))
      (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
      (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
      (g : ∀ i, ZMod (p i) → ℂ) (_hg : ∀ i, g i 0 = 0)
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ) (S : Finset I)
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ),
      (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q M : ℕ, 2 ≤ Q → ∀ hM0 : 1 ≤ M, M ≤ Q →
      (∀ b, movingTopPeriod value hvalue childBound pivotBound (T b) (hf b) ∣ M) →
      (∀ b, ∀ i ∈ S, (p i : ℤ) * movingSpectatorDenominator value (T b) ∣ (M : ℤ)) →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      Real.log (M : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      letI : NeZero M := ⟨Nat.ne_of_gt (Nat.zero_lt_one.trans_le hM0)⟩
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      let c := fun a b => movingResidueCoefficient p value (F false) (E false) g (Dq false) S
          (T false) (nodes false) a b *
        conj (movingResidueCoefficient p value (F true) (E true) g (Dq true) S (T true) (nodes true) a b)
      (∀ a ∈ reducedResidues M, ∀ b ∈ reducedResidues M,
        2 * ‖c a b‖ * (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
          Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      ‖complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
          movingOriginalGiantWeight p value childBound pivotBound (F false) (E false) g (Dq false) S
            ψ X lo hi φ G (T false) (t false) ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ *
          conj (movingOriginalGiantWeight p value childBound pivotBound (F true) (E true) g (Dq true) S
            ψ X lo hi φ G (T true) (t true) ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))) -
        ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) *
            correctedPrimePairAverage P Q M c x y / ((x : ℂ) * (y : ℂ))‖ ≤
          Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_paired_prime_residue_sum_rate (σ := σ) n C d,
    eventually_gt_atTop (0 : ℝ)] with L hL hL0
  intro value hvalue childBound pivotBound T hf t hT F E g hg Dq S ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip hout V hV Q M hQ hM0 hMQ hM hMq hlog hMlog
    u v r s hu huv hshort hr hrs hrshort
  dsimp only
  intro hbudget
  have : NeZero M := ⟨by omega⟩
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let c := fun a b => movingResidueCoefficient p value (F false) (E false) g (Dq false) S
      (T false) (nodes false) a b *
    conj (movingResidueCoefficient p value (F true) (E true) g (Dq true) S (T true) (nodes true) a b)
  let H := fun x y => movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
  have hfactor := prime_pair_residue_factorization M (by omega) u v r s
    (fun z hz _ => giant_interval_gt_modulus L hL0 M (by omega) hMlog u v hu z hz)
    (fun z hz _ => giant_interval_gt_modulus L hL0 M (by omega) hMlog r s hr z hz)
    (fun x y => movingOriginalGiantWeight p value childBound pivotBound (F false) (E false) g (Dq false) S
      ψ X lo hi φ G (T false) (t false) x y *
      conj (movingOriginalGiantWeight p value childBound pivotBound (F true) (E true) g (Dq true) S
      ψ X lo hi φ G (T true) (t true) x y)) c H (by
      intro x _ hx y _ hy a _ b _ hxa hyb
      have hx0 : (0 : ℝ) < x := by exact_mod_cast hx.pos
      have hy0 : (0 : ℝ) < y := by exact_mod_cast hy.pos
      dsimp only [H]
      rw [Real.exp_log hx0, Real.exp_log hy0]
      exact movingOriginalGiantWeight_paired_factor p value hvalue childBound pivotBound F E g hg Dq S
        ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf x y a b M hM hMq
        (Int.natCast_modEq_iff.mpr hxa) (Int.natCast_modEq_iff.mpr hyb))
  have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    V hV Q M hQ hM0 hMQ hlog u v r s hu huv hshort hr hrs hrshort hMlog c hbudget
  dsimp only at h
  have hbase := measurable_movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
  have hmeas : Measurable (Function.uncurry H) := by
    have hh := measurable_exp_pair_mul
      (movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G) hbase (1 : ℂ)
    simpa only [one_mul] using hh
  have hnorm (x y : ℝ) : ‖H x y‖ ≤
      ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 :=
    movingRealKernelPair_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ _ _
  have hu1 : 1 ≤ u := (Real.one_le_exp (by positivity)).trans hu
  have hr1 : 1 ≤ r := (Real.one_le_exp (by positivity)).trans hr
  rw [primeGiantMeasure_pair_haar_integral P Q M u v r s hu1 hr1 H hmeas _ hnorm c] at h
  rw [hfactor]
  exact h

theorem PublishedProgressionInput.moving_original_paired_mixed_comparison
    (P : PublishedProgressionInput) {σ I : Type*} (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n)
      (hf : ∀ b, (T b).Frequencies (· ≠ 0)) (t : Bool → FrequencyTree ℤ n)
      (_hT : ∀ b, (T b).Follows (t b))
      (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
      (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
      (g : ∀ i, ZMod (p i) → ℂ) (_hg : ∀ i, g i 0 = 0)
      (Dq : Bool → ∀ i, (ZMod (p i))ˣ) (S : Finset I)
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ),
      (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q M : ℕ, 2 ≤ Q → ∀ hM0 : 1 ≤ M, M ≤ Q →
      (∀ b, movingTopPeriod value hvalue childBound pivotBound (T b) (hf b) ∣ M) →
      (∀ b, ∀ i ∈ S, (p i : ℤ) * movingSpectatorDenominator value (T b) ∣ (M : ℤ)) →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      Real.log (M : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s J : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ J → u ≤ v → v ≤ u + 1 → v ≤ J + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      letI : NeZero M := ⟨Nat.ne_of_gt (Nat.zero_lt_one.trans_le hM0)⟩
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      let c := fun a b => movingResidueCoefficient p value (F false) (E false) g (Dq false) S
          (T false) (nodes false) a b *
        conj (movingResidueCoefficient p value (F true) (E true) g (Dq true) S (T true) (nodes true) a b)
      (∀ a ∈ Finset.range M, ∀ b ∈ reducedResidues M,
        2 * ‖c a b‖ * (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
          Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L))) →
      ‖complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
          movingOriginalGiantWeight p value childBound pivotBound (F false) (E false) g (Dq false) S
            ψ X lo hi φ G (T false) (t false) ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊ *
          conj (movingOriginalGiantWeight p value childBound pivotBound (F true) (E true) g (Dq true) S
            ψ X lo hi φ G (T true) (t true) ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊))) -
        ∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) *
            (Real.exp (x - J) : ℂ) * correctedMixedPairAverage P Q M c y / (y : ℂ)‖ ≤
          Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_paired_mixed_residue_sum_rate (σ := σ) n C d,
    eventually_gt_atTop (0 : ℝ)] with L hL hL0
  intro value hvalue childBound pivotBound T hf t hT F E g hg Dq S ψ X lo hi hlo hhi
    φ G B D hB hD hφ hlip hout V hV Q M hQ hM0 hMQ hM hMq hlog hMlog
    u v r s J hJ huv hshort hvJ hr hrs hrshort
  dsimp only
  intro hbudget
  have : NeZero M := ⟨by omega⟩
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let c := fun a b => movingResidueCoefficient p value (F false) (E false) g (Dq false) S
      (T false) (nodes false) a b *
    conj (movingResidueCoefficient p value (F true) (E true) g (Dq true) S (T true) (nodes true) a b)
  let H := fun x y => movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
  have hfactor := mixed_pair_residue_factorization M (by omega) u v r s J
    (fun z hz _ => giant_interval_gt_modulus L hL0 M (by omega) hMlog r s hr z hz)
    (fun x y => movingOriginalGiantWeight p value childBound pivotBound (F false) (E false) g (Dq false) S
      ψ X lo hi φ G (T false) (t false) x y *
      conj (movingOriginalGiantWeight p value childBound pivotBound (F true) (E true) g (Dq true) S
      ψ X lo hi φ G (T true) (t true) x y)) c H (by
      intro x hx y _ hy a _ b _ hxa hyb
      have hx0 : (0 : ℝ) < x :=
        (Real.exp_pos u).trans (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hx).1)
      have hy0 : (0 : ℝ) < y := by exact_mod_cast hy.pos
      dsimp only [H]
      rw [Real.exp_log hx0, Real.exp_log hy0]
      exact movingOriginalGiantWeight_paired_factor p value hvalue childBound pivotBound F E g hg Dq S
        ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf x y a b M hM hMq
        (Int.natCast_modEq_iff.mpr hxa) (Int.natCast_modEq_iff.mpr hyb))
  have h := hL value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    V hV Q M hQ hM0 hMQ hlog u v r s J hJ huv hshort hvJ hr hrs hrshort hMlog c hbudget
  dsimp only at h
  have hbase := measurable_movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
  have hmeas : Measurable (Function.uncurry H) := by
    have hh := measurable_exp_pair_mul
      (movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G) hbase (1 : ℂ)
    simpa only [one_mul] using hh
  have hnorm (x y : ℝ) : ‖H x y‖ ≤
      ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) ^ 2 :=
    movingRealKernelPair_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ _ _
  have hr1 : 1 ≤ r := (Real.one_le_exp (by positivity)).trans hr
  rw [mixedGiantMeasure_pair_haar_integral P Q M u v r s J hr1 H hmeas _ hnorm c] at h
  rw [hfactor]
  exact h

end Ostmann

end OAI
