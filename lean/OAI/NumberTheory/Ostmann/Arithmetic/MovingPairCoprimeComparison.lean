import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairHaarComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPairNormBudget
import OAI.NumberTheory.Ostmann.Construction.GiantCoprimeRates
import OAI.NumberTheory.Ostmann.Construction.GiantModulusCutoff

namespace OAI

/-! # Coprime top giants under the literal prime and integer laws -/

namespace Ostmann
universe u v
open Filter MeasureTheory
open scoped BigOperators Classical SchwartzMap

theorem PublishedProgressionInput.moving_pair_coprime_prime_haar_rate_uniform (P : PublishedProgressionInput)
    (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (σ : Type u) (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * A * (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
          if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then
            c (⌊Real.exp x⌋₊ % q) (⌊Real.exp y⌋₊ % q) *
              movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊
          else 0)) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) *
            correctedPrimePairAverage P Q q c x y / ((x : ℂ) * (y : ℂ)))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_pair_prime_haar_rate_uniform n C d,
    prime_pair_coprime_removal_rate C d, eventually_gt_atTop (0 : ℝ)] with L hL hR hL0
  intro σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
    V hV Q q hQ hq hqQ hlog u v r s hu huv hshort hr hrs hrshort hqlog c A hA0 hA hbudget
  have : NeZero q := ⟨by omega⟩
  dsimp only
  let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
  let H := fun x y => movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
  let F0 := fun x y : ℕ => c (x % q) (y % q) *
    movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G x y
  let K := A * (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2
  have hv : 0 ≤ (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := sq_nonneg _
  have hK0 : 0 ≤ K := mul_nonneg hA0 hv
  have hK : K ≤ Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) := by
    calc
      K ≤ 2 * K := by linarith
      _ = 2 * A * (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 := by ring
      _ ≤ _ := hbudget
  have hnorm (x y : ℕ) : ‖F0 x y‖ ≤ K := by
    dsimp only [F0]
    rw [norm_mul]
    exact mul_le_mul (hA _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)))
      (movingRealKernelPair_norm_variation value T nodes ψ X lo hi V hlo hhi hV φ G B D
        hB hD hφ hlip hout x y) (norm_nonneg _) hA0
  have hremove := hR u v r s K hu hrshort hK0 hK F0 (fun x _ y _ => hnorm x y)
  have h := hL σ value hvalue childBound pivotBound T hf ψ X lo hi hlo hhi φ G B D
    hB hD hφ hlip hout V hV Q q hQ hq hqQ hlog u v r s hu huv hshort hr hrs hrshort hqlog c (by
      intro a ha b hb
      have ha0 := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have hb0 := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hA a ha0 b hb0) (by norm_num)) hv).trans hbudget)
  have hfactor := prime_pair_residue_factorization q (by omega) u v r s
    (fun z hz _ => giant_interval_gt_modulus L hL0 q (by omega) hqlog u v hu z hz)
    (fun z hz _ => giant_interval_gt_modulus L hL0 q (by omega) hqlog r s hr z hz)
    F0 c H (by
      intro x _ hx y _ hy a ha b hb hxa hyb
      have hx0 : (0 : ℝ) < x := by exact_mod_cast hx.pos
      have hy0 : (0 : ℝ) < y := by exact_mod_cast hy.pos
      have ha0 : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      have hb0 : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      have hxa' : x % q = a := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt ha0] using hxa
      have hyb' : y % q = b := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt hb0] using hyb
      dsimp only [F0, H]
      rw [hxa', hyb', Real.exp_log hx0, Real.exp_log hy0])
  dsimp only at h
  rw [← hfactor] at h
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hremove h)

theorem PublishedProgressionInput.moving_pair_coprime_prime_haar_rate (P : PublishedProgressionInput)
    {σ : Type u} (n : ℕ) (C : ℝ) (d : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
      (childBound pivotBound : ℕ → ℕ) (T : Bool → MovingSlotData σ n) (hf : ∀ b, (T b).Frequencies (· ≠ 0))
      (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
      (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (_hB : 0 ≤ B) (_hD : 0 ≤ D)
      (_hφ : ∀ x, |φ x| ≤ B) (_hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
      (_hout : ∀ x, 1 ≤ |x| → φ x = 0) (V : ℝ), (∀ b, (T b).Frequencies (fun s => |(s : ℝ)| ≤ V)) →
      ∀ Q q : ℕ, 2 ≤ Q → ∀ hq : 1 ≤ q, q ≤ Q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v r s : ℝ,
      Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ r → r ≤ s → s ≤ r + 1 →
      Real.log (q : ℝ) ≤ Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ c : ℕ → ℕ → ℂ,
      ∀ A : ℝ, 0 ≤ A → (∀ a < q, ∀ b < q, ‖c a b‖ ≤ A) →
      2 * A * (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) ^ 2 ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      letI : NeZero q := ⟨by omega⟩
      let nodes := fun b => (T b).formulaNodes value hvalue childBound pivotBound (hf b) (.prime false) (.prime true)
      ‖complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
          if (⌊Real.exp x⌋₊).Coprime ⌊Real.exp y⌋₊ then
            c (⌊Real.exp x⌋₊ % q) (⌊Real.exp y⌋₊ % q) *
              movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊
          else 0)) -
        (∫ x in Set.Ioc u v, ∫ y in Set.Ioc r s,
          movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) *
            correctedPrimePairAverage P Q q c x y / ((x : ℂ) * (y : ℂ)))‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) + Real.exp (-Real.exp ((1225 / 100000 : ℝ) * L)) := by
  filter_upwards [P.moving_pair_coprime_prime_haar_rate_uniform n C d] with L hL
  exact hL σ

end Ostmann

end OAI
