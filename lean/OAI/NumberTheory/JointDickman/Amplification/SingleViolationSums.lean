import OAI.NumberTheory.JointDickman.Arithmetic.SingleSieveRemainder

namespace OAI

/-! # Finite summation of the one-coefficient regularity violations -/

namespace JointDickman

open Finset

theorem single_prefix_sum_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B u v : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → u ≤ v →
      ∀ (L : ℕ) (τ s : ℝ), 0 < L → 0 ≤ τ → 0 < s → s ≤ 1 →
      Real.exp s ≤ 2 → Real.exp (-s) ≤ 2 →
      0 ≤ auxiliaryLogLength B → auxiliaryLogLength B ≤ Real.log B →
      (∑ n ∈ Ico u v, prefixViolationMass B L τ (coefficientPrimeSet B n) (coefficientWeight B n)) ≤
      C * ((v : ℝ) - u) * prefixGridError B L (δ / 8) τ s +
      2 * L * B * singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
  classical
  obtain ⟨C, hC, hbound⟩ := single_prefix_pair_bound hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B u v hB hZ hPZ hlog huv L τ s hL hτ hs hs1 he hen hℓ hℓlog
  unfold prefixViolationMass
  rw [sum_comm]
  have hh := sum_le_linear_remainder (Icc 1 L)
    (fun i => ∑ n ∈ Ico u v,
      ((if ((primePrefix B ((i : ℝ) / L) (coefficientPrimeSet B n)).card : ℝ) <
        (((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B then coefficientWeight B n else 0) +
      (if (((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B <
        ((primePrefix B ((i : ℝ) / L) (coefficientPrimeSet B n)).card : ℝ) then coefficientWeight B n else 0)))
    (fun i => prefixLowerFactor B (δ / 8) ((i : ℝ) / L) τ s + prefixUpperFactor B (δ / 8) ((i : ℝ) / L) τ s)
    (fun i => Real.exp (s * ((((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B)) +
      Real.exp (-s * ((((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B)))
    (R := 2 * B) (singleCoefficientRemainder_nonneg _ _)
    (fun i _ => hbound B u v hB hZ hPZ hlog huv ((i : ℝ) / L) τ s hs he hen)
    (fun i hi => by
      have hL' : (0 : ℝ) < L := by exact_mod_cast hL
      have hiL : (i : ℝ) ≤ L := by exact_mod_cast (mem_Icc.mp hi).2
      have hm := prefix_markov_multiplier_bounds (by omega : 1 ≤ B)
        (div_nonneg (Nat.cast_nonneg i) hL'.le) ((div_le_one hL').mpr hiL) hτ hs.le hs1 hℓ hℓlog
      linarith only [hm.1, hm.2])
  convert hh using 1
  simp only [prefixGridError, Nat.card_Icc, Nat.add_sub_cancel]
  ring

theorem single_tail_sum_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B u v : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → u ≤ v →
      1 ≤ Real.log (auxiliaryCutoff B) → ∀ (C₀ : ℝ), 0 ≤ C₀ →
      (∑ n ∈ Ico u v, tailViolationMass B C₀ (coefficientPrimeSet B n) (coefficientWeight B n)) ≤
      C * ((v : ℝ) - u) * (∑ i ∈ activeTailIndices B, tailChernoffFactor B i (δ / 8) C₀) +
      (B : ℝ)^2 * singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
  classical
  obtain ⟨C, hC, hbound⟩ := single_tail_violation_bound hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B u v hB hZ hPZ hlog huv hlogP C₀ hC₀
  simp_rw [tailViolationMass_eq_restricted _ _ hC₀ hlogP]
  rw [sum_comm]
  have hh := sum_le_linear_remainder (activeTailIndices B)
    (fun i => ∑ n ∈ Ico u v,
      if (((coefficientPrimeSet B n).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀ then coefficientWeight B n else 0)
    (fun i => tailChernoffFactor B i (δ / 8) C₀)
    (fun i => Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀)))
    (R := B) (singleCoefficientRemainder_nonneg _ _)
    (fun i _ => hbound B u v hB hZ hPZ hlog huv i C₀)
    (fun i _ => by
      apply tail_markov_multiplier_bound (by exact_mod_cast (by omega : 1 ≤ B)) _ hC₀
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hlogP)
  apply hh.trans
  apply add_le_add_right
  have hcard : ((activeTailIndices B).card : ℝ) ≤ B := by
    exact_mod_cast (calc (activeTailIndices B).card ≤ (range B).card := card_filter_le _ _
                        _ = B := card_range B)
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg B))
    (singleCoefficientRemainder_nonneg B (sieveCutoff (δ / 8) B))
  nlinarith only [h]

end JointDickman

end OAI
