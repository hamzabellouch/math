import OAI.NumberTheory.JointDickman.Counting.SingleCoefficientIndicators

namespace OAI

/-! # Weighted regularity violations for a single coefficient -/

namespace JointDickman

open Finset

noncomputable def singleCoefficientRemainder (B Z : ℕ) : ℝ :=
  coefficientScale B * (2 * (Z + 1 : ℝ) * Z)

theorem singleCoefficientRemainder_nonneg (B Z : ℕ) : 0 ≤ singleCoefficientRemainder B Z := by
  have hs := coefficientScale_nonneg B
  unfold singleCoefficientRemainder
  positivity

open Classical in
theorem single_prefix_pair_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B u v : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → u ≤ v →
      ∀ (g τ s : ℝ), 0 < s → Real.exp s ≤ 2 → Real.exp (-s) ≤ 2 →
      (∑ n ∈ Ico u v,
        ((if ((primePrefix B g (coefficientPrimeSet B n)).card : ℝ) <
          (g / 2 - τ) * auxiliaryLogLength B then coefficientWeight B n else 0) +
        (if (g / 2 + τ) * auxiliaryLogLength B <
          ((primePrefix B g (coefficientPrimeSet B n)).card : ℝ) then coefficientWeight B n else 0))) ≤
      C * ((v : ℝ) - u) * (prefixLowerFactor B (δ / 8) g τ s + prefixUpperFactor B (δ / 8) g τ s) +
      (Real.exp (s * ((g / 2 - τ) * auxiliaryLogLength B)) +
        Real.exp (-s * ((g / 2 + τ) * auxiliaryLogLength B))) *
          singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
  obtain ⟨C, hC, hb⟩ := single_coefficient_count_tail hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C, hC, ?_⟩
  intro B u v hB hZ hPZ hlog huv g τ s hs he hen
  have hlo := hb B (sieveCutoff (δ / 8) B) u v hB hZ hPZ hlog huv
    (primePrefix B g (auxiliaryPrimes B)) (-s) ((g / 2 - τ) * auxiliaryLogLength B) hen
  have hup := hb B (sieveCutoff (δ / 8) B) u v hB hZ hPZ hlog huv
    (primePrefix B g (auxiliaryPrimes B)) s ((g / 2 + τ) * auxiliaryLogLength B) he
  have hlow := (sum_le_sum (fun n _ => single_prefix_lower_indicator (B := B) (n := n) g τ s hs)).trans hlo
  have hupp := (sum_le_sum (fun n _ => single_prefix_upper_indicator (B := B) (n := n) g τ s hs)).trans hup
  simp only [neg_neg, mul_assoc] at hlow hupp
  rw [sum_add_distrib]
  have h := add_le_add hlow hupp
  convert h using 1
  simp only [prefixLowerFactor, prefixUpperFactor, singleCoefficientRemainder, mul_assoc]
  ring

open Classical in
theorem single_tail_violation_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B u v : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → u ≤ v →
      ∀ (i : ℕ) (C₀ : ℝ),
      (∑ n ∈ Ico u v, if (((coefficientPrimeSet B n).filter
        (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
          (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀
        then coefficientWeight B n else 0) ≤
      C * ((v : ℝ) - u) * tailChernoffFactor B i (δ / 8) C₀ +
      Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀)) *
        singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
  obtain ⟨C, hC, hb⟩ := single_coefficient_count_tail hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C, hC, ?_⟩
  intro B u v hB hZ hPZ hlog huv i C₀
  have he : Real.exp (-(1 / 10 : ℝ)) ≤ 2 :=
    (Real.exp_le_exp.mpr (by norm_num : -(1 / 10 : ℝ) ≤ 0)).trans (by norm_num)
  have h := hb B (sieveCutoff (δ / 8) B) u v hB hZ hPZ hlog huv
    ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) (-(1 / 10 : ℝ))
    ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀) he
  have hh := (sum_le_sum (fun n _ => single_tail_indicator (B := B) (n := n) (i := i) C₀)).trans h
  simpa only [tailChernoffFactor, singleCoefficientRemainder, neg_neg, mul_assoc] using hh

end JointDickman

end OAI
