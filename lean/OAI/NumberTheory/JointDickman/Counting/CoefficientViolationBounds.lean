import OAI.NumberTheory.JointDickman.Counting.CoefficientCountIndicators

namespace OAI

/-! # Weighted bounds for individual prefix and tail violations -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def coefficientRectangleRemainder (B Z l₁ r₁ l₂ r₂ : ℕ) : ℝ :=
  coefficientScale B ^ 3 *
    (2 * (((r₁ : ℝ) - l₁) + ((r₂ : ℝ) - l₂) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3)

theorem coefficientRectangleRemainder_nonneg (B Z l₁ r₁ l₂ r₂ : ℕ)
    (hI : l₁ ≤ r₁) (hJ : l₂ ≤ r₂) : 0 ≤ coefficientRectangleRemainder B Z l₁ r₁ l₂ r₂ := by
  have hI' : (0 : ℝ) ≤ (r₁ : ℝ) - l₁ := sub_nonneg.mpr (by exact_mod_cast hI)
  have hJ' : (0 : ℝ) ≤ (r₂ : ℝ) - l₂ := sub_nonneg.mpr (by exact_mod_cast hJ)
  unfold coefficientRectangleRemainder
  have hs := coefficientScale_nonneg B
  positivity

theorem coefficient_prefix_pair_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (k : Fin 3) (g τ s : ℝ), 0 < s → Real.exp s ≤ 2 → Real.exp (-s) ≤ 2 →
      (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        ((if ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b d))).card : ℝ) <
          (g / 2 - τ) * auxiliaryLogLength B then tripleCoefficientWeight B j b d else 0) +
        (if (g / 2 + τ) * auxiliaryLogLength B <
          ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b d))).card : ℝ)
          then tripleCoefficientWeight B j b d else 0))) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        (prefixLowerFactor B (δ / 8) g τ s + prefixUpperFactor B (δ / 8) g τ s) +
      (Real.exp (s * ((g / 2 - τ) * auxiliaryLogLength B)) +
        Real.exp (-s * ((g / 2 + τ) * auxiliaryLogLength B))) *
          coefficientRectangleRemainder B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ := by
  classical
  obtain ⟨C, hC, hb⟩ := coefficient_form_count_tail hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C, hC, ?_⟩
  intro B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k g τ s hs he hen
  have hlo := hb B (sieveCutoff (δ / 8) B) j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k
    (primePrefix B g (auxiliaryPrimes B)) (-s) ((g / 2 - τ) * auxiliaryLogLength B) hen
  have hup := hb B (sieveCutoff (δ / 8) B) j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k
    (primePrefix B g (auxiliaryPrimes B)) s ((g / 2 + τ) * auxiliaryLogLength B) he
  have hlow := (sum_le_sum (fun b _ => sum_le_sum (fun d _ => prefix_lower_indicator_le (B := B) (j := j) (b := b) (c := d) k g τ s hs))).trans hlo
  have hupp := (sum_le_sum (fun b _ => sum_le_sum (fun d _ => prefix_upper_indicator_le (B := B) (j := j) (b := b) (c := d) k g τ s hs))).trans hup
  simp only [neg_neg, mul_assoc] at hlow hupp
  simp only [sum_add_distrib]
  have h := add_le_add hlow hupp
  convert h using 1
  simp only [prefixLowerFactor, prefixUpperFactor, coefficientRectangleRemainder, mul_assoc]
  ring

theorem coefficient_tail_violation_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (k : Fin 3) (i : ℕ) (C₀ : ℝ),
      (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        if (((coefficientPrimeSet B (coefficientForm k j b d)).filter
          (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
            (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀
          then tripleCoefficientWeight B j b d else 0) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j * tailChernoffFactor B i (δ / 8) C₀ +
      Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀)) *
        coefficientRectangleRemainder B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ := by
  classical
  obtain ⟨C, hC, hb⟩ := coefficient_form_count_tail hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C, hC, ?_⟩
  intro B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k i C₀
  have hen : Real.exp (-(1 / 10 : ℝ)) ≤ 2 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ 2 := by norm_num
  have h := hb B (sieveCutoff (δ / 8) B) j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k
    ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) (-(1 / 10 : ℝ))
    ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀) hen
  have hh := (sum_le_sum (fun b _ => sum_le_sum (fun d _ => tail_indicator_le (B := B) (j := j) (b := b) (c := d) k C₀))).trans h
  simpa only [tailChernoffFactor, coefficientRectangleRemainder, neg_neg, mul_assoc] using hh

end JointDickman

end OAI
