import OAI.NumberTheory.JointDickman.Amplification.PrefixViolationSum

namespace OAI

/-! # Finite dyadic summation of the actual tail failures -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def activeTailIndices (B : ℕ) : Finset ℕ :=
  (range B).filter (fun i => primeTailEndpoint B i < B)

theorem tailViolationMass_eq_restricted {B : ℕ} {C : ℝ} (S : Finset ℕ) (w : ℝ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) :
    tailViolationMass B C S w = ∑ i ∈ activeTailIndices B,
      if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C then w else 0 := by
  classical
  unfold tailViolationMass activeTailIndices
  rw [sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hi : primeTailEndpoint B i < B
  · simp only [hi, ite_true]
  · have hY : 0 < primeTailEndpoint B i := by unfold primeTailEndpoint; positivity
    have hdiv : (B : ℝ) / primeTailEndpoint B i ≤ 1 := (div_le_one hY).mpr (le_of_not_gt hi)
    have hlog' := Real.log_nonpos (div_nonneg (Nat.cast_nonneg B) hY.le) hdiv
    have hcount : (0 : ℝ) ≤ (S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card :=
      Nat.cast_nonneg _
    have hnot : ¬((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C := by linarith
    simp only [hi, hnot, ite_false]

theorem coefficient_tail_sum_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      1 ≤ Real.log (auxiliaryCutoff B) → ∀ (k : Fin 3) (C₀ : ℝ), 0 ≤ C₀ →
      (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        tailViolationMass B C₀ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d)) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        (∑ i ∈ activeTailIndices B, tailChernoffFactor B i (δ / 8) C₀) +
      (B : ℝ)^2 * coefficientRectangleRemainder B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ := by
  classical
  obtain ⟨C, hC, hbound⟩ := coefficient_tail_violation_bound hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ hlogP k C₀ hC₀
  let f := fun i b d =>
    if (((coefficientPrimeSet B (coefficientForm k j b d)).filter
      (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
      (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀
      then tripleCoefficientWeight B j b d else 0
  have heq : (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
      tailViolationMass B C₀ (coefficientPrimeSet B (coefficientForm k j b d))
        (tripleCoefficientWeight B j b d)) =
      ∑ i ∈ activeTailIndices B, ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, f i b d := by
    simp_rw [tailViolationMass_eq_restricted _ _ hC₀ hlogP]
    change (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, ∑ i ∈ activeTailIndices B, f i b d) = _
    calc
      _ = ∑ b ∈ Ico l₁ r₁, ∑ i ∈ activeTailIndices B, ∑ d ∈ Ico l₂ r₂, f i b d :=
        sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := sum_comm
  rw [heq]
  have hE := coefficientRectangleRemainder_nonneg B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ hI hJ
  have hsum := sum_le_linear_remainder (activeTailIndices B)
    (fun i => ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, f i b d)
    (fun i => tailChernoffFactor B i (δ / 8) C₀)
    (fun i => Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) *
      Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀)))
    (R := B) hE
    (fun i _ => hbound B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k i C₀)
    (fun i _ => by
      apply tail_markov_multiplier_bound (by exact_mod_cast (by omega : 1 ≤ B)) _ hC₀
      have hp : (1 : ℝ) ≤ (2 : ℝ)^i := one_le_pow₀ (by norm_num)
      exact one_le_mul_of_one_le_of_one_le hp hlogP)
  apply hsum.trans
  apply add_le_add_right
  have hcard : ((activeTailIndices B).card : ℝ) ≤ B := by
    exact_mod_cast (calc (activeTailIndices B).card ≤ (range B).card := card_filter_le _ _
                        _ = B := card_range B)
  have hh := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg B)
  have hh' := mul_le_mul_of_nonneg_right hh hE
  nlinarith

end JointDickman

end OAI
