import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesMass

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryGiantChoiceMass
open Construction

theorem choicesMass_nonneg (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (c : HistoryChoices sources seed V l) :
    0 ≤ choicesMass sources seed V l c := by
  rw [choicesMass_eq_internalSourcePrior]
  exact (internalSourcePrior sources seed l).mass_nonneg _

theorem choicesMass_total (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) :
    (∑ c : HistoryChoices sources seed V l, choicesMass sources seed V l c) =
      (Fintype.card (FrequencyChoices V l) : ℝ) := by
  have he := sum_choicesMass_eq_source_prior_real sources seed V l (fun _ => 1)
  simpa only [mul_one,(internalSourcePrior sources seed l).mass_total,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using he

theorem paired_choicesMass_total (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) :
    (∑ c : HistoryChoices sources seed V l, ∑ e : HistoryChoices sources seed V l,
      choicesMass sources seed V l c * choicesMass sources seed V l e) =
      (Fintype.card (FrequencyChoices V l × FrequencyChoices V l) : ℝ) := by
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul,choicesMass_total,Fintype.card_prod,Nat.cast_mul]

theorem paired_choicesMass_total_prod (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) :
    (∑ ce : HistoryChoices sources seed V l × HistoryChoices sources seed V l,
      choicesMass sources seed V l ce.1 * choicesMass sources seed V l ce.2) =
      (Fintype.card (FrequencyChoices V l × FrequencyChoices V l) : ℝ) := by
  rw [Fintype.sum_prod_type]
  exact paired_choicesMass_total sources seed V l

theorem paired_weighted_sum_le (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ)
    (F : HistoryChoices sources seed V l → HistoryChoices sources seed V l → ℝ)
    (B : ℝ)
    (hF : ∀ c e, 0 < choicesMass sources seed V l c →
      0 < choicesMass sources seed V l e → F c e ≤ B) :
    (∑ c : HistoryChoices sources seed V l, ∑ e : HistoryChoices sources seed V l,
      choicesMass sources seed V l c * choicesMass sources seed V l e * F c e) ≤
      (Fintype.card (FrequencyChoices V l × FrequencyChoices V l) : ℝ) * B := by
  calc
    _ ≤ ∑ c : HistoryChoices sources seed V l, ∑ e : HistoryChoices sources seed V l,
        choicesMass sources seed V l c * choicesMass sources seed V l e * B := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro e _
      by_cases hc : choicesMass sources seed V l c = 0
      · simp only [hc,zero_mul,le_refl]
      by_cases he : choicesMass sources seed V l e = 0
      · simp only [he,mul_zero,zero_mul,le_refl]
      have hcpos := lt_of_le_of_ne (choicesMass_nonneg sources seed V l c) (Ne.symm hc)
      have hepos := lt_of_le_of_ne (choicesMass_nonneg sources seed V l e) (Ne.symm he)
      exact mul_le_mul_of_nonneg_left (hF c e hcpos hepos) (mul_nonneg hcpos.le hepos.le)
    _ = (∑ c : HistoryChoices sources seed V l, ∑ e : HistoryChoices sources seed V l,
        choicesMass sources seed V l c * choicesMass sources seed V l e) * B := by
      simp only [Finset.sum_mul]
    _ = _ := by rw [paired_choicesMass_total]

theorem paired_weighted_sum_le_of_ne_zero (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ)
    (F : HistoryChoices sources seed V l → HistoryChoices sources seed V l → ℝ)
    (B : ℝ)
    (hF : ∀ c e, choicesMass sources seed V l c ≠ 0 →
      choicesMass sources seed V l e ≠ 0 → F c e ≤ B) :
    (∑ c : HistoryChoices sources seed V l, ∑ e : HistoryChoices sources seed V l,
      choicesMass sources seed V l c * choicesMass sources seed V l e * F c e) ≤
      (Fintype.card (FrequencyChoices V l × FrequencyChoices V l) : ℝ) * B :=
  paired_weighted_sum_le sources seed V l F B (fun c e hc he => hF c e hc.ne' he.ne')

theorem paired_weighted_sum_prod_le_of_ne_zero
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (l : ℕ)
    (F : HistoryChoices sources seed V l × HistoryChoices sources seed V l → ℝ)
    (B : ℝ)
    (hF : ∀ ce, choicesMass sources seed V l ce.1 ≠ 0 →
      choicesMass sources seed V l ce.2 ≠ 0 → F ce ≤ B) :
    (∑ ce : HistoryChoices sources seed V l × HistoryChoices sources seed V l,
      choicesMass sources seed V l ce.1 * choicesMass sources seed V l ce.2 * F ce) ≤
      (Fintype.card (FrequencyChoices V l × FrequencyChoices V l) : ℝ) * B := by
  rw [Fintype.sum_prod_type]
  exact paired_weighted_sum_le_of_ne_zero sources seed V l (fun c e => F (c,e)) B
    (fun c e => hF (c,e))

end Ostmann.Arithmetic.HistoryGiantChoiceMass

end

end OAI
