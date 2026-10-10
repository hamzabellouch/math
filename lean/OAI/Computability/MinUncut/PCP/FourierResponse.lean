import Mathlib
import OAI.Computability.MinUncut.Games.OuterQuestions
import OAI.Computability.MinUncut.Encoding.Decoder

namespace OAI

section
noncomputable section

namespace MinUncutGames.Foundations.Hastad

open scoped BigOperators
open Finset
open MinUncutGames.Foundations.Games

variable {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

def supportResponse (fallback : I) (s : Cube I) : FiniteDistribution I where
  weight i := if (support s).Nonempty then
    if i ∈ support s then 1 / ((support s).card : ℝ) else 0
    else if i = fallback then 1 else 0
  nonnegative i := by
    split_ifs <;> positivity
  normalized := by
    by_cases hs : (support s).Nonempty
    · have hc : ((support s).card : ℝ) ≠ 0 :=
        ne_of_gt (Nat.cast_pos.mpr (Finset.card_pos.mpr hs))
      simp [hs, hc]
    · simp [hs]

theorem supportResponse_expectation (fallback : I) (s : Cube I) (H : I → ℝ)
    (hs : (support s).Nonempty) :
    (supportResponse fallback s).expectation H =
      (∑ i ∈ support s, H i) / ((support s).card : ℝ) := by
  simp only [FiniteDistribution.expectation, supportResponse, hs, ite_true]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem]
  simp only [div_eq_mul_inv, one_mul, Finset.univ_inter]
  rw [← Finset.mul_sum]
  ring

def fourierResponse (fallback : I) (F : Cube I → Bool) : FiniteDistribution I where
  weight i := ∑ s, coefficient (fun f => bitSign (F f)) s ^ 2 *
    (supportResponse fallback s).weight i
  nonnegative i := Finset.sum_nonneg fun s _ =>
    mul_nonneg (sq_nonneg _) ((supportResponse fallback s).nonnegative i)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
    exact sign_parseval F

theorem fourierResponse_expectation (fallback : I) (F : Cube I → Bool)
    (H : I → ℝ) :
    (fourierResponse fallback F).expectation H =
      ∑ s, coefficient (fun f => bitSign (F f)) s ^ 2 *
        (supportResponse fallback s).expectation H := by
  unfold FiniteDistribution.expectation fourierResponse
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem response_expectation_nonnegative {K : Type*} [Fintype K]
    (law : FiniteDistribution K) (H : K → ℝ) (hH : ∀ k, 0 ≤ H k) :
    0 ≤ law.expectation H :=
  Finset.sum_nonneg fun k _ => mul_nonneg (law.nonnegative k) (hH k)

def responseAgreement (π : J → I) (fallbackI : I) (fallbackJ : J)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  (fourierResponse fallbackI A).expectation fun i =>
    (fourierResponse fallbackJ B).expectation fun j => if π j = i then 1 else 0

def validResponseAgreement (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  (fourierResponse fallbackI A).expectation fun i =>
    (fourierResponse fallbackJ B).expectation fun j =>
      if π j = i ∧ valid j = true then 1 else 0

theorem supportResponse_validAgreement (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (a : Cube I) (b : Cube J)
    (ha : (support a).Nonempty) (hb : (support b).Nonempty) :
    (supportResponse fallbackI a).expectation (fun i =>
      (supportResponse fallbackJ b).expectation (fun j =>
        if π j = i ∧ valid j = true then 1 else 0)) =
      validAgreementProbability valid π a b := by
  rw [supportResponse_expectation fallbackI a _ ha]
  simp_rw [supportResponse_expectation fallbackJ b _ hb, Finset.sum_boole]
  unfold validAgreementProbability
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

theorem validAgreement_le_supportResponses (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (a : Cube I) (b : Cube J) :
    validAgreementProbability valid π a b ≤
      (supportResponse fallbackI a).expectation (fun i =>
        (supportResponse fallbackJ b).expectation (fun j =>
          if π j = i ∧ valid j = true then 1 else 0)) := by
  by_cases ha : (support a).Nonempty
  · by_cases hb : (support b).Nonempty
    · exact le_of_eq (supportResponse_validAgreement valid π fallbackI fallbackJ a b ha hb).symm
    · have he : support b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      simp only [validAgreementProbability, he, Finset.card_empty, Nat.cast_zero,
        mul_zero, div_zero]
      apply response_expectation_nonnegative
      intro i
      apply response_expectation_nonnegative
      intro j
      split_ifs <;> norm_num
  · have he : support a = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    simp only [validAgreementProbability, he, Finset.sum_empty, Finset.card_empty,
      Nat.cast_zero, zero_mul, div_zero]
    apply response_expectation_nonnegative
    intro i
    apply response_expectation_nonnegative
    intro j
    split_ifs <;> norm_num

theorem validDecoderSuccess_le_response (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (A : Cube I → Bool) (B : Cube J → Bool) :
    validDecoderSuccess valid π A B ≤
      validResponseAgreement valid π fallbackI fallbackJ A B := by
  unfold validDecoderSuccess validResponseAgreement
  rw [FiniteDistribution.expectation_comm]
  rw [fourierResponse_expectation fallbackJ B]
  apply Finset.sum_le_sum
  intro b _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [FiniteDistribution.expectation_comm]
  rw [fourierResponse_expectation fallbackI A]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact validAgreement_le_supportResponses valid π fallbackI fallbackJ a b

theorem conditioned_folded_response_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool)
    (j₀ : {j : J // valid j = true}) (tableB : HalfCube j₀ → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (conditionedFoldedAnswer valid j₀ tableB g)) ^ 2 ≤
      validResponseAgreement valid π i₀ j₀.val (foldedAnswer i₀ tableA)
        (conditionedFoldedAnswer valid j₀ tableB) :=
  (conditioned_folded_decoder_bound ε π valid i₀ tableA j₀ tableB hε hε').trans
    (validDecoderSuccess_le_response valid π i₀ j₀.val _ _)

end MinUncutGames.Foundations.Hastad

end
end

end OAI
