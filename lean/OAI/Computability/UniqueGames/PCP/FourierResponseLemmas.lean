import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.PCP.SourceNoiseParameterLemmas

namespace OAI

section

/-! The Fourier decoder is an actual finite law of private answers.  Empty
Fourier supports use an explicit fallback answer, making every response law
normalized even before folding has been imposed. -/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset
open UniqueGamesTheorem.Foundations.Games

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

/-- Squared Fourier coefficients select a mask; a uniform support coordinate
selects the actual answer. Both stages use only this player's private table. -/
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

/-- Local soundness now bounds the success of two genuine normalized answer
laws. No assumption about randomized decoding or its normalization remains. -/
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

end UniqueGamesTheorem.Foundations.Hastad

end

end

section

/-! Weighted question averaging and the actual finite-game consequence of the
Håstad decoder. The game value is the maximum over deterministic private answer
tables; the Fourier responses are derandomized by the checked table law. -/

noncomputable section
namespace UniqueGamesTheorem.Foundations.Hastad

open scoped BigOperators
open Finset
open UniqueGamesTheorem.Foundations.Games

theorem distribution_sq_expectation_le {Ω : Type*} [Fintype Ω]
    (law : FiniteDistribution Ω) (F : Ω → ℝ) :
    law.expectation F ^ 2 ≤ law.expectation (fun x => F x ^ 2) := by
  let m := law.expectation F
  have h := response_expectation_nonnegative law (fun x => (F x - m) ^ 2)
    (fun x => sq_nonneg _)
  have he : law.expectation (fun x => (F x - m) ^ 2) =
      law.expectation (fun x => F x ^ 2) - m ^ 2 := by
    unfold FiniteDistribution.expectation
    calc
      _ = ∑ x, ((law.weight x * F x ^ 2 - 2 * m * (law.weight x * F x)) +
          law.weight x * m ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, law.normalized]
        change (law.expectation (fun x => F x ^ 2) - 2 * m * m) + 1 * m ^ 2 = _
        simp only [FiniteDistribution.expectation]
        ring
  rw [he] at h
  dsimp [m] at h
  linarith

variable {Q₁ Q₂ I J : Type*}
  [Fintype Q₁] [DecidableEq Q₁] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype J] [DecidableEq J] [Nonempty J]

def projectionGame (questions : FiniteDistribution (Q₁ × Q₂))
    (π : Q₁ → Q₂ → J → I) (valid : Q₂ → J → Bool) : Game Q₁ Q₂ I J where
  questions := questions
  accepts q₁ q₂ i j := decide (π q₁ q₂ j = i ∧ valid q₂ j = true)

def questionBias (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) (q : Q₁ × Q₂) : ℝ :=
  testBias ε (π q.1 q.2) (fun f => bitSign (A q.1 f)) (fun g => bitSign (B q.2 g))

def questionAcceptance (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) (q : Q₁ × Q₂) : ℝ :=
  testAcceptance ε (π q.1 q.2) (A q.1) (B q.2)

omit [DecidableEq Q₁] [DecidableEq Q₂] [Nonempty I] [Nonempty J] in
theorem questionAcceptance_eq (questions : FiniteDistribution (Q₁ × Q₂))
    (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) :
    questions.expectation (questionAcceptance ε π A B) =
      (1 + questions.expectation (questionBias ε π A B)) / 2 := by
  unfold questionAcceptance
  simp_rw [testAcceptance_eq]
  unfold questionBias FiniteDistribution.expectation
  simp only [div_eq_mul_inv, mul_add, mul_one, ← mul_assoc,
    Finset.sum_add_distrib, ← Finset.sum_mul, questions.normalized]

/-- Storage distinguishes an actually empty legal domain from a folded table
over its legal assignments. The empty case needs no nonexistent fold point. -/
inductive ConditionedOracle (valid : J → Bool) where
  | empty (noLegal : ∀ j, valid j = false)
  | stored (j₀ : {j : J // valid j = true}) (table : HalfCube j₀ → Bool)

def ConditionedOracle.answer {valid : J → Bool} : ConditionedOracle valid → Cube J → Bool
  | .empty _ => fun _ => false
  | .stored j₀ table => conditionedFoldedAnswer valid j₀ table

def ConditionedOracle.fallback {valid : J → Bool} (default : J) :
    ConditionedOracle valid → J
  | .empty _ => default
  | .stored j₀ _ => j₀.val

omit [Nonempty I] [Nonempty J] in
theorem testBias_constant_right (ε : ℝ) (π : J → I) (A : Cube I → ℝ) :
    testBias ε π A (fun _ => 1) = 𝔼 f, A f := by
  unfold testBias
  simp only [mul_one, Fintype.expect_const]
  simp_rw [← Finset.sum_mul, noiseWeight_sum, one_mul]

omit [Nonempty I] [Nonempty J] in
theorem empty_conditioned_bias (ε : ℝ) (π : J → I)
    (i₀ : I) (tableA : HalfCube i₀ → Bool) :
    testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun _ => bitSign false) = 0 := by
  simp only [bitSign, Bool.false_eq_true, ite_false]
  rw [testBias_constant_right]
  have hz := foldedAnswer_zero_coefficient i₀ tableA
  simpa [coefficient, walsh, bitSign] using hz

omit [Nonempty I] [Nonempty J] in
theorem conditionedOracle_response_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool) (default : J)
    (right : ConditionedOracle valid) (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (right.answer g)) ^ 2 ≤
      validResponseAgreement valid π i₀ (right.fallback default)
        (foldedAnswer i₀ tableA) right.answer := by
  cases right with
  | empty noLegal =>
      simp only [ConditionedOracle.answer, ConditionedOracle.fallback,
        empty_conditioned_bias, pow_two, mul_zero]
      unfold validResponseAgreement
      apply response_expectation_nonnegative
      intro i
      apply response_expectation_nonnegative
      intro j
      split_ifs <;> norm_num
  | stored j₀ table =>
      exact conditioned_folded_response_bound ε π valid i₀ tableA j₀ table hε hε'

theorem folded_game_decoder_bound
    (questions : FiniteDistribution (Q₁ × Q₂))
    (ε : ℝ) (π : Q₁ → Q₂ → J → I) (valid : Q₂ → J → Bool)
    (i₀ : Q₁ → I) (tableA : ∀ q, HalfCube (i₀ q) → Bool)
    (j₀ : ∀ q, {j : J // valid q j = true})
    (tableB : ∀ q, HalfCube (j₀ q) → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * questions.expectation (questionBias ε π
      (fun q => foldedAnswer (i₀ q) (tableA q))
      (fun q => conditionedFoldedAnswer (valid q) (j₀ q) (tableB q))) ^ 2 ≤
      (projectionGame questions π valid).value := by
  let A := fun q => foldedAnswer (i₀ q) (tableA q)
  let B := fun q => conditionedFoldedAnswer (valid q) (j₀ q) (tableB q)
  let bias := questionBias ε π A B
  calc
    _ ≤ 4 * ε * questions.expectation (fun q => bias q ^ 2) :=
      mul_le_mul_of_nonneg_left (distribution_sq_expectation_le questions bias) (by linarith)
    _ = questions.expectation (fun q => 4 * ε * bias q ^ 2) := by
      unfold FiniteDistribution.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ questions.expectation (fun q =>
        validResponseAgreement (valid q.2) (π q.1 q.2) (i₀ q.1) (j₀ q.2).val
          (A q.1) (B q.2)) := by
      unfold FiniteDistribution.expectation
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (questions.nonnegative q)
      exact conditioned_folded_response_bound ε (π q.1 q.2) (valid q.2)
        (i₀ q.1) (tableA q.1) (j₀ q.2) (tableB q.2) hε hε'
    _ = (projectionGame questions π valid).stochasticSuccess
        (fun q => fourierResponse (i₀ q) (A q))
        (fun q => fourierResponse (j₀ q).val (B q)) := by
      simp [Game.stochasticSuccess, projectionGame, validResponseAgreement]
    _ ≤ _ := Game.stochasticSuccess_le_value _ _ _

/-- The game bound includes inconsistent clause tuples, whose legal local
domain is empty and whose implemented right oracle is constant. -/
theorem conditionedOracle_game_decoder_bound
    (questions : FiniteDistribution (Q₁ × Q₂))
    (ε : ℝ) (π : Q₁ → Q₂ → J → I) (valid : Q₂ → J → Bool)
    (i₀ : Q₁ → I) (tableA : ∀ q, HalfCube (i₀ q) → Bool)
    (default : J) (right : ∀ q, ConditionedOracle (valid q))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * questions.expectation (questionBias ε π
      (fun q => foldedAnswer (i₀ q) (tableA q)) (fun q => (right q).answer)) ^ 2 ≤
      (projectionGame questions π valid).value := by
  let A := fun q => foldedAnswer (i₀ q) (tableA q)
  let B := fun q => (right q).answer
  let bias := questionBias ε π A B
  calc
    _ ≤ 4 * ε * questions.expectation (fun q => bias q ^ 2) :=
      mul_le_mul_of_nonneg_left (distribution_sq_expectation_le questions bias) (by linarith)
    _ = questions.expectation (fun q => 4 * ε * bias q ^ 2) := by
      unfold FiniteDistribution.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ questions.expectation (fun q =>
        validResponseAgreement (valid q.2) (π q.1 q.2) (i₀ q.1)
          ((right q.2).fallback default) (A q.1) (B q.2)) := by
      unfold FiniteDistribution.expectation
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (questions.nonnegative q)
      exact conditionedOracle_response_bound ε (π q.1 q.2) (valid q.2)
        (i₀ q.1) (tableA q.1) default (right q.2) hε hε'
    _ = (projectionGame questions π valid).stochasticSuccess
        (fun q => fourierResponse (i₀ q) (A q))
        (fun q => fourierResponse ((right q).fallback default) (B q)) := by
      simp [Game.stochasticSuccess, projectionGame, validResponseAgreement]
    _ ≤ _ := Game.stochasticSuccess_le_value _ _ _

theorem conditionedOracle_acceptance_bound
    (questions : FiniteDistribution (Q₁ × Q₂))
    (ε δ : ℝ) (π : Q₁ → Q₂ → J → I) (valid : Q₂ → J → Bool)
    (i₀ : Q₁ → I) (tableA : ∀ q, HalfCube (i₀ q) → Bool)
    (default : J) (right : ∀ q, ConditionedOracle (valid q))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hvalue : (projectionGame questions π valid).value ≤ 4 * ε * δ ^ 2) :
    questions.expectation (questionAcceptance ε π
      (fun q => foldedAnswer (i₀ q) (tableA q)) (fun q => (right q).answer)) ≤
      (1 + δ) / 2 := by
  have hd := conditionedOracle_game_decoder_bound questions ε π valid i₀ tableA
    default right hε hε'
  have hpos : 0 < 4 * ε := by positivity
  have hs := le_of_mul_le_mul_left (hd.trans hvalue) hpos
  rw [questionAcceptance_eq]
  nlinarith

end UniqueGamesTheorem.Foundations.Hastad

end

end

end OAI
