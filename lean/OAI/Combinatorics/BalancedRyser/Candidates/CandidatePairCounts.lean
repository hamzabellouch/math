import OAI.Combinatorics.BalancedRyser.Candidates.CandidateConditionalMean
import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePrescribedLine
import OAI.Combinatorics.BalancedRyser.Probability.FiniteExposureTower

namespace OAI

namespace Balanced.CandidatePairs

noncomputable section
open scoped Classical BigOperators
open MeasureTheory PartialAlignment ConditionalRestriction
open CandidateExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def lineTuples (M : MergedPairs F) (l : Line F) : Finset (FourTuple F) :=
  (eligibleTuples l.1).filter (fun T =>
    (∀ i, OnLine (tuplePoint M T i) l) ∧ Function.Injective (tuplePoint M T))

def lineCount (M : MergedPairs F) (l : Line F) : ℕ := (lineTuples M l).card

def targetLine (g : Direction F) (T : FourTuple F) (M : MergedPairs F) : Line F :=
  (g, lineEval g (tuplePoint M T 0))

def pairCount (g : Direction F) (M : MergedPairs F) : ℕ :=
  ∑ T ∈ eligibleTuples g, if M ∈ successfulInDirection T g then
    lineCount M (targetLine g T M) else 0

theorem lineCount_eq_successfulCodes (M : MergedPairs F) (l : Line F) :
    lineCount M l = (CandidatePrescribed.successfulCodes M l).card := by
  apply Finset.card_bij (fun T _ => (T.generator, T.side))
  · intro T hT
    simpa [lineTuples, eligibleTuples, CandidatePrescribed.successfulCodes,
      CandidatePrescribed.alignedCodes, CandidatePrescribed.Eligible, and_assoc] using hT
  · intro T _ U _ h
    cases T
    cases U
    cases h
    rfl
  · intro c hc
    refine ⟨⟨c.1, c.2⟩, ?_, rfl⟩
    simpa [lineTuples, eligibleTuples, CandidatePrescribed.successfulCodes,
      CandidatePrescribed.alignedCodes, CandidatePrescribed.Eligible, and_assoc] using hc

theorem lineCount_le_card (M : MergedPairs F) (l : Line F) :
    lineCount M l ≤ Fintype.card (FourTuple F) := Finset.card_le_univ _

omit [Fintype F] in
theorem tuplePoint_eq_of_generators (T : FourTuple F) (M N : MergedPairs F)
    (h : ∀ d ∈ generatorSet T, M d = N d) (i : Fin 4) :
    tuplePoint M T i = tuplePoint N T i := by
  have hi : T.generator i ∈ generatorSet T := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hn : T.generator (i+1) ∈ generatorSet T :=
    Finset.mem_image.mpr ⟨i+1, Finset.mem_univ _, rfl⟩
  simp only [tuplePoint, constituent, h _ hi, h _ hn]

omit [Fintype F] in
theorem successfulInDirection_congr (T : FourTuple F) (g : Direction F)
    (M N : MergedPairs F) (h : ∀ d ∈ generatorSet T, M d = N d) :
    M ∈ successfulInDirection T g ↔ N ∈ successfulInDirection T g := by
  have heq : tuplePoint M T = tuplePoint N T := funext (tuplePoint_eq_of_generators T M N h)
  simp only [successfulInDirection, alignedInDirection, Set.mem_ofPred_eq, heq]

section Measurable
variable [MeasurableSpace F] [MeasurableSingletonClass F]

theorem conditional_lineCount_le (old : Finset (Direction F)) (a : MergedPairs F)
    (l : Line F) (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (lineCount M l : ℝ) ∂(exposedLaw old a).toMeasure) ≤
      (20480 * (m + 1) ^ 4 : ℝ) := by
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul, lineCount_eq_successfulCodes]
  exact CandidatePrescribed.expected_successfulCodes_le_of_card_le old a l m hm

theorem conditional_partnerCount_le (old : Finset (Direction F))
    (T : FourTuple F) (g : Direction F) (a : MergedPairs F)
    (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (lineCount M (targetLine g T M) : ℝ)
      ∂(exposedLaw (old ∪ generatorSet T) a).toMeasure) ≤
      (20480 * (m + 4 + 1) ^ 4 : ℝ) := by
  have heq := integral_eq_of_eq_on_support (exposedLaw (old ∪ generatorSet T) a)
    (fun M => (lineCount M (targetLine g T M) : ℝ))
    (fun M => (lineCount M (targetLine g T a) : ℝ)) (by
      intro M hM
      have hexposed := (PMF.mem_support_filter_iff
        (canonical_exposure_supported (old ∪ generatorSet T) a)).mp hM |>.1
      have hp := tuplePoint_eq_of_generators T M a
        (fun d hd => hexposed d (Finset.mem_union_right _ hd)) 0
      simp only [targetLine, hp])
  rw [heq]
  have hgen : (generatorSet T).card ≤ 4 := by
    exact (Finset.card_image_le).trans (by simp)
  have hu : (old ∪ generatorSet T).card ≤ m + 4 :=
    (Finset.card_union_le _ _).trans (by omega)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    conditional_lineCount_le (old ∪ generatorSet T) a (targetLine g T a) (m + 4) hu

theorem exposed_integral_mul_le (old extra : Finset (Direction F)) (a : MergedPairs F)
    (f z : MergedPairs F → ℝ) (C Bf Bz : ℝ) (hC : 0 ≤ C)
    (hfn : ∀ M, 0 ≤ f M) (hzn : ∀ M, 0 ≤ z M)
    (hfb : ∀ M, f M ≤ Bf) (hzb : ∀ M, z M ≤ Bz)
    (hdep : ∀ M N, (∀ d ∈ old ∪ extra, M d = N d) → f M = f N)
    (hbound : ∀ y, (∫ M, z M ∂(exposedLaw (old ∪ extra) y).toMeasure) ≤ C) :
    (∫ M, f M * z M ∂(exposedLaw old a).toMeasure) ≤
      C * ∫ M, f M ∂(exposedLaw old a).toMeasure := by
  have huni : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := by
    apply PMF.ext
    intro M
    simp only [offsetLaw, PMF.uniformOfFintype_apply, Fintype.card_eq_nat_card]
  simp only [exposedLaw, huni] at hbound ⊢
  exact filtered_integral_mul_le (D := Direction F) (A := Bool → F)
    old extra a f z C Bf Bz hC hfn hzn hfb hzb hdep hbound

theorem integral_success_indicator (old : Finset (Direction F)) (a : MergedPairs F)
    (T : FourTuple F) (g : Direction F) :
    (∫ M, (if M ∈ successfulInDirection T g then (1 : ℝ) else 0)
      ∂(exposedLaw old a).toMeasure) =
      conditionalProbability old a (successfulInDirection T g) := by
  have hh := integral_eventCount_eq_sum (exposedLaw old a) ({T} : Finset (FourTuple F))
    (fun U => successfulInDirection U g)
  have heq : (fun M : MergedPairs F =>
      ((({T} : Finset (FourTuple F)).filter
        (fun U => M ∈ successfulInDirection U g)).card : ℝ)) =
      (fun M => if M ∈ successfulInDirection T g then 1 else 0) := by
    funext M
    by_cases hM : M ∈ successfulInDirection T g <;>
      simp only [Finset.filter_singleton, hM, ite_true, ite_false,
        Finset.card_singleton, Finset.card_empty, Nat.cast_one, Nat.cast_zero]
  rw [heq] at hh
  simpa only [Finset.sum_singleton, conditionalProbability] using hh

theorem conditional_first_partner_le (old : Finset (Direction F))
    (T : FourTuple F) (g : Direction F) (a : MergedPairs F)
    (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (if M ∈ successfulInDirection T g then
      (lineCount M (targetLine g T M) : ℝ) else 0)
      ∂(exposedLaw old a).toMeasure) ≤
      (20480 * (m + 4 + 1) ^ 4 : ℝ) *
        conditionalProbability old a (successfulInDirection T g) := by
  let f : MergedPairs F → ℝ := fun M => if M ∈ successfulInDirection T g then 1 else 0
  let z : MergedPairs F → ℝ := fun M => lineCount M (targetLine g T M)
  have h := exposed_integral_mul_le old (generatorSet T) a f z
    (20480 * (m + 4 + 1) ^ 4) 1 (Fintype.card (FourTuple F)) (by positivity)
    (fun M => by dsimp [f]; split_ifs <;> norm_num)
    (fun M => by dsimp [z]; positivity)
    (fun M => by dsimp [f]; split_ifs <;> norm_num)
    (fun M => by dsimp [z]; exact_mod_cast lineCount_le_card M (targetLine g T M))
    (by
      intro M N hMN
      have hs := successfulInDirection_congr T g M N
        (fun d hd => hMN d (Finset.mem_union_right _ hd))
      simp only [f, hs])
    (fun y => conditional_partnerCount_le old T g y m hm)
  change (∫ M, f M * z M ∂(exposedLaw old a).toMeasure) ≤
      _ * ∫ M, f M ∂(exposedLaw old a).toMeasure at h
  rw [show (∫ M, f M ∂(exposedLaw old a).toMeasure) =
    conditionalProbability old a (successfulInDirection T g) from
      integral_success_indicator old a T g] at h
  simpa only [f, z, ite_mul, one_mul, zero_mul] using h

theorem integral_sum_pmf {Ω I : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (s : Finset I) (f : I → Ω → ℝ) :
    (∫ ω, ∑ i ∈ s, f i ω ∂p.toMeasure) =
      ∑ i ∈ s, ∫ ω, f i ω ∂p.toMeasure := by
  simp only [PMF.integral_eq_sum, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem conditional_sum_first_partner_le (old : Finset (Direction F))
    (s : Finset (FourTuple F)) (g : Direction F) (a : MergedPairs F)
    (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (∑ T ∈ s, if M ∈ successfulInDirection T g then
      (lineCount M (targetLine g T M) : ℝ) else 0)
      ∂(exposedLaw old a).toMeasure) ≤
      (20480 * (m + 4 + 1) ^ 4 : ℝ) *
        ∑ T ∈ s, conditionalProbability old a (successfulInDirection T g) := by
  rw [integral_sum_pmf, Finset.mul_sum]
  exact Finset.sum_le_sum (fun T _ => conditional_first_partner_le old T g a m hm)

theorem conditional_pairCount_le (old : Finset (Direction F))
    (g : Direction F) (a : MergedPairs F) (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (pairCount g M : ℝ) ∂(exposedLaw old a).toMeasure) ≤
      (20480 * (m + 4 + 1) ^ 4 : ℝ) *
        (20480 * (m + 1) ^ 4) * Fintype.card F := by
  have h := conditional_sum_first_partner_le old (eligibleTuples g) g a m hm
  have hn : (0 : ℝ) ≤ 20480 * (m + 4 + 1) ^ 4 := by positivity
  have hb := mul_le_mul_of_nonneg_left (successProbabilitySum_le g old a m hm) hn
  have heq (M : MergedPairs F) : (pairCount g M : ℝ) =
      ∑ T ∈ eligibleTuples g, if M ∈ successfulInDirection T g then
        (lineCount M (targetLine g T M) : ℝ) else 0 := by
    simp only [pairCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  simp_rw [heq]
  exact h.trans (by simpa only [successProbabilitySum, mul_assoc] using hb)

def firstOverlapPairCount (old : Finset (Direction F)) (g : Direction F)
    (M : MergedPairs F) : ℕ :=
  ∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T old).card),
    if M ∈ successfulInDirection T g then lineCount M (targetLine g T M) else 0

theorem conditional_firstOverlapPairCount_le (old : Finset (Direction F))
    (g : Direction F) (a : MergedPairs F) (m : ℕ) (hm : old.card ≤ m) :
    (∫ M, (firstOverlapPairCount old g M : ℝ) ∂(exposedLaw old a).toMeasure) ≤
      (20480 * (m + 4 + 1) ^ 4 : ℝ) * (16384 * (m + 1) ^ 4) := by
  have h := conditional_sum_first_partner_le old
    ((eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T old).card)) g a m hm
  have hn : (0 : ℝ) ≤ 20480 * (m + 4 + 1) ^ 4 := by positivity
  have hb := mul_le_mul_of_nonneg_left (overlapProbabilitySum_le g old a m hm) hn
  have heq (M : MergedPairs F) : (firstOverlapPairCount old g M : ℝ) =
      ∑ T ∈ (eligibleTuples g).filter (fun T => 0 < (exposedTupleIndices T old).card),
        if M ∈ successfulInDirection T g then
          (lineCount M (targetLine g T M) : ℝ) else 0 := by
    simp only [firstOverlapPairCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  simp_rw [heq]
  exact h.trans hb

end Measurable
end
end Balanced.CandidatePairs

end OAI
