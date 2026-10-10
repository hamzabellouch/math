import OAI.Combinatorics.BalancedRyser.Candidates.CandidateMultiplicity
import OAI.Combinatorics.BalancedRyser.Candidates.Candidates
import OAI.Combinatorics.BalancedRyser.Probability.DistinctPairs

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter Topology

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def mergedPairsEquivConstituentOffsets :
    MergedPairs F ≃ ConstituentOffsets (Direction F) F where
  toFun M d := (M d false, M d true)
  invFun M d b := if b then (M d).2 else (M d).1
  left_inv M := by
    funext d b
    cases b <;> rfl
  right_inv M := by
    funext d
    rfl

omit [Field F] [DecidableEq F] in

theorem nat_card_distinctConstituents :
    Nat.card {M : MergedPairs F // DistinctConstituents M} =
      (Fintype.card F * (Fintype.card F - 1)) ^ (Fintype.card F + 1) := by
  classical
  let e := mergedPairsEquivConstituentOffsets (F := F)
  let eA : {M : MergedPairs F // DistinctConstituents M} ≃
      {M : ConstituentOffsets (Direction F) F // AllConstituentPairsDistinct M} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  have hc := card_allConstituentPairsDistinct (Direction F) F
  calc
    _ = Nat.card {M : ConstituentOffsets (Direction F) F //
      AllConstituentPairsDistinct M} := Nat.card_congr eA
    _ = _ := by
      simp only [Direction, Fintype.card_option] at hc
      simpa only [Fintype.card_eq_nat_card] using hc

theorem offsetProbability_distinctConstituents :
    offsetEventProbability {M : MergedPairs F | DistinctConstituents M} =
      (1 - 1 / (Fintype.card F : ℝ)) ^ (Fintype.card F + 1) := by
  classical
  unfold offsetEventProbability
  rw [offsetLaw_eq_uniform, ← finiteUniformProbability_eq_toOuterMeasure]
  unfold finiteUniformProbability
  rw [nat_card_distinctConstituents, Nat.card_eq_fintype_card]
  simp only [MergedPairs, Fintype.card_fun, Fintype.card_bool,
    Direction, Fintype.card_option, Nat.cast_pow, Nat.cast_mul]
  rw [← div_pow]
  congr 1
  rw [Nat.cast_sub (by exact Fintype.card_pos : 1 ≤ Fintype.card F), Nat.cast_one]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := F)
  field_simp

theorem offsetProbability_distinctConstituents_eq_order :
    offsetEventProbability {M : MergedPairs F | DistinctConstituents M} =
      distinctConstituentProbability (Fintype.card F) := by
  rw [offsetProbability_distinctConstituents,
    distinctConstituentProbability_eq _ Fintype.card_pos]

theorem tendsto_offsetProbability_distinctConstituents
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | DistinctConstituents M}) atTop (𝓝 (Real.exp (-1))) := by
  simpa only [offsetProbability_distinctConstituents_eq_order, Function.comp_def] using
    tendsto_distinctConstituentProbability.comp hq

theorem tendsto_candidateGood_and_distinct
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (c C : ℝ)
    (hgood : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c C}) atTop (𝓝 1)) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c C ∧ DistinctConstituents M})
      atTop (𝓝 (Real.exp (-1))) := by
  have hdistinct := tendsto_offsetProbability_distinctConstituents F hq
  have h := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun _ => {M | DistinctConstituents M})
    (fun _ => {M | CandidateGraphGood M c C}) hdistinct hgood
  simpa only [offsetEventProbability, ← Set.ofPred_and, and_comm] using h

end Balanced

end OAI
