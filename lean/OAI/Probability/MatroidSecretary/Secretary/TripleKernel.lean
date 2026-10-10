import OAI.Probability.MatroidProphet.Main
import OAI.Probability.MatroidSecretary.Secretary.TripleKernelModel
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

namespace OAI

/-! Explicit normalized one-label reconstruction kernel from secretary.tex,
lines 64--81. These are finite identities, including the zero-mask case. -/

namespace MatroidProphet.Secretary

open Finset

lemma tripleWeight_sum (t : ℝ) : (∑ x : MaskTriple, tripleWeight t x) = 1 := by
  simp [MaskTriple, Fintype.sum_prod_type, tripleWeight]
  ring

lemma tripleWeight_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : MaskTriple) : 0 ≤ tripleWeight t x := by
  rcases x with ⟨h,d,c⟩
  cases d <;> cases c <;> norm_num [tripleWeight] <;> linarith

lemma tripleWeight_zero (t : ℝ) :
    tripleWeight t (false, false, false) = 3 / 8 * (1-t) := by
  norm_num [tripleWeight]

lemma mainRevealRate_eq_source :
    mainRevealRate = (5 : ℝ) / 8 + 3 * ((2 : ℝ)^143)⁻¹ := by
  norm_num [mainRevealRate, thinningRate]

lemma mainRevealRate_pos : 0 < mainRevealRate := by
  norm_num [mainRevealRate, thinningRate]

lemma mainRevealRate_lt_one : mainRevealRate < 1 := by
  norm_num [mainRevealRate, thinningRate]

lemma mainRevealRate_complement :
    1 - mainRevealRate = tripleWeight thinningRate (false, false, false) := by
  simp [mainRevealRate, tripleWeight]
  ring

lemma tripleRevealed_eq_false (x : MaskTriple) :
    tripleRevealed x = false ↔ x = (false, false, false) := by
  rcases x with ⟨h,d,c⟩
  cases h <;> cases d <;> cases c <;> decide

lemma conditionalTripleWeight_nonneg (b : Bool) (x : MaskTriple) :
    0 ≤ conditionalTripleWeight b x := by
  have ht0 : 0 ≤ thinningRate := constants_positive.2.2.1.le
  have ht1 : thinningRate ≤ 1 := by norm_num [thinningRate]
  unfold conditionalTripleWeight
  split_ifs
  · exact div_nonneg (tripleWeight_nonneg ht0 ht1 x) mainRevealRate_pos.le
  · norm_num
  · norm_num
  · norm_num

lemma conditionalTripleWeight_sum (b : Bool) :
    (∑ x : MaskTriple, conditionalTripleWeight b x) = 1 := by
  cases b
  · simp [conditionalTripleWeight]
  · simp [MaskTriple, Fintype.sum_prod_type,
      conditionalTripleWeight, tripleRevealed, tripleWeight]
    field_simp [ne_of_gt mainRevealRate_pos]
    simp [mainRevealRate]
    ring

lemma conditionalTripleWeight_support (b : Bool) (x : MaskTriple)
    (h : tripleRevealed x ≠ b) : conditionalTripleWeight b x = 0 := by
  rcases x with ⟨x,y,z⟩
  cases b <;> cases x <;> cases y <;> cases z <;>
    simp_all [conditionalTripleWeight, tripleRevealed]

/-- Multiplying the explicit conditional kernel by the observed-bit law
recovers the original joint law, not just a marginal event probability. -/
lemma conditionalTripleWeight_joint (b : Bool) (x : MaskTriple) :
    revealBitWeight b * conditionalTripleWeight b x =
      if tripleRevealed x = b then tripleWeight thinningRate x else 0 := by
  rcases x with ⟨x,y,z⟩
  cases b <;> cases x <;> cases y <;> cases z <;>
    simp [revealBitWeight, conditionalTripleWeight, tripleRevealed,
      mainRevealRate_complement] <;>
    field_simp [ne_of_gt mainRevealRate_pos]

lemma conditionalTripleWeight_reconstruct (x : MaskTriple) :
    (∑ b : Bool, revealBitWeight b * conditionalTripleWeight b x) =
      tripleWeight thinningRate x := by
  simp only [conditionalTripleWeight_joint, Fintype.sum_bool]
  cases h : tripleRevealed x <;> simp

lemma revealBitWeight_pos (b : Bool) : 0 < revealBitWeight b := by
  cases b
  · exact sub_pos.mpr mainRevealRate_lt_one
  · exact mainRevealRate_pos

lemma revealBitWeight_sum : (∑ b : Bool, revealBitWeight b) = 1 := by
  simp [revealBitWeight]

lemma tripleWeight_source_pos (x : MaskTriple) :
    0 < tripleWeight thinningRate x := by
  rcases x with ⟨h,d,c⟩
  cases d <;> cases c <;> norm_num [tripleWeight, thinningRate]

/-- Exactly seven triples are compatible with an observed label. -/
lemma card_revealed_triples :
    Fintype.card {x : MaskTriple // tripleRevealed x = true} = 7 := by decide

lemma conditionalTripleWeight_pos_iff (b : Bool) (x : MaskTriple) :
    0 < conditionalTripleWeight b x ↔ tripleRevealed x = b := by
  constructor
  · intro hx
    by_contra h
    rw [conditionalTripleWeight_support b x h] at hx
    exact (lt_irrefl (0 : ℝ)) hx
  · intro hx
    have h := conditionalTripleWeight_joint b x
    rw [ite_eq_left hx] at h
    have hp : 0 < revealBitWeight b * conditionalTripleWeight b x := by
      rw [h]
      exact tripleWeight_source_pos x
    exact (mul_pos_iff_of_pos_left (revealBitWeight_pos b)).mp hp

end MatroidProphet.Secretary

end OAI
