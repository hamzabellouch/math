import OAI.Probability.MatroidProphet.Pivots.Arbitrary
import OAI.Probability.MatroidProphet.Pivots.Encoding
import OAI.Probability.MatroidProphet.Pivots.OccurrenceSupport
import OAI.Probability.MatroidProphet.Pivots.Scores
import OAI.Probability.MatroidProphet.Pivots.Sign
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace OAI

namespace MatroidProphet
namespace Pivots

open Set Finset
open scoped BigOperators

variable {α : Type*} [Fintype α] {r q n : ℕ}

def occurrenceMark (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) :
    Occurrence r q → Bool := Sum.elim oldMark movableMark

noncomputable def markedScore (s : ℕ) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) (o : Occurrence r q) : ℝ :=
  if occurrenceMark oldMark movableMark o then (2 : ℝ) ^ scoreExponent s time o
  else -(2 : ℝ) ^ scoreExponent s time o

lemma abs_markedScore (s : ℕ) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) (o : Occurrence r q) :
    |markedScore s time oldMark movableMark o| = (2 : ℝ) ^ scoreExponent s time o := by
  unfold markedScore
  split <;> simp [abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]

noncomputable def fixedOldScore (s : ℕ) (oldMark : Fin r → Bool) (i : Fin r) : ℝ :=
  if oldMark i then (2 : ℝ)^((s+1)*(i.val+1)) else -(2 : ℝ)^((s+1)*(i.val+1))

noncomputable def constantScore (s : ℕ) (oldMark : Fin r → Bool) : Occurrence r q → ℝ :=
  Sum.elim (fixedOldScore s oldMark) (fun _ => 0)

noncomputable def coordinateScore : Occurrence r q → ((Fin q → ℝ) →ₗ[ℝ] ℝ) :=
  Sum.elim (fun _ => 0) (fun i => LinearMap.proj i)

noncomputable def patternLinear (M : Matroid α) (label : Occurrence r q → α)
    (J : Finset (Occurrence r q)) (e : α) : (Fin q → ℝ) →ₗ[ℝ] ℝ :=
  ∑ o ∈ occurrenceSupport M label J e, coordinateScore o

noncomputable def patternConstant (M : Matroid α) (label : Occurrence r q → α)
    (J : Finset (Occurrence r q)) (e : α) (s : ℕ) (oldMark : Fin r → Bool) : ℝ :=
  ∑ o ∈ occurrenceSupport M label J e, constantScore s oldMark o

lemma affineScore_eq_sum
    {α : Type u_1} [Fintype α] {r : ℕ} {q : ℕ} (M : Matroid α) (label : Occurrence r q → α)
    (J : Finset (Occurrence r q)) (e : α) (s : ℕ) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) :
    patternLinear M label J e (fun i => markedScore s time oldMark movableMark (Sum.inr i)) +
      patternConstant M label J e s oldMark =
      ∑ o ∈ occurrenceSupport M label J e, markedScore s time oldMark movableMark o := by
  simp only [patternLinear, patternConstant, LinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o _
  cases o <;> simp [coordinateScore, constantScore, fixedOldScore, markedScore,
    occurrenceMark, scoreExponent]
  all_goals rfl

def RecordsPivots (M : Matroid α) (label : Occurrence r q → α)
    (test : Fin n → α) (time : Occurrence r q → ℕ)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool) (t : Finset (Fin n)) : Prop :=
  ∀ f, ∃ o, IsPivot M label time (test f) o ∧
    (occurrenceMark oldMark movableMark o = true ↔ f ∈ t)

lemma recordsPivots_affine (M : Matroid α) (b : ℕ → α) (a : Fin q → α)
    (test : Fin n → α) (s : ℕ) (hqs : q ≤ s)
    (oldMark : Fin r → Bool) (movableMark : Fin q → Bool)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time) (htime : Function.Injective time)
    (hground : ∀ o : Occurrence r q, occurrenceLabel b a o ∈ M.E) (t : Finset (Fin n))
    (hrecords : RecordsPivots M (occurrenceLabel b a) test time oldMark movableMark t) :
    ∃ x, RealizesSigns
      (fun f => patternLinear M (occurrenceLabel b a) (retained M b a time) (test f))
      (fun f => patternConstant M (occurrenceLabel b a) (retained M b a time) (test f) s oldMark)
      t x := by
  classical
  let label : Occurrence r q → α := occurrenceLabel b a
  let J := retained M b a time
  let w := markedScore s time oldMark movableMark
  let exponent := scoreExponent s time
  refine ⟨fun i => w (Sum.inr i), ?_⟩
  intro f
  rw [affineScore_eq_sum]
  obtain ⟨o, hpivot, hmark⟩ := hrecords f
  have hp := pivot_mem_support_and_max M label time hground htime hpivot
  change o ∈ occurrenceSupport M label J (test f) ∧
    (∀ p ∈ occurrenceSupport M label J (test f), time p ≤ time o) at hp
  have hmax : ∀ p ∈ occurrenceSupport M label J (test f), p ≠ o → exponent p < exponent o := by
    intro p hp' hne
    apply scoreExponent_preserves_order s hqs time horder
    exact lt_of_le_of_ne (hp.2 p hp') (fun heq => hne (htime heq))
  have hexp := scoreExponent_injective s hqs time horder htime
  have habs : ∀ p ∈ occurrenceSupport M label J (test f), |w p| = 2 ^ exponent p :=
    fun p _ => abs_markedScore s time oldMark movableMark p
  have hpos := sum_positive_iff_max_exponent _ w exponent hexp hp.1 hmax habs
  have hneg := sum_positive_iff_max_exponent _ (fun p => -w p) exponent hexp hp.1 hmax
    (by intro p hp'; simpa using habs p hp')
  simp only [Finset.sum_neg_distrib, neg_pos] at hneg
  have hpow : (0 : ℝ) < 2 ^ exponent o := pow_pos (by norm_num) _
  by_cases hf : f ∈ t
  · simp only [hf, ↓reduceIte]
    apply hpos.mpr
    have hm := hmark.mpr hf
    simp [w, markedScore, hm]
  · simp only [hf, ↓reduceIte]
    apply hneg.mpr
    have hm : occurrenceMark oldMark movableMark o = false := by
      cases h : occurrenceMark oldMark movableMark o
      · rfl
      · exact False.elim (hf (hmark.mp h))
    simp [w, markedScore, hm]

end Pivots
end MatroidProphet

end OAI
