import OAI.NumberTheory.TwoPoint.Walks.WordRelations
import OAI.NumberTheory.TwoPoint.Bounds.OrderedElimination

namespace OAI

/-! Actual active witness intervals give a triangular system on the ambient labels. -/

namespace TwoPointCorrelations

open Finset

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]

/-- Record also an occurrence of the controlling prime. This proves that
later fresh labels cannot occur as an earlier controlling modulus. -/
theorem active_relation_with_control (w : LabeledPrimeWord ι) (h : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : w.Realizes value) (y : ι) (hy : ActivePrime h w.word (value y)) :
    ∃ c a b r, c ≠ y ∧ a ≤ b ∧ b ≤ w.word.length ∧
      TuplePrimeAt w.word (value c) r ∧
      primeRelationEvent (w.intervalRelation h a b) y c (fun j => (value j : ℤ)) := by
  obtain ⟨p, a, b, hpy, hab, hb, ⟨r, hpr⟩, hdiv, hnonzero⟩ := hy.distinct_controller
  obtain ⟨c, _, hc⟩ := w.occurrence_has_label value hprime hw p ⟨r, hpr.index_lt⟩ hpr
  refine ⟨c, a, b, r, ?_, hab, hb, ?_, ?_, ?_⟩
  · intro heq
    exact hpy (by simpa only [heq] using hc.symm)
  · simpa only [hc] using hpr
  · rw [w.intervalRelation_eval h a b value hw hb]
    change (value c : ℤ) ∣ _
    simpa only [hc] using hdiv
  · apply primeRelation_coefficient_nondegenerate
    rw [w.intervalRelation_contribution h a b value hinj hprime hw hb y]
    change ¬(value c : ℤ) ∣ _
    simpa only [hc] using hnonzero

end LabeledPrimeWord

/-- A family of active primes absent from all earlier witnesses gives
actual interval relations, ordered independently of the names of the
selected labels. The conclusion includes the controlling-prime exclusion. -/
theorem select_internal_relations {κ ι : Type*} [Fintype κ] [LinearOrder κ]
    [DecidableEq ι] (word : κ → LabeledPrimeWord ι) (h : ℕ) (value : ι → ℕ)
    (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hw : ∀ i, (word i).Realizes value)
    (hsq : ∀ i t, t ∈ (word i).word → Squarefree t.tuple)
    (active : κ → ℕ) (hactive : ∀ i, ActivePrime h (word i).word (active i))
    (hfresh : ∀ i j, i < j → active j ∉ wordPrimeSupport (word i).word) :
    ∃ selected control : κ → ι, ∃ left right : κ → ℕ,
      Function.Injective selected ∧
      (∀ i, value (selected i) = active i) ∧
      (∀ i, control i ≠ selected i ∧ left i ≤ right i ∧ right i ≤ (word i).word.length ∧
        primeRelationEvent ((word i).intervalRelation h (left i) (right i))
          (selected i) (control i) (fun j => (value j : ℤ))) ∧
      ∀ i j, i < j →
        selected j ∉ primeRelationSupport ((word i).intervalRelation h (left i) (right i)) ∧
          control i ≠ selected j := by
  classical
  have hsel (i : κ) : ∃ y : ι, value y = active i := by
    have hm := (hactive i).mem_wordPrimeSupport (hsq i)
    obtain ⟨r, hr⟩ := (mem_wordPrimeSupport_iff _ _ (hsq i)).mp hm
    obtain ⟨y, _, hy⟩ := (word i).occurrence_has_label value hprime (hw i) (active i)
      ⟨r, hr.index_lt⟩ hr
    exact ⟨y, hy⟩
  choose selected hselected using hsel
  have hrel (i : κ) := (word i).active_relation_with_control h value hinj hprime (hw i)
    (selected i) (by simpa only [hselected i] using hactive i)
  choose control left right occurrence hc hl hr hocc hevent using hrel
  refine ⟨selected, control, left, right, ?_, hselected,
    (fun i => ⟨hc i, hl i, hr i, hevent i⟩), ?_⟩
  · intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij' | hji'
    · apply hfresh i j hij'
      rw [← hselected j, ← hij, hselected i]
      exact (hactive i).mem_wordPrimeSupport (hsq i)
    · apply hfresh j i hji'
      rw [← hselected i, hij, hselected j]
      exact (hactive j).mem_wordPrimeSupport (hsq j)
  · intro i j hij
    have hnot : ∀ r, ¬TuplePrimeAt (word i).word (value (selected j)) r := by
      intro r hpr
      apply hfresh i j hij
      rw [← hselected j]
      exact (mem_wordPrimeSupport_iff _ _ (hsq i)).mpr ⟨r, hpr⟩
    refine ⟨(word i).intervalRelation_not_mem h (left i) (right i) value hinj hprime
      (hw i) (selected j) (fun r _ _ => hnot r), ?_⟩
    intro heq
    exact hnot (occurrence i) (by simpa only [← heq] using hocc i)

end TwoPointCorrelations

end OAI
