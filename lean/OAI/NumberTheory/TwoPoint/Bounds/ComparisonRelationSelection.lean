import OAI.NumberTheory.TwoPoint.Walks.WordRelations

namespace OAI

/-! Exact triangular comparison systems selected from positive witness words. -/

namespace TwoPointCorrelations

open Finset

/-- Earlier partners give a comparison system ordered by increasing
attachment, with the actual private labels as selected variables. -/
theorem select_earlier_comparison_relations {n h : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (value : ι → ℕ) (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hw : ∀ i, (word i).Realizes value)
    (hsq : ∀ i t, t ∈ (word i).word → Squarefree t.tuple)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ)
    (horder : Monotone attachment) (hbound : ∀ i, attachment i ≤ main.word.length)
    (hprivate : ∀ i j, j ≠ i → value (mark i) ∉ wordPrimeSupport (word j).word)
    (hmain : ∀ i v, TuplePrimeAt main.word (value (mark i)) v → v = position i)
    (x : ℤ) (hpositive : ∀ i, PositiveWord h (x + wordDisplacement h
      (main.word.take (attachment i))) (word i).word)
    (R : Finset (Fin n)) (partner : R → Fin n) (hpartner : ∀ i, partner i < i.val)
    (ri rj prime : R → ℕ) (hpos : ∀ i : R, attachment i ≤ position i)
    (hocc : ∀ i : R, TuplePrimeAt (word i).word (prime i) (ri i))
    (hocc' : ∀ i : R, TuplePrimeAt (word (partner i)).word (prime i) (rj i))
    (hnonzero : ∀ i : R, ¬(prime i : ℤ) ∣
      wordPrimeContribution h (word i).word (value (mark i)) 0 (ri i)) :
    ∃ control : R → ι,
      (∀ i : R, value (control i) = prime i ∧ control i ≠ mark i ∧
        primeRelationEvent
          (comparisonRelation main (word i) (word (partner i)) h
            (attachment (partner i)) (attachment i) (ri i) (rj i))
          (mark i) (control i) (fun z => (value z : ℤ))) ∧
      ∀ i j : R, i.val < j.val →
        mark j ∉ primeRelationSupport
          (comparisonRelation main (word i) (word (partner i)) h
            (attachment (partner i)) (attachment i) (ri i) (rj i)) ∧
          control i ≠ mark j := by
  classical
  have hc (i : R) : ∃ c : ι, value c = prime i := by
    obtain ⟨c, _, hc⟩ := (word i).occurrence_has_label value hprime (hw i) (prime i)
      ⟨ri i, (hocc i).index_lt⟩ (hocc i)
    exact ⟨c, hc⟩
  choose control hcontrol using hc
  have hshared (i : R) : ∀ k, prime i ≠ value (mark k) := by
    apply shared_prime_ne_private (fun i => (word i).word) (fun i => value (mark i)) hprivate
      (ne_of_gt (hpartner i))
    · exact (mem_wordPrimeSupport_iff _ _ (hsq i)).mpr ⟨ri i, hocc i⟩
    · exact (mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mpr ⟨rj i, hocc' i⟩
  refine ⟨control, ?_, ?_⟩
  · intro i
    refine ⟨hcontrol i, ?_, ?_⟩
    · intro heq
      exact hshared i i (by simpa only [heq] using (hcontrol i).symm)
    · apply comparisonRelation_event main (word i) (word (partner i)) h
        (attachment (partner i)) (attachment i) (ri i) (rj i) value hinj hprime hm
        (hw i) (hw (partner i)) (hbound i) (horder (hpartner i).le) x
        (mark i) (control i) (hpositive i) (hpositive (partner i))
        (by simpa only [hcontrol i] using hocc i)
        (by simpa only [hcontrol i] using hocc' i)
      rw [earlier_comparison_private_contribution main.word (fun i => (word i).word)
        (fun i => value (mark i)) attachment position hsq hprivate hmain
        (hpartner i) (hpos i) (ri i) (rj i)]
      simpa only [hcontrol i] using hnonzero i
  · intro i j hij
    have he := earlier_comparison_excludes_later (fun i => (word i).word)
      (fun i => value (mark i)) attachment position horder hprivate (hpartner i) hij (hpos j)
    constructor
    · apply comparisonRelation_not_mem main (word i) (word (partner i)) h
        (attachment (partner i)) (attachment i) (ri i) (rj i) value hinj hprime hm
        (hw i) (hw (partner i)) (mark j)
      · intro r har hri hpr
        exact he.2.2 r (mem_Ico.mpr ⟨har, hri⟩) (hmain j r hpr)
      · intro r hpr
        exact he.1 ((mem_wordPrimeSupport_iff _ _ (hsq i)).mpr ⟨r, hpr⟩)
      · intro r hpr
        exact he.2.1 ((mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mpr ⟨r, hpr⟩)
    · intro heq
      exact hshared i j (by simpa only [heq] using (hcontrol i).symm)

/-- Later partners give the same system in the reverse witness order.
The selected contribution changes sign, which preserves nondivisibility. -/
theorem select_later_comparison_relations {n h : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (value : ι → ℕ) (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hw : ∀ i, (word i).Realizes value)
    (hsq : ∀ i t, t ∈ (word i).word → Squarefree t.tuple)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ)
    (horder : Monotone attachment) (hbound : ∀ i, attachment i ≤ main.word.length)
    (hprivate : ∀ i j, j ≠ i → value (mark i) ∉ wordPrimeSupport (word j).word)
    (hmain : ∀ i v, TuplePrimeAt main.word (value (mark i)) v → v = position i)
    (x : ℤ) (hpositive : ∀ i, PositiveWord h (x + wordDisplacement h
      (main.word.take (attachment i))) (word i).word)
    (R : Finset (Fin n)) (partner : R → Fin n) (hpartner : ∀ i, i.val < partner i)
    (ri rj prime : R → ℕ) (hpos : ∀ i : R, position i < attachment i)
    (hocc : ∀ i : R, TuplePrimeAt (word i).word (prime i) (ri i))
    (hocc' : ∀ i : R, TuplePrimeAt (word (partner i)).word (prime i) (rj i))
    (hnonzero : ∀ i : R, ¬(prime i : ℤ) ∣
      wordPrimeContribution h (word i).word (value (mark i)) 0 (ri i)) :
    ∃ control : R → ι,
      (∀ i : R, value (control i) = prime i ∧ control i ≠ mark i ∧
        primeRelationEvent
          (comparisonRelation main (word (partner i)) (word i) h
            (attachment i) (attachment (partner i)) (rj i) (ri i))
          (mark i) (control i) (fun z => (value z : ℤ))) ∧
      ∀ i j : R, j.val < i.val →
        mark j ∉ primeRelationSupport
          (comparisonRelation main (word (partner i)) (word i) h
            (attachment i) (attachment (partner i)) (rj i) (ri i)) ∧
          control i ≠ mark j := by
  classical
  have hc (i : R) : ∃ c : ι, value c = prime i := by
    obtain ⟨c, _, hc⟩ := (word i).occurrence_has_label value hprime (hw i) (prime i)
      ⟨ri i, (hocc i).index_lt⟩ (hocc i)
    exact ⟨c, hc⟩
  choose control hcontrol using hc
  have hshared (i : R) : ∀ k, prime i ≠ value (mark k) := by
    apply shared_prime_ne_private (fun i => (word i).word) (fun i => value (mark i)) hprivate
      (ne_of_lt (hpartner i))
    · exact (mem_wordPrimeSupport_iff _ _ (hsq i)).mpr ⟨ri i, hocc i⟩
    · exact (mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mpr ⟨rj i, hocc' i⟩
  refine ⟨control, ?_, ?_⟩
  · intro i
    refine ⟨hcontrol i, ?_, ?_⟩
    · intro heq
      exact hshared i i (by simpa only [heq] using (hcontrol i).symm)
    · apply comparisonRelation_event main (word (partner i)) (word i) h
        (attachment i) (attachment (partner i)) (rj i) (ri i) value hinj hprime hm
        (hw (partner i)) (hw i) (hbound (partner i)) (horder (hpartner i).le) x
        (mark i) (control i) (hpositive (partner i)) (hpositive i)
        (by simpa only [hcontrol i] using hocc' i)
        (by simpa only [hcontrol i] using hocc i)
      rw [later_comparison_private_contribution main.word (fun i => (word i).word)
        (fun i => value (mark i)) attachment position hsq hprivate hmain
        (hpartner i) (hpos i) (ri i) (rj i)]
      rw [dvd_neg]
      simpa only [hcontrol i] using hnonzero i
  · intro i j hji
    have he := later_comparison_excludes_earlier (fun i => (word i).word)
      (fun i => value (mark i)) attachment position horder hprivate (hpartner i) hji (hpos j)
    constructor
    · apply comparisonRelation_not_mem main (word (partner i)) (word i) h
        (attachment i) (attachment (partner i)) (rj i) (ri i) value hinj hprime hm
        (hw (partner i)) (hw i) (mark j)
      · intro r har hri hpr
        exact he.2.2 r (mem_Ico.mpr ⟨har, hri⟩) (hmain j r hpr)
      · intro r hpr
        exact he.2.1 ((mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mpr ⟨r, hpr⟩)
      · intro r hpr
        exact he.1 ((mem_wordPrimeSupport_iff _ _ (hsq i)).mpr ⟨r, hpr⟩)
    · intro heq
      exact hshared i j (by simpa only [heq] using (hcontrol i).symm)

end TwoPointCorrelations

end OAI
