import OAI.NumberTheory.TwoPoint.Walks.WitnessPrimeSystems
import OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding

namespace OAI

/-! The actual witness selector lands in the bounded metadata universe. -/

namespace TwoPointCorrelations

open Finset

lemma internal_witness_metadata {n N h : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (R : Finset (Fin n)) (reverse : Bool)
    (selected control : R → ι) (left right : R → ℕ)
    (hleft : ∀ i, left i ≤ N) (hright : ∀ i, right i ≤ N)
    (hcontrol : ∀ i, control i ≠ selected i)
    (htriangular : ∀ i j : R, (if reverse then j.val < i.val else i.val < j.val) →
      selected j ∉ primeRelationSupport ((word i).intervalRelation h (left i) (right i)) ∧
        control i ≠ selected j)
    (value : ι → ℕ)
    (hholds : ∀ i : R, primeRelationEvent ((word i).intervalRelation h (left i) (right i))
      (selected i) (control i) (fun z => (value z : ℤ))) :
    ∃ d : WitnessSystemData n N ι, d.chosen = R ∧ d.Triangular main word h ∧
      d.Holds main word h (fun z => (value z : ℤ)) := by
  let d : WitnessSystemData n N ι := {
    mode := if reverse then 1 else 0
    chosen := R
    slot := fun i => (selected i, control i, i.val,
      ⟨left i, Nat.lt_succ_of_le (hleft i)⟩, ⟨right i, Nat.lt_succ_of_le (hright i)⟩, 0, 0) }
  refine ⟨d, rfl, ?_, ?_⟩
  · cases reverse <;> exact ⟨hcontrol, htriangular⟩
  · cases reverse <;> exact hholds

/-- Every index in the constructed metadata is bounded by the total
recorded-length bound. Thus the actual four-way selector is covered by
the finite code count, with no numerical-prime values in its code. -/
theorem witness_system_metadata {n K h s J N : ℕ} {supply : ℕ → ℕ → Prop}
    {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (value : ι → ℕ) (hinj : Function.Injective value) (hprime : ∀ j, (value j).Prime)
    (hm : main.Realizes value) (hw : ∀ i, (word i).Realizes value)
    (mark : Fin n → ι) (attachment position : Fin n → ℕ)
    (hsize : 8 * K ≤ n)
    (hminimal : ∀ i, MinimalWord (ForwardProhibited h s supply) (word i).word)
    (hsq : ∀ i t, t ∈ (word i).word → Squarefree t.tuple)
    (hcard : ∀ i t, t ∈ (word i).word → t.tuple.primeFactors.card = J)
    (hsupport : ∀ i p j, TuplePrimeAt (word i).word p j →
      ¬p ∣ h ∧ ∀ t ∈ (word i).word, ¬p ∣ t.padding)
    (hmark : ∀ i, value (mark i) ∈ wordPrimeSupport (word i).word)
    (hprivate : ∀ i j, j ≠ i → value (mark i) ∉ wordPrimeSupport (word j).word)
    (horder : Monotone attachment) (hbound : ∀ i, attachment i ≤ main.word.length)
    (hmain : ∀ i v, TuplePrimeAt main.word (value (mark i)) v → v = position i)
    (hmainLength : main.word.length ≤ N) (hwordLength : ∀ i, (word i).word.length ≤ N)
    (x : ℤ) (hpositive : ∀ i, PositiveWord h (x + wordDisplacement h
      (main.word.take (attachment i))) (word i).word) :
    ∃ d : WitnessSystemData n N ι, K ≤ d.chosen.card ∧ d.Triangular main word h ∧
      d.Holds main word h (fun z => (value z : ℤ)) := by
  classical
  obtain ⟨R, hRK, hcase⟩ := select_witness_relations (fun i => (word i).word)
    (fun i => value (mark i)) attachment position hsize hminimal hsq hcard hsupport hmark hprivate
  rcases hcase with hbefore | hafter | hearlier | hlater
  · obtain ⟨active, _, hactive, hfresh⟩ := select_fresh_before_labels (fun i => (word i).word)
      R hsq hbefore
    obtain ⟨selected, control, left, right, _, _, hd, ht⟩ :=
      select_internal_relations (fun i : R => word i) h value hinj hprime
        (fun i => hw i) (fun i => hsq i) active hactive (fun i j hij => hfresh i j hij)
    obtain ⟨d, hR, htri, hholds⟩ := internal_witness_metadata main word R false selected control left right
      (fun i : R => (hd i).2.1.trans ((hd i).2.2.1.trans (hwordLength i)))
      (fun i : R => (hd i).2.2.1.trans (hwordLength i)) (fun i : R => (hd i).1)
      ht value (fun i : R => (hd i).2.2.2)
    exact ⟨d, by simpa only [hR] using hRK, htri, hholds⟩
  · obtain ⟨active, _, hactive, hfresh⟩ := select_fresh_after_labels (fun i => (word i).word)
      R hsq hafter
    obtain ⟨selected, control, left, right, _, _, hd, ht⟩ :=
      select_internal_relations (fun i : OrderDual R => word (OrderDual.ofDual i).val) h value hinj hprime
        (fun i => hw (OrderDual.ofDual i).val) (fun i => hsq (OrderDual.ofDual i).val)
        active hactive (fun i j hij => hfresh i j hij)
    obtain ⟨d, hR, htri, hholds⟩ := internal_witness_metadata main word R true selected control left right
      (fun i : R => (hd i).2.1.trans ((hd i).2.2.1.trans (hwordLength i)))
      (fun i : R => (hd i).2.2.1.trans (hwordLength i)) (fun i : R => (hd i).1)
      ht value (fun i : R => (hd i).2.2.2)
    exact ⟨d, by simpa only [hR] using hRK, htri, hholds⟩
  · have hdata (i : R) := (hearlier i i.property).2
    choose prime ri partner hpartner _ hocc hnonzero hshared using hdata
    have hpos (i : R) := (hearlier i i.property).1
    have hex (i : R) : ∃ rj, TuplePrimeAt (word (partner i)).word (prime i) rj :=
      (mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mp (hshared i)
    choose rj hocc' using hex
    obtain ⟨control, hc, ht⟩ := select_earlier_comparison_relations main word value hinj hprime hm hw
      hsq mark attachment position horder hbound hprivate hmain x hpositive R partner hpartner
      ri rj prime hpos hocc hocc' hnonzero
    let d : WitnessSystemData n N ι := {
      mode := 2
      chosen := R
      slot := fun i => (mark i, control i, partner i,
        ⟨attachment (partner i), Nat.lt_succ_of_le ((hbound _).trans hmainLength)⟩,
        ⟨attachment i, Nat.lt_succ_of_le ((hbound _).trans hmainLength)⟩,
        ⟨ri i, Nat.lt_succ_of_le ((hocc i).index_lt.le.trans (hwordLength i))⟩,
        ⟨rj i, Nat.lt_succ_of_le ((hocc' i).index_lt.le.trans (hwordLength (partner i)))⟩) }
    refine ⟨d, hRK, ?_, ?_⟩
    · constructor
      · exact fun i => (hc i).2.1
      · intro i j hij
        apply ht i j
        with_unfolding_all exact hij
    · exact fun i => (hc i).2.2
  · have hdata (i : R) := (hlater i i.property).2
    choose prime ri partner hpartner _ hocc hnonzero hshared using hdata
    have hpos (i : R) := (hlater i i.property).1
    have hex (i : R) : ∃ rj, TuplePrimeAt (word (partner i)).word (prime i) rj :=
      (mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mp (hshared i)
    choose rj hocc' using hex
    obtain ⟨control, hc, ht⟩ := select_later_comparison_relations main word value hinj hprime hm hw
      hsq mark attachment position horder hbound hprivate hmain x hpositive R partner hpartner
      ri rj prime hpos hocc hocc' hnonzero
    let d : WitnessSystemData n N ι := {
      mode := 3
      chosen := R
      slot := fun i => (mark i, control i, partner i,
        ⟨attachment i, Nat.lt_succ_of_le ((hbound _).trans hmainLength)⟩,
        ⟨attachment (partner i), Nat.lt_succ_of_le ((hbound _).trans hmainLength)⟩,
        ⟨ri i, Nat.lt_succ_of_le ((hocc i).index_lt.le.trans (hwordLength i))⟩,
        ⟨rj i, Nat.lt_succ_of_le ((hocc' i).index_lt.le.trans (hwordLength (partner i)))⟩) }
    refine ⟨d, hRK, ?_, ?_⟩
    · constructor
      · exact fun i => (hc i).2.1
      · intro i j hij
        apply ht i j
        with_unfolding_all exact hij
    · exact fun i => (hc i).2.2

end TwoPointCorrelations

end OAI
