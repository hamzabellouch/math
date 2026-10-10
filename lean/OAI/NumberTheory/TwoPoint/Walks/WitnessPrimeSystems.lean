import OAI.NumberTheory.TwoPoint.Bounds.InternalRelationSelection
import OAI.NumberTheory.TwoPoint.Bounds.ComparisonRelationSelection
import OAI.NumberTheory.TwoPoint.Bounds.OrderedPrimeSystems

namespace OAI

/-! Assemble the four witness alternatives into one ordered congruence system. -/

namespace TwoPointCorrelations

open Finset

/-- Bundle an actual fresh-active family into the finite system used by
reciprocal elimination. -/
theorem internal_prime_system {κ : Type} [Fintype κ] [LinearOrder κ]
    {ι : Type*} [DecidableEq ι] (word : κ → LabeledPrimeWord ι)
    (h : ℕ) (value : ι → ℕ) (hinj : Function.Injective value)
    (hprime : ∀ j, (value j).Prime) (hw : ∀ i, (word i).Realizes value)
    (hsq : ∀ i t, t ∈ (word i).word → Squarefree t.tuple)
    (active : κ → ℕ) (hactive : ∀ i, ActivePrime h (word i).word (active i))
    (hfresh : ∀ i j, i < j → active j ∉ wordPrimeSupport (word i).word) :
    ∃ S : OrderedPrimeSystem ι, S.size = Fintype.card κ ∧
      S.Holds (fun z => (value z : ℤ)) := by
  obtain ⟨selected, control, left, right, _, _, hdata, htriangular⟩ :=
    select_internal_relations word h value hinj hprime hw hsq active hactive hfresh
  let S : OrderedPrimeSystem ι := {
    Index := κ
    indexFintype := inferInstance
    indexOrder := inferInstance
    Term := fun i => Fin (word i).word.length
    termFintype := fun _ => inferInstance
    relation := fun i => (word i).intervalRelation h (left i) (right i)
    selected := selected
    control := control
    control_ne := fun i => (hdata i).1
    triangular := htriangular }
  exact ⟨S, rfl, fun i => (hdata i).2.2.2⟩

/-- The actual four-way selection theorem. It assumes the numerical
minimality and privacy properties of the witness cover, and constructs
all congruences and their later-variable exclusions inside the proof. -/
theorem witness_prime_system {n K h s J : ℕ} {supply : ℕ → ℕ → Prop}
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
    (x : ℤ) (hpositive : ∀ i, PositiveWord h (x + wordDisplacement h
      (main.word.take (attachment i))) (word i).word) :
    ∃ S : OrderedPrimeSystem ι, K ≤ S.size ∧ S.Holds (fun z => (value z : ℤ)) := by
  classical
  obtain ⟨R, hRK, hcase⟩ := select_witness_relations (fun i => (word i).word)
    (fun i => value (mark i)) attachment position hsize hminimal hsq hcard hsupport hmark hprivate
  rcases hcase with hbefore | hafter | hearlier | hlater
  · obtain ⟨active, _, hactive, hfresh⟩ := select_fresh_before_labels (fun i => (word i).word)
      R hsq hbefore
    obtain ⟨S, hS, hholds⟩ := internal_prime_system (fun i : R => word i) h value hinj hprime
      (fun i => hw i) (fun i => hsq i) active hactive (fun i j hij => hfresh i j hij)
    exact ⟨S, by simpa only [hS, Fintype.card_coe] using hRK, hholds⟩
  · obtain ⟨active, _, hactive, hfresh⟩ := select_fresh_after_labels (fun i => (word i).word)
      R hsq hafter
    obtain ⟨S, hS, hholds⟩ := internal_prime_system (fun i : OrderDual R => word (OrderDual.ofDual i).val) h value hinj hprime
      (fun i => hw (OrderDual.ofDual i).val) (fun i => hsq (OrderDual.ofDual i).val) active hactive (fun i j hij => hfresh i j hij)
    exact ⟨S, by simpa only [hS, Fintype.card_orderDual, Fintype.card_coe] using hRK, hholds⟩
  · have hdata (i : R) := (hearlier i i.property).2
    choose prime ri partner hpartner _ hocc hnonzero hshared using hdata
    have hpos (i : R) := (hearlier i i.property).1
    have hex (i : R) : ∃ rj, TuplePrimeAt (word (partner i)).word (prime i) rj :=
      (mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mp (hshared i)
    choose rj hocc' using hex
    obtain ⟨control, hc, ht⟩ := select_earlier_comparison_relations main word value hinj hprime hm hw
      hsq mark attachment position horder hbound hprivate hmain x hpositive R partner hpartner
      ri rj prime hpos hocc hocc' hnonzero
    let S : OrderedPrimeSystem ι := {
      Index := R
      indexFintype := inferInstance
      indexOrder := inferInstance
      Term := fun i => Fin main.word.length ⊕
        (Fin (word i).word.length ⊕ Fin (word (partner i)).word.length)
      termFintype := fun _ => inferInstance
      relation := fun i => comparisonRelation main (word i) (word (partner i)) h
        (attachment (partner i)) (attachment i) (ri i) (rj i)
      selected := fun i => mark i
      control := control
      control_ne := fun i => (hc i).2.1
      triangular := ht }
    exact ⟨S, by simpa only [S, OrderedPrimeSystem.size, Fintype.card_coe] using hRK,
      fun i => (hc i).2.2⟩
  · have hdata (i : R) := (hlater i i.property).2
    choose prime ri partner hpartner _ hocc hnonzero hshared using hdata
    have hpos (i : R) := (hlater i i.property).1
    have hex (i : R) : ∃ rj, TuplePrimeAt (word (partner i)).word (prime i) rj :=
      (mem_wordPrimeSupport_iff _ _ (hsq (partner i))).mp (hshared i)
    choose rj hocc' using hex
    obtain ⟨control, hc, ht⟩ := select_later_comparison_relations main word value hinj hprime hm hw
      hsq mark attachment position horder hbound hprivate hmain x hpositive R partner hpartner
      ri rj prime hpos hocc hocc' hnonzero
    let S : OrderedPrimeSystem ι := {
      Index := OrderDual R
      indexFintype := inferInstance
      indexOrder := inferInstance
      Term := fun i => Fin main.word.length ⊕
        (Fin (word (partner (OrderDual.ofDual i))).word.length ⊕ Fin (word (OrderDual.ofDual i).val).word.length)
      termFintype := fun _ => inferInstance
      relation := fun i => comparisonRelation main (word (partner (OrderDual.ofDual i))) (word (OrderDual.ofDual i).val) h
        (attachment (OrderDual.ofDual i).val) (attachment (partner (OrderDual.ofDual i))) (rj (OrderDual.ofDual i)) (ri (OrderDual.ofDual i))
      selected := fun i => mark (OrderDual.ofDual i).val
      control := fun i => control (OrderDual.ofDual i)
      control_ne := fun i => (hc (OrderDual.ofDual i)).2.1
      triangular := fun i j hij => ht (OrderDual.ofDual i) (OrderDual.ofDual j) hij }
    exact ⟨S, by simpa only [S, OrderedPrimeSystem.size, Fintype.card_orderDual, Fintype.card_coe] using hRK,
      fun i => (hc i).2.2⟩

end TwoPointCorrelations

end OAI
