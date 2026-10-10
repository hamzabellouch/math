import OAI.NumberTheory.TwoPoint.Bounds.AmbientTupleLabels
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedDensity
import OAI.NumberTheory.TwoPoint.Bounds.MainPaddingTests

namespace OAI

/-! The literal supplied tuple words discharge the ambient support and padding-test hypotheses. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma columnTupleWord_pairs {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs) :
    ∀ a ∈ columnTupleWord w forward padding, (a.tuple, a.padding) ∈ data.pairs := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact hpairs i

lemma ProhibitedPrimeFamily.supplied_word_support_subset {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (word : List SignedStep)
    (hpairs : ∀ a ∈ word, (a.tuple, a.padding) ∈ data.pairs) :
    wordDivisorPrimeSupport word ⊆ data.P ∪ data.Q := by
  intro p hp
  obtain ⟨a, ha, hpa⟩ := mem_biUnion.mp hp
  have hpair := hpairs a (List.mem_toFinset.mp ha)
  rw [Nat.primeFactors_mul (data.padding_squarefree _ hpair).ne_zero
    (data.tuple_squarefree _ hpair).ne_zero, mem_union] at hpa
  rcases hpa with hp | hp
  · exact mem_union_right _ (data.padding_pool _ hpair hp)
  · exact mem_union_left _ (data.tuple_pool _ hpair hp)

lemma supplied_tuple_support {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (padding : Fin R → ℕ) (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    tuplePrimeSupport w ⊆ data.P ∧ paddingPrimeSupport padding ⊆ data.Q := by
  constructor
  · intro p hp
    obtain ⟨j, i, rfl⟩ := (mem_tuplePrimeSupport w p).mp hp
    apply data.tuple_pool _ (hpairs i)
    rw [columnTuple_primeFactors w i hprime hdisjoint]
    exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
  · intro p hp
    obtain ⟨i, _, hp⟩ := mem_biUnion.mp hp
    exact data.padding_pool _ (hpairs i) hp

lemma supplied_tuple_padding_disjoint {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (padding : Fin R → ℕ) (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Disjoint (tuplePrimeSupport w) (paddingPrimeSupport padding) := by
  have hs := supplied_tuple_support data w padding hpairs hprime hdisjoint
  exact data.disjoint.mono hs.1 hs.2

lemma supplied_tuple_label_pool {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (padding : Fin R → ℕ) (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val) :
    ∀ i ∈ univ.image label, i.val ∈ data.P := by
  intro i hi
  apply (supplied_tuple_support data w padding hpairs hprime hdisjoint).1
  exact (tuple_label_support w Subtype.val Subtype.val_injective label hlabel i).mp hi

lemma supplied_tuple_label_seen {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val) :
    ∀ i ∈ univ.image label, i.val ∈ wordDivisorPrimeSupport (columnTupleWord w forward padding) := by
  intro i hi
  rw [tupleWord_primeSupport w forward padding hprime hdisjoint
    (fun i => (data.padding_squarefree _ (hpairs i)).ne_zero)]
  exact mem_union_left _ ((tuple_label_support w Subtype.val Subtype.val_injective label hlabel i).mp hi)

lemma supplied_tuple_label_cover {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val) :
    ∀ (k : Fin (columnTupleWord w forward padding).length) (p : ↥(data.P ∪ data.Q)),
      p.val ∈ ((columnTupleWord w forward padding).get k).tuple.primeFactors →
        p ∈ univ.image label := by
  intro k p hp
  have hk : k.val < R := by simpa only [columnTupleWord, List.length_ofFn] using k.isLt
  let i : Fin R := ⟨k.val, hk⟩
  have hi : ((columnTupleWord w forward padding).get k).tuple = columnTuple w i := by
    change ((List.ofFn (fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)))[k.val]).tuple = _
    simp only [List.getElem_ofFn]
    rfl
  rw [hi, columnTuple_primeFactors w i hprime hdisjoint] at hp
  obtain ⟨j, _, hj⟩ := mem_image.mp hp
  exact mem_image.mpr ⟨(i, j), mem_univ _, Subtype.ext ((hlabel i j).trans hj)⟩

theorem supplied_tuple_padding_retained {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (x : ↥(data.P ∪ data.Q) → Fin B)
    (hx : MainPaddingTests Subtype.val h B (columnTupleWord w forward padding) x) :
    RetainedMainTests Subtype.val (univ.image label) h B (columnTupleWord w forward padding) x := by
  apply mainPaddingTests_retained Subtype.val (univ.image label) h B
    (columnTupleWord w forward padding) x
    (fun a ha => (data.padding_squarefree _
      (columnTupleWord_pairs data w forward padding hpairs a ha)).ne_zero)
    (fun a ha => (data.tuple_squarefree _
      (columnTupleWord_pairs data w forward padding hpairs a ha)).ne_zero)
    (supplied_tuple_label_cover data w forward padding hprime hdisjoint label hlabel) hx

end TwoPointCorrelations

end OAI
