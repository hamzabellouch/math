import OAI.NumberTheory.TwoPoint.Bounds.SuppliedTupleWords

namespace OAI

/-! Prime-slot coverage for the numerical words in the trace catalog. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma ofFn_step_get {R : ℕ} (step : Fin R → SignedStep) (k : Fin (List.ofFn step).length) :
    (List.ofFn step).get k = step ⟨k.val, by simpa only [List.length_ofFn] using k.isLt⟩ := by
  change (List.ofFn step)[k.val] = _
  simp only [List.getElem_ofFn]

lemma numerical_label_cover {h J M R : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i, (step i).tuple.primeFactors = univ.image (fun j => (label (i, j)).val)) :
    ∀ k : Fin (List.ofFn step).length, ∀ p : ↥(data.P ∪ data.Q),
      p.val ∈ ((List.ofFn step).get k).tuple.primeFactors → p ∈ univ.image label := by
  intro k p hp
  rw [ofFn_step_get, hlabel] at hp
  obtain ⟨j, _, hj⟩ := mem_image.mp hp
  exact mem_image.mpr ⟨(_, j), mem_univ _, Subtype.ext hj⟩

lemma numerical_label_pool {h J M R : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hpairs : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs)
    (hlabel : ∀ i, (step i).tuple.primeFactors = univ.image (fun j => (label (i, j)).val)) :
    ∀ p ∈ univ.image label, p.val ∈ data.P := by
  intro p hp
  obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_image.mp hp
  apply data.tuple_pool _ (hpairs i)
  rw [hlabel]
  exact mem_image.mpr ⟨j, mem_univ _, rfl⟩

lemma numerical_word_pairs {h J M R : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep)
    (hpairs : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs) :
    ∀ a ∈ List.ofFn step, (a.tuple, a.padding) ∈ data.pairs := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact hpairs i

lemma numerical_label_seen {h J M R : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hpairs : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs)
    (hlabel : ∀ i, (step i).tuple.primeFactors = univ.image (fun j => (label (i, j)).val)) :
    ∀ p ∈ univ.image label, p.val ∈ wordDivisorPrimeSupport (List.ofFn step) := by
  intro p hp
  obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_image.mp hp
  apply mem_biUnion.mpr
  refine ⟨step i, List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩), ?_⟩
  rw [Nat.primeFactors_mul (data.padding_squarefree _ (hpairs i)).ne_zero
    (data.tuple_squarefree _ (hpairs i)).ne_zero]
  apply mem_union_right
  rw [hlabel]
  exact mem_image.mpr ⟨j, mem_univ _, rfl⟩

lemma numerical_padding_retained {h J M R B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hpairs : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs)
    (hlabel : ∀ i, (step i).tuple.primeFactors = univ.image (fun j => (label (i, j)).val))
    (x : ↥(data.P ∪ data.Q) → Fin B)
    (hx : MainPaddingTests Subtype.val h B (List.ofFn step) x) :
    RetainedMainTests Subtype.val (univ.image label) h B (List.ofFn step) x := by
  apply mainPaddingTests_retained Subtype.val _ h B (List.ofFn step) x
    (fun a ha => (data.padding_squarefree _ (numerical_word_pairs data step hpairs a ha)).ne_zero)
    (fun a ha => (data.tuple_squarefree _ (numerical_word_pairs data step hpairs a ha)).ne_zero)
    (numerical_label_cover data step label hlabel) hx

lemma numerical_singleton_position {h J M R : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hpairs : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs)
    (hlabel : ∀ i, (step i).tuple.primeFactors = univ.image (fun j => (label (i, j)).val))
    (c : singletonLabels label) (v : ℕ)
    (hv : TuplePrimeAt (List.ofFn step) c.val.val v) :
    v = (singletonRepresentative label c).1.val := by
  have hvR : v < R := by simpa only [List.length_ofFn] using hv.index_lt
  let i : Fin R := ⟨v, hvR⟩
  have hd := ((tuplePrimeAt_iff_getElem _ _ _ hv.index_lt).mp hv).2
  have hd' : c.val.val ∣ (step i).tuple := by
    simpa only [List.getElem_ofFn] using hd
  have hm : c.val.val ∈ (step i).tuple.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hv.1, hd', (data.tuple_squarefree _ (hpairs i)).ne_zero⟩
  rw [hlabel] at hm
  obtain ⟨j, _, hj⟩ := mem_image.mp hm
  have he : label (i, j) = c.val := Subtype.ext hj
  exact congrArg (fun t : Fin R × Fin J => t.1.val)
    (singleton_occurrence_unique label c (i, j) he)

end TwoPointCorrelations

end OAI
