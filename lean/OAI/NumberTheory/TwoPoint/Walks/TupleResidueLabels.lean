import OAI.NumberTheory.TwoPoint.Walks.TupleWordPrimeSupport
import OAI.NumberTheory.TwoPoint.Walks.WeightedWordEnvelope
import OAI.NumberTheory.TwoPoint.Walks.WordBlockGeometry

namespace OAI

/-! Recover singleton positions and tuple-coordinate support from the actual numerical word. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma tuplePrimeAt_columnTupleWord_iff {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ q ∈ P j, q.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (q v : ℕ) :
    TuplePrimeAt (columnTupleWord w forward padding) q v ↔
      ∃ i : Fin R, ∃ j : Fin J, i.val = v ∧ (w j i).val = q := by
  constructor
  · intro hq
    have hv : v < R := by simpa only [columnTupleWord, List.length_ofFn] using hq.index_lt
    have hd := ((tuplePrimeAt_iff_getElem _ q v hq.index_lt).mp hq).2
    have hd' : q ∣ columnTuple w ⟨v, hv⟩ := by
      simpa only [columnTupleWord, List.getElem_ofFn] using hd
    have hmem : q ∈ (columnTuple w ⟨v, hv⟩).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq.1, hd', (columnTuple_squarefree w _ hprime hdisjoint).ne_zero⟩
    rw [columnTuple_primeFactors w _ hprime hdisjoint] at hmem
    obtain ⟨j, _, hj⟩ := mem_image.mp hmem
    exact ⟨⟨v, hv⟩, j, rfl, hj⟩
  · rintro ⟨i, j, rfl, rfl⟩
    have hv : i.val < (columnTupleWord w forward padding).length := by
      simpa only [columnTupleWord, List.length_ofFn] using i.isLt
    apply (tuplePrimeAt_iff_getElem _ _ _ hv).mpr
    refine ⟨hprime j _ (w j i).property, ?_⟩
    have hd : (w j i).val ∣ columnTuple w i :=
      dvd_prod_of_mem (fun l => (w l i).val) (mem_univ j)
    simpa only [columnTupleWord, List.getElem_ofFn, Fin.eta] using hd

lemma tuple_label_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) (c : ι) :
    c ∈ univ.image label ↔ p c ∈ tuplePrimeSupport w := by
  rw [mem_tuplePrimeSupport]
  constructor
  · rintro hc
    obtain ⟨⟨i, j⟩, _, hc⟩ := mem_image.mp hc
    exact ⟨j, i, (hlabel i j).symm.trans (congrArg p hc)⟩
  · rintro ⟨j, i, hi⟩
    exact mem_image.mpr ⟨(i, j), mem_univ _, hinj ((hlabel i j).trans hi)⟩

lemma tuple_singleton_position {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ q ∈ P j, q.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val)
    (c : singletonLabels label) (v : ℕ)
    (hv : TuplePrimeAt (columnTupleWord w forward padding) (p c) v) :
    v = (singletonRepresentative label c).1.val := by
  obtain ⟨i, j, hi, hj⟩ :=
    (tuplePrimeAt_columnTupleWord_iff w forward padding hprime hdisjoint (p c) v).mp hv
  have he : label (i, j) = c.val := hinj ((hlabel i j).trans hj)
  have ht := singleton_occurrence_unique label c (i, j) he
  exact hi.symm.trans (congrArg (fun t : Fin R × Fin J => t.1.val) ht)

end TwoPointCorrelations

end OAI
