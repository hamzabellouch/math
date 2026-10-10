import OAI.NumberTheory.TwoPoint.Walks.ClosedVertexMask
import OAI.NumberTheory.TwoPoint.Bounds.PrimeResidueLift
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedTraceTerms
import OAI.NumberTheory.TwoPoint.Bounds.SuppliedTupleWords

namespace OAI

/-! Exact identification of a masked closed matrix word with the literal
centered word average.  No arithmetic or probabilistic estimate is assumed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma centeredTuple_column {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) :
    centeredTuple (columnTuple w i).primeFactors n =
      ∏ j, ((if ((w j i).val : ℤ) ∣ n then (1 : ℝ) else 0) - ((w j i).val : ℝ)⁻¹) := by
  unfold centeredTuple
  rw [columnTuple_primeFactors w i hprime hdisjoint, prod_image]
  exact fun _ _ _ _ he => selectedPrimeValues_injective (fun j => w j i) hdisjoint he

theorem lifted_tuple_center_product {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    scalarWalkProduct h (fun t n => centeredTuple t.tuple.primeFactors n)
      (data.residueOrigin x) (columnTupleWord w forward padding) =
      ∏ t : Fin R × Fin J,
        ((if ((label t).val : ℤ) ∣ (x (label t)).val +
            wordDisplacement h ((columnTupleWord w forward padding).take t.1.val)
          then (1 : ℝ) else 0) - ((label t).val : ℝ)⁻¹) := by
  simp only [columnTupleWord]
  rw [scalarWalkProduct_ofFn, Fintype.prod_prod_type]
  apply prod_congr rfl
  intro i _
  rw [centeredTuple_column w i hprime hdisjoint]
  apply prod_congr rfl
  intro j _
  rw [← hlabel i j]
  simp only [data.residueOrigin_divisibility]
  rfl

theorem lifted_catalog_mask_product {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s D : ℕ) (step : Fin R → SignedStep)
    (hR : 0 < R) (hRD : R ≤ D) (hclosed : wordDisplacement h (List.ofFn step) = 0)
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    scalarWalkProduct h (fun _ n =>
      if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then (0 : ℝ) else 1)
      (data.residueOrigin x) (List.ofFn step) =
      attachedCatalogAvoidance data s B D (List.ofFn step) x := by
  rw [scalarWalkProduct_ofFn]
  have hc := attachedCatalogAvoidance_eq_departure_product data s B D (List.ofFn step)
    (by simpa only [List.length_ofFn] using hRD)
    (by simpa only [List.length_ofFn] using hR) hclosed x (data.residueOrigin x)
    (data.residueOrigin_spec x)
  apply Eq.trans _ hc.symm
  apply Fintype.prod_equiv (finCongr (List.length_ofFn (f := step))).symm
  intro i
  rfl

theorem closed_masked_word_eq_centered_product {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (s D : ℕ) (hR : 0 < R) (hRD : R ≤ D)
    (hclosed : wordDisplacement h (columnTupleWord w forward padding) = 0)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : SignedStep → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : SignedStep → ℤ → Prop)
    (hg : ∀ n, g n ≠ 0) (x : ↥(data.P ∪ data.Q) → Fin B) :
    let mask := fun n => if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n
      then (0 : ℝ) else 1
    scalarWalkProduct h (fun t n => mask n *
      signedIntegerWeight Q u (eligible t) g (centeredTuple t.tuple.primeFactors)
        L K (extra t) h t n * mask (n + t.displacement h))
      (data.residueOrigin x) (columnTupleWord w forward padding) =
      data.residueValue
        (fun n => scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h)
          n (columnTupleWord w forward padding)) x *
      (∏ t : Fin R × Fin J,
        ((if ((label t).val : ℤ) ∣ (x (label t)).val +
            wordDisplacement h ((columnTupleWord w forward padding).take t.1.val)
          then (1 : ℝ) else 0) - ((label t).val : ℝ)⁻¹)) *
      attachedCatalogAvoidance data s B D (columnTupleWord w forward padding) x := by
  dsimp only
  unfold columnTupleWord
  rw [closed_masked_scalar_word hR h _ (data.residueOrigin x) hclosed _ _
    (fun n => by split_ifs <;> simp)]
  rw [closed_signed_word_factorization Q u eligible g
    (fun t n => centeredTuple t.tuple.primeFactors n) L K extra h (data.residueOrigin x)
    (List.ofFn (fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i))) hg
    (fun t q _ n => centeredTuple_padding_periodic t.tuple.primeFactors h t.tuple
      (fun p hp => (Nat.mem_primeFactors.mp hp).2.1) q n) hclosed]
  have hc := lifted_tuple_center_product data w forward padding hprime hdisjoint label hlabel x
  unfold columnTupleWord at hc
  rw [hc]
  rw [lifted_catalog_mask_product data s D _ hR hRD hclosed x]
  rfl

theorem closed_masked_word_average {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (s D : ℕ) (hR : 0 < R) (hRD : R ≤ D)
    (hclosed : wordDisplacement h (columnTupleWord w forward padding) = 0)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : SignedStep → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : SignedStep → ℤ → Prop) (hg : ∀ n, g n ≠ 0) :
    let mask := fun n => if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n
      then (0 : ℝ) else 1
    (data.residueLaw B hB).average (fun x => scalarWalkProduct h (fun t n => mask n *
      signedIntegerWeight Q u (eligible t) g (centeredTuple t.tuple.primeFactors)
        L K (extra t) h t n * mask (n + t.displacement h))
      (data.residueOrigin x) (columnTupleWord w forward padding)) =
    prohibitedCenteredAverage data hB s D (columnTupleWord w forward padding) label
      (data.residueValue (fun n => scalarWalkProduct h
        (retainedEdgeDeparture Q u eligible g L K extra h) n (columnTupleWord w forward padding))) := by
  dsimp only
  unfold prohibitedCenteredAverage
  apply congrArg (data.residueLaw B hB).average
  funext x
  exact closed_masked_word_eq_centered_product data w forward padding hprime hdisjoint
    label hlabel s D hR hRD hclosed Q u eligible g L K extra hg x

end TwoPointCorrelations

end OAI
