import OAI.NumberTheory.Jacobsthal.Primes.ReferenceSourcePrimeSets

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferenceEulerRecurrence

open _root_.Finset
open ReferencePruning ReferencePrefixRecurrence ReferenceCutoffRecurrence
open ReferenceSourcePrimeSets ReferenceProductsBasics ReferenceMertens ReferenceAdmission
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

lemma signedWeight_cons (p : ℕ) (ps : List ℕ) :
    signedWeight (p::ps)=(-(p:ℝ)⁻¹)*signedWeight ps := by
  simp only [signedWeight,List.length_cons,pow_succ,prefixWeight,List.map_cons,List.prod_cons]
  ring

theorem survivor_first_recurrence (P : Finset ℕ) :
    survivorProduct P=1-∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct (P.filter (fun q => q<p)) := by
  have h := sum_decreasing_by_first P signedWeight
  rw [sum_signedWeight] at h
  have hnil : signedWeight []=1 := by simp [signedWeight,prefixWeight]
  rw [hnil] at h
  have hs : (∑ p ∈ P,∑ ps ∈ decreasingPrefixes (P.filter (fun q => q<p)),signedWeight (p::ps))=
      -(∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct (P.filter (fun q => q<p))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    simp_rw [signedWeight_cons]
    rw [← Finset.mul_sum,sum_signedWeight]
    ring
  rw [hs] at h
  linarith

theorem survivor_cutoff_recurrence {P Q : Finset ℕ} (h : Above P Q) :
    survivorProduct (P∪Q)=survivorProduct Q-
      ∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct ((P.filter (fun q => q<p))∪Q) := by
  have hf := survivor_first_recurrence (P∪Q)
  have hl := survivor_first_recurrence Q
  rw [Finset.sum_union (above_disjoint h)] at hf
  have hhi : (∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct ((P∪Q).filter (fun q => q<p)))=
      ∑ p ∈ P,(p:ℝ)⁻¹*survivorProduct ((P.filter (fun q => q<p))∪Q) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_high h hp]
  have hlo : (∑ p ∈ Q,(p:ℝ)⁻¹*survivorProduct ((P∪Q).filter (fun q => q<p)))=
      ∑ p ∈ Q,(p:ℝ)⁻¹*survivorProduct (Q.filter (fun q => q<p)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [union_filter_at_low h hp]
  rw [hhi,hlo] at hf
  linarith

theorem referenceProduct_eq_survivor (w b : ℝ) (closed : Bool) :
    referenceProduct w b closed=survivorProduct (sourcePrimes w b closed) := rfl

theorem highPrimes_at_selected {w b : ℝ} (hw : 1 < w) (closed : Bool) {p : ℕ}
    (hp : p ∈ sourcePrimes w b closed) :
    highPrimes w (primeExponent w p) false=(highPrimes w b closed).filter (fun q => q<p) := by
  ext q
  simp only [highPrimes,Finset.mem_filter,sourcePrimes_at_selected hw closed hp]
  tauto

theorem actual_product_cutoff_identity {w b : ℝ} (hw : 1 < w) (hb : 2 < b) (closed : Bool) :
    referenceProduct w b closed=referenceProduct w 2 true-
      ∑ p ∈ highPrimes w b closed,(p:ℝ)⁻¹*referenceProduct w (primeExponent w p) false := by
  have hsep := highPrimes_above_boundary (b:=b) hw closed
  have hr := survivor_cutoff_recurrence hsep
  have hpart := sourcePrimes_partition hw hb closed
  rw [← hpart] at hr
  have hbase : survivorProduct (boundaryPrimes w)=referenceProduct w 2 true := by
    rw [referenceProduct_eq_survivor,sourcePrimes_boundary]
  rw [hbase] at hr
  change referenceProduct w b closed=referenceProduct w 2 true-
    (∑ p ∈ highPrimes w b closed,(p:ℝ)⁻¹*survivorProduct (((highPrimes w b closed).filter (fun q => q<p))∪boundaryPrimes w)) at hr
  rw [hr]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpS : p ∈ sourcePrimes w b closed := (Finset.mem_filter.mp hp).1
  have hchild := sourcePrimes_at_selected hw closed hpS
  rw [hpart,union_filter_at_high hsep hp] at hchild
  rw [referenceProduct_eq_survivor,hchild]

end NumberTheoryLean.ReferenceEulerRecurrence

end

end Erdos970

end OAI
