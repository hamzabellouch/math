import OAI.NumberTheory.TwoPoint.Bounds.DeletionRowSplit
import OAI.NumberTheory.TwoPoint.Bounds.VariableWindowComparison
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedRowComparison

namespace OAI

/-! The three source deletions at the actual, possibly bin-dependent,
integer sampling sites. Extra pair eligibility is retained in the rare
term and may be discarded in the two nonnegative numerical terms. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma uniformAverage_finset_sum {α ι : Type*} [Fintype α]
    (S : Finset ι) (f : ι → α → ℝ) :
    uniformAverage (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, uniformAverage (f i) := by
  unfold uniformAverage
  rw [sum_comm, sum_div]

lemma uniformAverage_prohibitedPositiveRow {α : Type*} [Fintype α] {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (D : Finset ℕ)
    (padding : ℕ → Finset ℕ) (f : α → ℤ) :
    uniformAverage (fun x => prohibitedPositiveRow data s D padding (f x)) =
      ∑ d ∈ D, ∑ q ∈ padding d, uniformAverage (fun x =>
        actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (f x) *
          if (q : ℤ) ∣ f x ∧ ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (f x)
            then 1 else 0) := by
  simp only [prohibitedPositiveRow, uniformAverage_finset_sum]

noncomputable def positiveDeletionAtom (P Q R : Finset ℕ)
    (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ) (eligible : ℤ → ℕ → ℕ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (d q : ℕ) (n : ℤ) : ℝ :=
  if eligible j d q then
    actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
      if (q : ℤ) ∣ n ∧
        (¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
          (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∨
        6 * W * d.primeFactors.card < (actualPaddingDegree P n : ℝ) ∨ bad j n)
        then 1 else 0
  else 0

lemma positiveDeletionAtom_le (P Q R : Finset ℕ) (η : ℝ) (c : ℕ → ℝ)
    (L K W : ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (j : ℤ) (d q : ℕ) (n : ℤ)
    (he : eligible j d q → actualPaddingBin η (c d) j q) :
    positiveDeletionAtom P Q R η c L K W eligible bad j d q n ≤
      paddingRejectionAtom Q d.primeFactors R (actualPaddingBin η (c d) j) L K q n +
      (if actualPaddingBin η (c d) j q then positiveDegreeCost P d.primeFactors W q n else 0) +
      (if eligible j d q then actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
        (if (q : ℤ) ∣ n ∧ bad j n then 1 else 0) else 0) := by
  have hw := mul_nonneg (actualPaddingCoefficient_nonneg q) (positivePrimeWeight_nonneg d.primeFactors n)
  by_cases h : eligible j d q
  · have hb := he h
    simp only [positiveDeletionAtom, h, hb, paddingRejectionAtom, positiveDegreeCost, ite_true]
    simpa using weighted_three_deletions _ hw ((q : ℤ) ∣ n)
      (¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n)
      (6 * W * d.primeFactors.card < (actualPaddingDegree P n : ℝ)) (bad j n)
  · simp only [positiveDeletionAtom, h, ite_false, add_zero]
    unfold paddingRejectionAtom positiveDegreeCost
    split_ifs <;> positivity

lemma variable_source_deletion_split (P Q D R : Finset ℕ) (bins : Finset ℤ)
    (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (he : ∀ j ∈ bins, ∀ d ∈ D, ∀ q ∈ R,
      eligible j d q → actualPaddingBin η (c d) j q)
    (site : ℤ) (a N : ℤ → ℕ) :
    (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, uniformAverage (fun x : Fin (N j) =>
      positiveDeletionAtom P Q R η c L K W eligible bad j d q ((a j + x.val : ℤ) + site))) ≤
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, uniformAverage (fun x : Fin (N j) =>
        paddingRejectionAtom Q d.primeFactors R (actualPaddingBin η (c d) j) L K q
          ((a j + x.val : ℤ) + site))) +
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (actualPaddingBin η (c d) j),
        uniformAverage (fun x : Fin (N j) =>
          positiveDegreeCost P d.primeFactors W q ((a j + x.val : ℤ) + site))) +
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (eligible j d),
        uniformAverage (fun x : Fin (N j) =>
          actualPaddingCoefficient q * positivePrimeWeight d.primeFactors ((a j + x.val : ℤ) + site) *
            if (q : ℤ) ∣ ((a j + x.val : ℤ) + site) ∧ bad j ((a j + x.val : ℤ) + site)
              then 1 else 0)) := by
  have hi (j : ℤ) (pred : Prop) (f : Fin (N j) → ℝ) :
      uniformAverage (fun x => if pred then f x else 0) =
        if pred then uniformAverage f else 0 := by
    by_cases hp : pred <;> simp only [hp, ite_true, ite_false]
    simp only [uniformAverage, sum_const_zero, zero_div]
  have hs (j : ℤ) (hj : j ∈ bins) (d : ℕ) (hd : d ∈ D) (q : ℕ) (hq : q ∈ R) :=
    uniformAverage_mono (fun x : Fin (N j) =>
      positiveDeletionAtom_le P Q R η c L K W eligible bad j d q
        ((a j + x.val : ℤ) + site) (he j hj d hd q hq))
  have hadd (j : ℤ) (f g k : Fin (N j) → ℝ) :
      uniformAverage (fun x => f x + g x + k x) =
        uniformAverage f + uniformAverage g + uniformAverage k := by
    simp only [uniformAverage, sum_add_distrib, add_div]
  simp only [hadd, hi] at hs
  have hs' := sum_le_sum (fun j hj => sum_le_sum (fun d hd =>
    sum_le_sum (fun q hq => hs j hj d hd q hq)))
  simp only [sum_add_distrib] at hs'
  simpa only [sum_filter] using hs'

lemma shifted_source_deletion_split (P Q D R : Finset ℕ) (bins : Finset ℤ)
    (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (he : ∀ j ∈ bins, ∀ d ∈ D, ∀ q ∈ R,
      eligible j d q → actualPaddingBin η (c d) j q)
    (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ) :
    (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, uniformAverage (fun x : Fin (N j) =>
      positiveDeletionAtom P Q R η c L K W eligible bad j d q ((a j + x.val : ℤ) + site j d q))) ≤
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, uniformAverage (fun x : Fin (N j) =>
        paddingRejectionAtom Q d.primeFactors R (actualPaddingBin η (c d) j) L K q
          ((a j + x.val : ℤ) + site j d q))) +
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (actualPaddingBin η (c d) j),
        uniformAverage (fun x : Fin (N j) =>
          positiveDegreeCost P d.primeFactors W q ((a j + x.val : ℤ) + site j d q))) +
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (eligible j d),
        uniformAverage (fun x : Fin (N j) =>
          actualPaddingCoefficient q * positivePrimeWeight d.primeFactors ((a j + x.val : ℤ) + site j d q) *
            if (q : ℤ) ∣ ((a j + x.val : ℤ) + site j d q) ∧ bad j ((a j + x.val : ℤ) + site j d q)
              then 1 else 0)) := by
  have hi (j : ℤ) (pred : Prop) (f : Fin (N j) → ℝ) :
      uniformAverage (fun x => if pred then f x else 0) =
        if pred then uniformAverage f else 0 := by
    by_cases hp : pred <;> simp only [hp, ite_true, ite_false]
    simp only [uniformAverage, sum_const_zero, zero_div]
  have hs (j : ℤ) (hj : j ∈ bins) (d : ℕ) (hd : d ∈ D) (q : ℕ) (hq : q ∈ R) :=
    uniformAverage_mono (fun x : Fin (N j) =>
      positiveDeletionAtom_le P Q R η c L K W eligible bad j d q
        ((a j + x.val : ℤ) + site j d q) (he j hj d hd q hq))
  have hadd (j : ℤ) (f g k : Fin (N j) → ℝ) :
      uniformAverage (fun x => f x + g x + k x) =
        uniformAverage f + uniformAverage g + uniformAverage k := by
    simp only [uniformAverage, sum_add_distrib, add_div]
  simp only [hadd, hi] at hs
  have hs' := sum_le_sum (fun j hj => sum_le_sum (fun d hd =>
    sum_le_sum (fun q hq => hs j hj d hd q hq)))
  simp only [sum_add_distrib] at hs'
  simpa only [sum_filter] using hs'

end TwoPointCorrelations

end OAI
