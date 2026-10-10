import OAI.NumberTheory.TwoPoint.Bounds.PaddingDeletionIdentity
import OAI.NumberTheory.TwoPoint.Bounds.DegreeDeletionSum

namespace OAI

/-! Deterministic union bound for the three actual source deletions.
The disjoint logarithmic bins prevent an extra bin-count loss in the
tuple-degree term. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma actualPaddingBin_sum_le (bins : Finset ℤ) (η c : ℝ) (hη : 0 < η)
    (q : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    (∑ j ∈ bins, if actualPaddingBin η c j q then w else 0) ≤ w := by
  have he (j : ℤ) : actualPaddingBin η c j q ↔ paddingBin η c (Real.log q) = j :=
    (paddingBin_eq_iff η c (Real.log q) j hη).symm
  simp only [he]
  by_cases hm : paddingBin η c (Real.log q) ∈ bins
  · simp [hm]
  · simpa [hm] using hw

lemma weighted_three_deletions (w : ℝ) (hw : 0 ≤ w) (divisor A B C : Prop) :
    w * (if divisor ∧ (A ∨ B ∨ C) then 1 else 0) ≤
      w * (if divisor ∧ A then 1 else 0) +
      w * (if divisor ∧ B then 1 else 0) +
      w * (if divisor ∧ C then 1 else 0) := by
  by_cases hd : divisor <;> by_cases ha : A <;> by_cases hb : B <;> by_cases hc : C <;>
    simp [hd, ha, hb, hc] <;> linarith

noncomputable def positiveSourceDeletion (P Q D R : Finset ℕ) (bins : Finset ℤ)
    (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ) (bad : ℤ → ℤ → Prop) (n : ℤ) : ℝ :=
  ∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R,
    if actualPaddingBin η (c d) j q then
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
        (if (q : ℤ) ∣ n ∧
          (¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
            (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∨
          6 * W * d.primeFactors.card < (actualPaddingDegree P n : ℝ) ∨ bad j n)
          then 1 else 0)
    else 0

lemma positiveSourceDeletion_split (P Q D R : Finset ℕ) (bins : Finset ℤ)
    (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ) (hη : 0 < η)
    (bad : ℤ → ℤ → Prop) (n : ℤ) :
    positiveSourceDeletion P Q D R bins η c L K W bad n ≤
      (∑ d ∈ D, positivePrimeWeight d.primeFactors n *
        paddingRejectedMass Q R bins η (c d) L K n) +
      (∑ d ∈ D, ∑ q ∈ R, positiveDegreeCost P d.primeFactors W q n) +
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (actualPaddingBin η (c d) j),
        actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
          if (q : ℤ) ∣ n ∧ bad j n then 1 else 0) := by
  let pad := fun j d q => paddingRejectionAtom Q d.primeFactors R
    (actualPaddingBin η (c d) j) L K q n
  let deg := fun j d q => if actualPaddingBin η (c d) j q then
    positiveDegreeCost P d.primeFactors W q n else 0
  let rare := fun j d q => if actualPaddingBin η (c d) j q then
    actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
      (if (q : ℤ) ∣ n ∧ bad j n then 1 else 0) else 0
  have hterm (j : ℤ) (d q : ℕ) :
      (if actualPaddingBin η (c d) j q then
        actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
          (if (q : ℤ) ∣ n ∧
            (¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
              (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∨
            6 * W * d.primeFactors.card < (actualPaddingDegree P n : ℝ) ∨ bad j n)
            then 1 else 0) else 0) ≤ pad j d q + deg j d q + rare j d q := by
    by_cases hb : actualPaddingBin η (c d) j q
    · simp only [pad, deg, rare, paddingRejectionAtom, hb, ite_true, positiveDegreeCost]
      simpa using weighted_three_deletions
        (actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n)
        (mul_nonneg (actualPaddingCoefficient_nonneg q) (positivePrimeWeight_nonneg _ _))
        ((q : ℤ) ∣ n)
        (¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
          (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n)
        (6 * W * d.primeFactors.card < (actualPaddingDegree P n : ℝ)) (bad j n)
    · simp only [pad, deg, rare, paddingRejectionAtom, hb, ite_false, add_zero, le_refl]
  have hpad : (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, pad j d q) =
      ∑ d ∈ D, positivePrimeWeight d.primeFactors n * paddingRejectedMass Q R bins η (c d) L K n := by
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    exact (padding_rejection_bin_identity Q d.primeFactors R bins η (c d) L K n).symm
  have hdeg : (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, deg j d q) ≤
      ∑ d ∈ D, ∑ q ∈ R, positiveDegreeCost P d.primeFactors W q n := by
    rw [sum_comm]
    apply sum_le_sum
    intro d _
    rw [sum_comm]
    apply sum_le_sum
    intro q _
    apply actualPaddingBin_sum_le bins η (c d) hη q
    unfold positiveDegreeCost
    exact mul_nonneg (mul_nonneg (actualPaddingCoefficient_nonneg q)
      (positivePrimeWeight_nonneg _ _)) (by split_ifs <;> norm_num)
  have hrare : (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, rare j d q) =
      ∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R.filter (actualPaddingBin η (c d) j),
        actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
          if (q : ℤ) ∣ n ∧ bad j n then 1 else 0 := by
    simp only [sum_filter, rare]
  calc
    _ ≤ ∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, (pad j d q + deg j d q + rare j d q) := by
      apply sum_le_sum
      intro j _
      apply sum_le_sum
      intro d _
      apply sum_le_sum
      intro q _
      exact hterm j d q
    _ = (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, pad j d q) +
        (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, deg j d q) +
        (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ R, rare j d q) := by simp only [sum_add_distrib]
    _ ≤ _ := by rw [hpad, hrare]; linarith

end TwoPointCorrelations

end OAI
