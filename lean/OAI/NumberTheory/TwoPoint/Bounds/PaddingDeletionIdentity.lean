import OAI.NumberTheory.TwoPoint.Bounds.PaddingCutCost

namespace OAI

/-! Exact sum of fixed-pair deletion costs. The high-degree and
low-degree density failures are disjoint and exhaust the padding cut. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def paddingRejectionAtom (Q S D : Finset ℕ) (eligible : ℕ → Prop)
    (L K : ℝ) (q : ℕ) (n : ℤ) : ℝ :=
  if eligible q then
    actualPaddingCoefficient q * positivePrimeWeight S n *
      if (q : ℤ) ∣ n ∧ ¬integerEdgeKeep D actualPaddingCoefficient eligible
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n then 1 else 0
  else 0

lemma padding_rejection_row_identity (Q S D : Finset ℕ) (eligible : ℕ → Prop)
    (L K : ℝ) (n : ℤ) :
    positivePrimeWeight S n * (actualPaddingVertex Q n) ^ 2 *
      (if ¬integerEdgeKeep D actualPaddingCoefficient eligible
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n then
          paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex Q) n else 0) =
      ∑ q ∈ D, paddingRejectionAtom Q S D eligible L K q n := by
  by_cases hk : integerEdgeKeep D actualPaddingCoefficient eligible
      (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n
  · simp only [paddingRejectionAtom, hk, not_true_eq_false, and_false, ite_false,
      mul_zero, ite_self, sum_const_zero]
  · simp only [paddingRejectionAtom, hk, not_false_eq_true, and_true, ite_true]
    calc
      _ = positivePrimeWeight S n *
          ∑ q ∈ D, if eligible q ∧ (q : ℤ) ∣ n then actualPaddingCoefficient q else 0 := by
        unfold paddingDensity
        field_simp [actualPaddingVertex_ne_zero Q n]
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro q _
        by_cases he : eligible q <;> by_cases hd : (q : ℤ) ∣ n <;>
          simp only [he, hd, and_true, and_false, ite_true, ite_false,
            mul_zero, mul_one]
        ring

lemma padding_rejection_failure_split (Q D : Finset ℕ) (eligible : ℕ → Prop)
    (L K : ℝ) (q : ℕ) (n : ℤ) :
    (if (q : ℤ) ∣ n ∧ ¬integerEdgeKeep D actualPaddingCoefficient eligible
      (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n then (1 : ℝ) else 0) =
    (if (q : ℤ) ∣ n ∧ 400 * Real.log L < (actualPaddingDegree Q n : ℝ) then 1 else 0) +
    (if (q : ℤ) ∣ n ∧ actualPaddingDegreeCut Q L n ∧
      K / L < paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex Q) n
      then 1 else 0) := by
  by_cases hd : (q : ℤ) ∣ n
  · by_cases hdegree : actualPaddingDegreeCut Q L n
    · by_cases hdensity : paddingDensity D actualPaddingCoefficient eligible
          (actualPaddingVertex Q) n ≤ K / L
      · simp only [integerEdgeKeep, hd, hdensity, hdegree, true_and, not_true_eq_false,
          ite_false, add_zero, not_lt.mpr hdensity]
        have hn : ¬400 * Real.log L < (actualPaddingDegree Q n : ℝ) :=
          not_lt.mpr hdegree
        simp only [hn, ite_false]
      · have hgt := lt_of_not_ge hdensity
        have hn : ¬400 * Real.log L < (actualPaddingDegree Q n : ℝ) :=
          not_lt.mpr hdegree
        simp only [integerEdgeKeep, hd, hdensity, hdegree, false_and, and_false,
          true_and, not_false_eq_true, ite_true, hgt, hn, ite_false, zero_add]
    · have hgt : 400 * Real.log L < (actualPaddingDegree Q n : ℝ) :=
        lt_of_not_ge hdegree
      simp only [integerEdgeKeep, hd, hdegree, and_false, false_and, true_and,
        not_false_eq_true, ite_true, hgt, ite_false, add_zero]
  · simp only [hd, false_and, ite_false, add_zero]

lemma padding_rejection_bin_identity (Q S D : Finset ℕ) (bins : Finset ℤ)
    (η c L K : ℝ) (n : ℤ) :
    positivePrimeWeight S n * paddingRejectedMass Q D bins η c L K n =
      ∑ j ∈ bins, ∑ q ∈ D, paddingRejectionAtom Q S D (actualPaddingBin η c j) L K q n := by
  unfold paddingRejectedMass
  rw [← mul_assoc, mul_sum]
  apply sum_congr rfl
  intro j _
  exact padding_rejection_row_identity Q S D (actualPaddingBin η c j) L K n

end TwoPointCorrelations

end OAI
