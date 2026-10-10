import OAI.NumberTheory.TwoPoint.Bounds.PrimeTuplePool
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWeightIndependence

namespace OAI

/-! The graph's literal padding weight and vertex normalization.
The normalization is the square root of `5^omega_Q(n)` and depends
only on the padding-prime residues, including at the integer zero. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def actualPaddingDegree (Q : Finset ℕ) (n : ℤ) : ℕ :=
  (Q.filter (fun p : ℕ => (p : ℤ) ∣ n)).card

noncomputable def actualPaddingWeight (Q : Finset ℕ) (n : ℤ) : ℝ :=
  (5 : ℝ) ^ actualPaddingDegree Q n

noncomputable def actualPaddingVertex (Q : Finset ℕ) (n : ℤ) : ℝ :=
  Real.sqrt (actualPaddingWeight Q n)

noncomputable def actualPaddingCoefficient (q : ℕ) : ℝ :=
  (4 : ℝ) ^ q.primeFactors.card

lemma actualPaddingCoefficient_nonneg (q : ℕ) : 0 ≤ actualPaddingCoefficient q := by
  unfold actualPaddingCoefficient
  positivity

lemma actualPaddingWeight_one_le (Q : Finset ℕ) (n : ℤ) : 1 ≤ actualPaddingWeight Q n :=
  one_le_pow₀ (by norm_num)

lemma actualPaddingVertex_one_le (Q : Finset ℕ) (n : ℤ) : 1 ≤ actualPaddingVertex Q n := by
  simpa only [actualPaddingVertex, Real.sqrt_one] using
    Real.sqrt_le_sqrt (actualPaddingWeight_one_le Q n)

lemma actualPaddingVertex_pos (Q : Finset ℕ) (n : ℤ) : 0 < actualPaddingVertex Q n :=
  zero_lt_one.trans_le (actualPaddingVertex_one_le Q n)

lemma actualPaddingVertex_ne_zero (Q : Finset ℕ) (n : ℤ) : actualPaddingVertex Q n ≠ 0 :=
  (actualPaddingVertex_pos Q n).ne'

lemma actualPaddingVertex_sq (Q : Finset ℕ) (n : ℤ) :
    actualPaddingVertex Q n ^ 2 = actualPaddingWeight Q n :=
  Real.sq_sqrt (zero_le_one.trans (actualPaddingWeight_one_le Q n))

lemma actualPaddingDegree_residue_congr (Q : Finset ℕ) (n m : ℤ)
    (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    actualPaddingDegree Q n = actualPaddingDegree Q m := by
  unfold actualPaddingDegree
  congr 1
  ext p
  simp only [mem_filter]
  apply and_congr_right
  intro hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hnm p hp]

lemma actualPaddingWeight_residue_congr (Q : Finset ℕ) (n m : ℤ)
    (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    actualPaddingWeight Q n = actualPaddingWeight Q m := by
  unfold actualPaddingWeight
  rw [actualPaddingDegree_residue_congr Q n m hnm]

lemma actualPaddingVertex_residue_congr (Q : Finset ℕ) (n m : ℤ)
    (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    actualPaddingVertex Q n = actualPaddingVertex Q m := by
  unfold actualPaddingVertex
  rw [actualPaddingWeight_residue_congr Q n m hnm]

noncomputable def actualPaddingDegreeCut (Q : Finset ℕ) (L : ℝ) (n : ℤ) : Prop :=
  (actualPaddingDegree Q n : ℝ) ≤ 400 * Real.log L

lemma actualPaddingDegreeCut_residue_congr (Q : Finset ℕ) (L : ℝ) (n m : ℤ)
    (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    actualPaddingDegreeCut Q L n ↔ actualPaddingDegreeCut Q L m := by
  unfold actualPaddingDegreeCut
  rw [actualPaddingDegree_residue_congr Q n m hnm]

lemma actualPaddingDegree_eq_available (Q : Finset ℕ) (n : ℤ) :
    actualPaddingDegree Q n =
      (paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n))).card := by
  rw [paddingAvailablePrimes_integer]
  rfl

lemma actualPaddingWeight_eq_tilt (Q : Finset ℕ) (n : ℤ) :
    actualPaddingWeight Q n = paddingTiltWeight Q (fun p => decide ((p.val : ℤ) ∣ n)) := by
  rw [paddingTiltWeight_eq_five_pow, ← paddingAvailablePrimes_card,
    ← actualPaddingDegree_eq_available]
  rfl

lemma actualPaddingWeight_eq_divisor_sum (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (n : ℤ) :
    actualPaddingWeight Q n = ∑ q ∈ retainedPrimeDivisors Q,
      if (q : ℤ) ∣ n then actualPaddingCoefficient q else 0 := by
  simpa only [actualPaddingWeight, actualPaddingDegree, actualPaddingCoefficient] using
    (padding_integer_weight_total Q hQ n).symm

def actualPaddingBin (η c : ℝ) (j : ℤ) (q : ℕ) : Prop :=
  (j : ℝ) * η ≤ Real.log q + c ∧ Real.log q + c < ((j : ℝ) + 1) * η

/-- With all squarefree padding divisors available, the graph density is
exactly the literal normalized bin mass. -/
lemma actualPaddingDensity_eq_integerBin (Q : Finset ℕ) (n : ℤ) (η c : ℝ) (j : ℤ) :
    paddingDensity (retainedPrimeDivisors Q) actualPaddingCoefficient
      (actualPaddingBin η c j) (actualPaddingVertex Q) n =
      integerPaddingBinMass Q n η c j := by
  unfold paddingDensity integerPaddingBinMass
  rw [actualPaddingVertex_sq]
  change (∑ q ∈ retainedPrimeDivisors Q,
      if actualPaddingBin η c j q ∧ (q : ℤ) ∣ n then actualPaddingCoefficient q else 0) /
        (5 : ℝ) ^ (Q.filter (fun p : ℕ => (p : ℤ) ∣ n)).card = _
  have hs : (∑ q ∈ retainedPrimeDivisors Q,
      if actualPaddingBin η c j q ∧ (q : ℤ) ∣ n then actualPaddingCoefficient q else 0) =
      ∑ q ∈ retainedPrimeDivisors Q,
        if (q : ℤ) ∣ n ∧ (j : ℝ) * η ≤ Real.log q + c ∧
            Real.log q + c < ((j : ℝ) + 1) * η
        then (4 : ℝ) ^ q.primeFactors.card else 0 := by
    apply sum_congr rfl
    intro q _
    have he : actualPaddingBin η c j q ∧ (q : ℤ) ∣ n ↔
        (q : ℤ) ∣ n ∧ (j : ℝ) * η ≤ Real.log q + c ∧
          Real.log q + c < ((j : ℝ) + 1) * η := by
      unfold actualPaddingBin
      tauto
    simp only [he, actualPaddingCoefficient]
  rw [hs, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_comm]

lemma actualPaddingDensity_nonneg (Q : Finset ℕ) (D : Finset ℕ)
    (eligible : ℕ → Prop) (n : ℤ) :
    0 ≤ paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex Q) n := by
  unfold paddingDensity
  apply div_nonneg _ (sq_nonneg _)
  apply sum_nonneg
  intro q _
  split_ifs
  · exact actualPaddingCoefficient_nonneg q
  · exact le_rfl

lemma actualPaddingDensity_le_one (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : Finset ℕ) (hD : D ⊆ retainedPrimeDivisors Q)
    (eligible : ℕ → Prop) (n : ℤ) :
    paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex Q) n ≤ 1 := by
  unfold paddingDensity
  rw [actualPaddingVertex_sq]
  apply (div_le_one (zero_lt_one.trans_le (actualPaddingWeight_one_le Q n))).mpr
  calc
    _ ≤ ∑ q ∈ D, if (q : ℤ) ∣ n then actualPaddingCoefficient q else 0 := by
      apply sum_le_sum
      intro q _
      by_cases he : eligible q <;> by_cases hd : (q : ℤ) ∣ n
      · simp only [he, hd, and_self, ite_true, le_refl]
      · simp only [he, hd, and_false, ite_false, le_refl]
      · simp only [he, hd, false_and, ite_false, ite_true]
        exact actualPaddingCoefficient_nonneg q
      · simp only [he, hd, false_and, ite_false, le_refl]
    _ ≤ ∑ q ∈ retainedPrimeDivisors Q,
        if (q : ℤ) ∣ n then actualPaddingCoefficient q else 0 := by
      apply sum_le_sum_of_subset_of_nonneg hD
      intro q _ _
      split_ifs
      · exact actualPaddingCoefficient_nonneg q
      · exact le_rfl
    _ = _ := (actualPaddingWeight_eq_divisor_sum Q hQ n).symm

lemma actualPaddingDensity_le_integerBin (Q : Finset ℕ) (D : Finset ℕ)
    (hD : D ⊆ retainedPrimeDivisors Q) (n : ℤ) (η c : ℝ) (j : ℤ) :
    paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex Q) n ≤ integerPaddingBinMass Q n η c j := by
  rw [← actualPaddingDensity_eq_integerBin Q n η c j]
  unfold paddingDensity
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply sum_le_sum_of_subset_of_nonneg hD
  intro q _ _
  split_ifs
  · exact actualPaddingCoefficient_nonneg q
  · exact le_rfl

lemma actualPaddingDensity_residue_congr (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : Finset ℕ) (hD : D ⊆ retainedPrimeDivisors Q) (eligible : ℕ → Prop)
    (n m : ℤ) (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex Q) n =
      paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex Q) m :=
  paddingDensity_eq_of_prime_residues Q D actualPaddingCoefficient eligible (actualPaddingVertex Q)
    (fun _ hq => retainedPrimeDivisor_squarefree Q hQ (hD hq))
    (fun _ hq => retainedPrimeDivisor_factors Q hQ (hD hq)) n m hnm
    (actualPaddingVertex_residue_congr Q n m hnm)

lemma actualPaddingKeep_residue_congr (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : Finset ℕ) (hD : D ⊆ retainedPrimeDivisors Q) (eligible : ℕ → Prop)
    (L K : ℝ) (n m : ℤ) (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    integerEdgeKeep D actualPaddingCoefficient eligible (actualPaddingVertex Q) L K
        (actualPaddingDegreeCut Q L) n ↔
      integerEdgeKeep D actualPaddingCoefficient eligible (actualPaddingVertex Q) L K
        (actualPaddingDegreeCut Q L) m := by
  unfold integerEdgeKeep
  rw [actualPaddingDensity_residue_congr Q hQ D hD eligible n m hnm,
    actualPaddingDegreeCut_residue_congr Q L n m hnm]

end TwoPointCorrelations

end OAI
