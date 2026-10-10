import OAI.NumberTheory.TwoPoint.Walks.TupleDegreeDeletion
import OAI.NumberTheory.TwoPoint.Bounds.DeletionRowSplit

namespace OAI

/-! The tuple-degree deletion summed over disjoint logarithmic bins,
each sampled on its own integer interval. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma padding_bin_reciprocal_sum_le (Q R : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hR : R ⊆ retainedPrimeDivisors Q) (bins : Finset ℤ) (η c : ℝ) (hη : 0 < η) :
    (∑ j ∈ bins, ∑ q ∈ R.filter (actualPaddingBin η c j),
      actualPaddingCoefficient q / (q : ℝ)) ≤ paddingTiltNormalizer Q := by
  simp only [sum_filter]
  rw [sum_comm]
  calc
    _ ≤ ∑ q ∈ R, actualPaddingCoefficient q / (q : ℝ) := by
      apply sum_le_sum
      intro q _
      exact actualPaddingBin_sum_le bins η c hη q _
        (div_nonneg (actualPaddingCoefficient_nonneg q) (Nat.cast_nonneg q))
    _ ≤ _ := retained_padding_mass_le Q R hQ hR

theorem BravermanDepth22Input.eventually_variable_tuple_degree_deletion
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      ∀ W : ℝ, 10 ≤ W → (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (J : ℝ) ≤ L ^ 2 → 6 * W * J ≤ 400 * Real.log L →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η : ℝ) (c : ℕ → ℝ), 0 < η →
      ∀ (site : ℤ) (a N : ℤ → ℕ), (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
        uniformAverage (fun x : Fin (N j) =>
          positiveDegreeCost data.P d.primeFactors W q ((a j + x.val : ℤ) + site))) ≤
      (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * paddingTiltNormalizer data.Q *
        Real.exp (-2 * W * J) +
          bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_integer_degree_sum
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL P hP hprime hdisjoint W hW hV hJ hTL D hD Q hQ
    hqdegree bins η c hη site a N hN
  have hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * J := by
    rw [← primeHarmonicMass_eq_sum, ← hP, primeTuplePool_mass P hdisjoint]
    calc
      _ ≤ ∑ _j : Fin J, 2 * W := sum_le_sum (fun j _ => hV j)
      _ = _ := by simp; ring
  have ht (d : ℕ) (hd : d ∈ D) :
      (∑ j ∈ bins, ∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
        uniformAverage (fun x : Fin (N j) =>
          positiveDegreeCost data.P d.primeFactors W q ((a j + x.val : ℤ) + site))) ≤
      positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) * paddingTiltNormalizer data.Q +
        bins.card * Q.card * Real.exp (-(L ^ 9)) := by
    have ha := primeTupleDivisors_arithmetic P hprime hdisjoint (hD hd)
    have heach (j : ℤ) (hj : j ∈ bins) :
        (∑ q ∈ Q.filter (actualPaddingBin η (c d) j),
          uniformAverage (fun x : Fin (N j) =>
            positiveDegreeCost data.P d.primeFactors W q ((a j + x.val : ℤ) + site))) ≤
        positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
          (∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
            Q.card * Real.exp (-(L ^ 9)) := by
      have hx := hb h J M B data hB hpool hBL d.primeFactors (ha.2.2.trans_eq hP)
        (by simpa only [ha.2.1] using hJ) W hW (by simpa only [ha.2.1] using hTL)
        (by simpa only [ha.2.1] using hmass) (Q.filter (actualPaddingBin η (c d) j))
        ((filter_subset _ _).trans hQ) (fun q hq => hqdegree q (mem_filter.mp hq).1)
        site (a j) (N j) (hN j hj)
      have hcard : ((Q.filter (actualPaddingBin η (c d) j)).card : ℝ) ≤ Q.card := by
        exact_mod_cast card_filter_le Q (actualPaddingBin η (c d) j)
      have herr := mul_le_mul_of_nonneg_right hcard (Real.exp_pos (-(L ^ 9))).le
      simp only [ha.2.1] at hx
      linarith
    calc
      _ ≤ ∑ j ∈ bins, (positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
            (∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
              Q.card * Real.exp (-(L ^ 9))) := sum_le_sum heach
      _ = positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
            (∑ j ∈ bins, ∑ q ∈ Q.filter (actualPaddingBin η (c d) j), actualPaddingCoefficient q / q) +
              bins.card * Q.card * Real.exp (-(L ^ 9)) := by
        simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left
          (padding_bin_reciprocal_sum_le data.Q Q data.primeQ hQ bins η (c d) hη)
          (show 0 ≤ positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) by
            unfold positivePrimeNormalizer; positivity)
        linarith
  rw [sum_comm]
  calc
    _ ≤ ∑ d ∈ D, (positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
          paddingTiltNormalizer data.Q + bins.card * Q.card * Real.exp (-(L ^ 9))) := sum_le_sum ht
    _ = (∑ d ∈ D, positivePrimeNormalizer d.primeFactors) * Real.exp (-2 * W * J) *
          paddingTiltNormalizer data.Q + bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
      simp only [sum_add_distrib, ← sum_mul, sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (tuple_normalizer_sum_le P hprime hdisjoint D hD)
          (Real.exp_pos (-2 * W * J)).le) (paddingTiltNormalizer_pos data.Q).le
      nlinarith

end TwoPointCorrelations

end OAI
