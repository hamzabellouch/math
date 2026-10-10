import OAI.NumberTheory.TwoPoint.Bounds.DegreeDeletionSum
import OAI.NumberTheory.TwoPoint.Walks.TupleDeletionNormalizer

namespace OAI

/-! Sum the tuple-degree deletion before normalization. One reciprocal
prime factor remains for each selected tuple coordinate, and every
padding choice contributes its exact u(q)/q mass. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_integer_tuple_degree_deletion
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
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      (∀ d ∈ D, ∀ q ∈ padding d, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      (∑ d ∈ D, ∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
        positiveDegreeCost data.P d.primeFactors W q ((a + x.val : ℤ) + site))) ≤
      (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * paddingTiltNormalizer data.Q *
        Real.exp (-2 * W * J) +
          (∑ d ∈ D, (padding d).card : ℕ) * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_integer_degree_sum
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL P hP hprime hdisjoint W hW hV hJ hTL D hD
    padding hpadding hqdegree site a N hN
  have hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * J := by
    rw [← primeHarmonicMass_eq_sum, ← hP, primeTuplePool_mass P hdisjoint]
    calc
      _ ≤ ∑ _j : Fin J, 2 * W := sum_le_sum (fun j _ => hV j)
      _ = _ := by simp; ring
  have hd (d : ℕ) (hd : d ∈ D) := primeTupleDivisors_arithmetic P hprime hdisjoint (hD hd)
  have heach (d : ℕ) (hmem : d ∈ D) :
      (∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
        positiveDegreeCost data.P d.primeFactors W q ((a + x.val : ℤ) + site))) ≤
      positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
        (∑ q ∈ padding d, actualPaddingCoefficient q / q) +
          (padding d).card * Real.exp (-(L ^ 9)) := by
    have ha := hd d hmem
    have hx := hb h J M B data hB hpool hBL d.primeFactors (ha.2.2.trans_eq hP)
      (by simpa only [ha.2.1] using hJ) W hW (by simpa only [ha.2.1] using hTL)
      (by simpa only [ha.2.1] using hmass) (padding d) (hpadding d hmem)
      (hqdegree d hmem) site a N hN
    simpa only [ha.2.1] using hx
  calc
    _ ≤ ∑ d ∈ D, (positivePrimeNormalizer d.primeFactors * Real.exp (-2 * W * J) *
          (∑ q ∈ padding d, actualPaddingCoefficient q / q) +
            (padding d).card * Real.exp (-(L ^ 9))) := sum_le_sum heach
    _ = (∑ d ∈ D, positivePrimeNormalizer d.primeFactors *
          ∑ q ∈ padding d, actualPaddingCoefficient q / q) * Real.exp (-2 * W * J) +
        (∑ d ∈ D, (padding d).card : ℕ) * Real.exp (-(L ^ 9)) := by
      rw [sum_add_distrib, Nat.cast_sum, sum_mul, sum_mul]
      congr 1
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_right
        (tuple_padding_normalizer_sum_le P hprime hdisjoint data.Q D data.primeQ hD padding hpadding)
        (Real.exp_pos (-2 * W * J)).le
      linarith

end TwoPointCorrelations

end OAI
