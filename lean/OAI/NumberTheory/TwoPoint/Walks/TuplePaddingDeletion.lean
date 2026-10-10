import OAI.NumberTheory.TwoPoint.Bounds.PaddingDeletionComparison
import OAI.NumberTheory.TwoPoint.Walks.TupleDeletionNormalizer

namespace OAI

/-! Sum the padding-cut estimate over all tuple divisors. The center
of the logarithmic bins may depend on the tuple, as required for the
actual product d*q bins. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_integer_tuple_padding_deletion
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ (A : ℕ) (C : ℝ), 1000 ≤ A ∧ 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) → (J : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      (∑ d ∈ D, uniformAverage (fun x : Fin N =>
        positivePrimeWeight d.primeFactors ((a + x.val : ℤ) + site) *
          paddingRejectedMass data.Q Q bins η (c d) L K ((a + x.val : ℤ) + site))) /
            paddingTiltNormalizer data.Q ≤
      (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * (C / K + L ^ (-100 : ℝ)) +
        (2 * bins.card * Q.card * D.card * Real.exp (-(L ^ 9))) / paddingTiltNormalizer data.Q := by
  obtain ⟨A, C, hA, hC, hb⟩ := hBr.eventually_integer_padding_deletion hP E
  refine ⟨A, C, hA, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro h J M B data hQ hB hpool hBL P hPeq hprime hdisjoint hJ D hD Q hQsub hqdegree
    bins η K c hη hηone hK site a N hN
  have hd (d : ℕ) (hd : d ∈ D) := primeTupleDivisors_arithmetic P hprime hdisjoint (hD hd)
  have heach (d : ℕ) (hmem : d ∈ D) :
      uniformAverage (fun x : Fin N => positivePrimeWeight d.primeFactors ((a + x.val : ℤ) + site) *
        paddingRejectedMass data.Q Q bins η (c d) L K ((a + x.val : ℤ) + site)) /
          paddingTiltNormalizer data.Q ≤
      positivePrimeNormalizer d.primeFactors * (C / K + L ^ (-100 : ℝ)) +
        (2 * bins.card * Q.card * Real.exp (-(L ^ 9))) / paddingTiltNormalizer data.Q := by
    exact hb h J M B data hQ hB hpool hBL d.primeFactors ((hd d hmem).2.2.trans_eq hPeq)
      (by simpa only [(hd d hmem).2.1] using hJ) Q hQsub hqdegree bins η (c d) K
      hη hηone hK site a N hN
  have hn : 0 ≤ C / K + L ^ (-100 : ℝ) := by
    exact add_nonneg (div_nonneg hC.le hK.le) (Real.rpow_nonneg (by linarith) _)
  calc
    _ = ∑ d ∈ D, uniformAverage (fun x : Fin N =>
        positivePrimeWeight d.primeFactors ((a + x.val : ℤ) + site) *
          paddingRejectedMass data.Q Q bins η (c d) L K ((a + x.val : ℤ) + site)) /
            paddingTiltNormalizer data.Q := sum_div _ _ _
    _ ≤ ∑ d ∈ D, (positivePrimeNormalizer d.primeFactors * (C / K + L ^ (-100 : ℝ)) +
        (2 * bins.card * Q.card * Real.exp (-(L ^ 9))) / paddingTiltNormalizer data.Q) :=
      sum_le_sum heach
    _ = (∑ d ∈ D, positivePrimeNormalizer d.primeFactors) * (C / K + L ^ (-100 : ℝ)) +
        (2 * bins.card * Q.card * D.card * Real.exp (-(L ^ 9))) / paddingTiltNormalizer data.Q := by
      simp only [sum_add_distrib, ← sum_mul, sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_right (tuple_normalizer_sum_le P hprime hdisjoint D hD) hn
      linarith

end TwoPointCorrelations

end OAI
