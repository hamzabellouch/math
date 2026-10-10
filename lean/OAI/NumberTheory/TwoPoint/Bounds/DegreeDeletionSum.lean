import OAI.NumberTheory.TwoPoint.Bounds.DegreeCostResidue

namespace OAI

/-! Summing the actual integer degree-deletion cost preserves the
padding reciprocal mass and the tuple normalizer. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def positiveDegreeCost (P S : Finset ℕ) (W : ℝ) (q : ℕ) (n : ℤ) : ℝ :=
  actualPaddingCoefficient q * positivePrimeWeight S n *
    if (q : ℤ) ∣ n ∧ 6 * W * S.card < (actualPaddingDegree P n : ℝ) then 1 else 0

theorem BravermanDepth22Input.eventually_integer_degree_sum
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (W : ℝ), 10 ≤ W → 6 * W * S.card ≤ 400 * Real.log L →
      (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      (∑ q ∈ Q, uniformAverage (fun x : Fin N =>
        positiveDegreeCost data.P S W q ((a + x.val : ℤ) + site))) ≤
      positivePrimeNormalizer S * Real.exp (-2 * W * S.card) *
        (∑ q ∈ Q, actualPaddingCoefficient q / q) + Q.card * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_integer_degree_cost
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL S hSP hSL W hW hTL hmass Q hQ hqdegree site a N hN
  calc
    _ ≤ ∑ q ∈ Q, (actualPaddingCoefficient q / q * positivePrimeNormalizer S *
        Real.exp (-2 * W * S.card) + Real.exp (-(L ^ 9))) := by
      apply sum_le_sum
      intro q hq
      simpa only [positiveDegreeCost] using
        hb h J M B data hB hpool hBL S hSP hSL W hW hTL hmass
          q (hQ hq) (hqdegree q hq) site a N hN
    _ = _ := by
      simp only [sum_add_distrib, ← sum_mul, sum_const, nsmul_eq_mul]
      ring

end TwoPointCorrelations

end OAI
