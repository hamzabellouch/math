import OAI.NumberTheory.TwoPoint.Bounds.PositiveCostPeriodicity
import OAI.NumberTheory.TwoPoint.Bounds.VariableWindowComparison
import OAI.NumberTheory.TwoPoint.Bounds.SourceDeletionTerms

namespace OAI

/-! Rare-site row comparison with a distinct additive shift at every
numerical pair, in particular the opposite endpoint of that edge. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def shiftedProhibitedRow {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (s : ℕ) (D : Finset ℕ) (padding : ℕ → Finset ℕ) (site : ℕ → ℕ → ℤ) (n : ℤ) : ℝ :=
  ∑ d ∈ D, ∑ q ∈ padding d, actualPaddingCoefficient q *
    positivePrimeWeight d.primeFactors (n + site d q) *
      if (q : ℤ) ∣ n + site d q ∧
        ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (n + site d q) then 1 else 0

theorem BravermanDepth22Input.eventually_shifted_prohibited_row_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B s cap : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      (s : ℝ) ≤ L → (cap : ℝ) ≤ L ^ 2 →
      (data.pairs.card : ℝ) ≤ Real.exp (101 * L) →
      (∀ dq ∈ data.pairs, (dq.2 * dq.1).primeFactors.card ≤ cap) →
      ∀ (D : Finset ℕ),
      (∀ d ∈ D, d.primeFactors ⊆ data.P ∪ data.Q) →
      (∀ d ∈ D, (d.primeFactors.card : ℝ) ≤ L ^ 2) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      (∀ d ∈ D, ∀ q ∈ padding d, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (site : ℕ → ℕ → ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |(∑ d ∈ D, ∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
          actualPaddingCoefficient q * positivePrimeWeight d.primeFactors ((a + x.val : ℤ) + site d q) *
            if (q : ℤ) ∣ (a + x.val : ℤ) + site d q ∧
              ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) ((a + x.val : ℤ) + site d q)
              then 1 else 0)) -
        (data.residueLaw B hB).average (fun x =>
          prohibitedPositiveRow data s D padding (data.residueOrigin x))| ≤
            (∑ d ∈ D, (padding d).card : ℕ) * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_prohibited_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B s cap data hB hpool hBL hs hcap hpair hdegree D hD hcard
    padding hpadding hqdegree site a N hN
  let μ := data.residueLaw B hB
  let atom := fun d q n => actualPaddingCoefficient q * positivePrimeWeight (Nat.primeFactors d) n *
    if (q : ℤ) ∣ n ∧ ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then 1 else 0
  have hpoint (d : ℕ) (hd : d ∈ D) (q : ℕ) (hq : q ∈ padding d) :
      |uniformAverage (fun x : Fin N => atom d q ((a + x.val : ℤ) + site d q)) -
        μ.average (fun x => atom d q (data.residueOrigin x))| ≤ Real.exp (-(L ^ 9)) := by
    have hx := hb h J M B s cap data hB hpool hBL hs hcap hpair hdegree
      d.primeFactors (hD d hd) (hcard d hd) q (hpadding d hd hq) (hqdegree d hd q hq)
      (site d q) a N hN
    dsimp only at hx
    rw [data.prohibited_cost_average_translate hB d.primeFactors (hD d hd) s q
      (hpadding d hd hq) (site d q)] at hx
    exact hx
  have hinner (d : ℕ) (hd : d ∈ D) :
      |(∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
          atom d q ((a + x.val : ℤ) + site d q))) -
        μ.average (fun x => ∑ q ∈ padding d, atom d q (data.residueOrigin x))| ≤
          (padding d).card * Real.exp (-(L ^ 9)) := by
    rw [μ.average_finset_sum]
    simpa only [sum_const, nsmul_eq_mul] using finset_sum_error (padding d)
      (fun q => uniformAverage (fun x : Fin N => atom d q ((a + x.val : ℤ) + site d q)))
      (fun q => μ.average (fun x => atom d q (data.residueOrigin x)))
      (fun _ => Real.exp (-(L ^ 9))) (hpoint d hd)
  have hout := finset_sum_error D
    (fun d => ∑ q ∈ padding d, uniformAverage (fun x : Fin N =>
      atom d q ((a + x.val : ℤ) + site d q)))
    (fun d => μ.average (fun x => ∑ q ∈ padding d, atom d q (data.residueOrigin x)))
    (fun d => (padding d).card * Real.exp (-(L ^ 9))) hinner
  rw [← μ.average_finset_sum, ← sum_mul, ← Nat.cast_sum] at hout
  exact hout

end TwoPointCorrelations

end OAI
