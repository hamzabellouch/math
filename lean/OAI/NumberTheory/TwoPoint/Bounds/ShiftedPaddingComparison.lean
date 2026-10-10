import OAI.NumberTheory.TwoPoint.Bounds.VariablePaddingDeletion
import OAI.NumberTheory.TwoPoint.Bounds.PositiveCostPeriodicity

namespace OAI

/-! Each numerical pair can be sampled at its own additive shift.
The common model is recovered by exact residue translation. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_shifted_padding_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (D : Finset ℕ),
      (∀ d ∈ D, d.primeFactors ⊆ data.P ∪ data.Q) →
      (∀ d ∈ D, (d.primeFactors.card : ℝ) ≤ L ^ 2) →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ) (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      |(∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q, uniformAverage (fun x : Fin (N j) =>
          paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
            ((a j + x.val : ℤ) + site j d q))) -
        (data.residueLaw B hB).average (fun x => ∑ d ∈ D,
          positivePrimeWeight d.primeFactors (data.residueOrigin x) *
            paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x))| ≤
        2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_padding_atom_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL D hD hcard Q hQ hqdegree bins η K c site a N hN
  let I := bins ×ˢ (D ×ˢ Q)
  let f := fun (i : ℤ × (ℕ × ℕ)) (n : ℤ) =>
    paddingRejectionAtom data.Q i.2.1.primeFactors Q (actualPaddingBin η (c i.2.1) i.1)
      L K i.2.2 (n + site i.1 i.2.1 i.2.2)
  let g := fun (i : ℤ × (ℕ × ℕ)) (x : ↥(data.P ∪ data.Q) → Fin B) =>
    paddingRejectionAtom data.Q i.2.1.primeFactors Q (actualPaddingBin η (c i.2.1) i.1)
      L K i.2.2 (data.residueOrigin x)
  have hs := finite_interval_family_error I (data.residueLaw B hB)
    (fun i => a i.1) (fun i => N i.1) f g (fun _ => 2 * Real.exp (-(L ^ 9))) (by
      intro i hi
      obtain ⟨hj, hdq⟩ := mem_product.mp hi
      obtain ⟨hd, hq⟩ := mem_product.mp hdq
      have hx := hb h J M B data hB hpool hBL i.2.1.primeFactors (hD _ hd) (hcard _ hd)
        i.2.2 (hQ hq) (hqdegree _ hq) Q hQ (actualPaddingBin η (c i.2.1) i.1)
        K (site i.1 i.2.1 i.2.2) (a i.1) (N i.1) (hN _ hj)
      rw [data.padding_rejection_average_translate hB i.2.1.primeFactors Q (hD _ hd)
        hQ (actualPaddingBin η (c i.2.1) i.1) L K i.2.2 (hQ hq)
          (site i.1 i.2.1 i.2.2)] at hx
      exact hx)
  have he : (∑ _i ∈ I, 2 * Real.exp (-(L ^ 9))) =
      2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
    simp only [sum_const, nsmul_eq_mul, I, card_product, Nat.cast_mul]
    ring
  rw [he] at hs
  simp only [I, sum_product, f, g] at hs
  have hmodel (x : ↥(data.P ∪ data.Q) → Fin B) :
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q,
        paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
          (data.residueOrigin x)) =
      ∑ d ∈ D, positivePrimeWeight d.primeFactors (data.residueOrigin x) *
        paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    exact (padding_rejection_bin_identity data.Q d.primeFactors Q bins η (c d) L K _).symm
  simpa only [hmodel] using hs

end TwoPointCorrelations

end OAI
