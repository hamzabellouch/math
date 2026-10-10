import OAI.NumberTheory.TwoPoint.Walks.ProhibitedCostComparison
import OAI.NumberTheory.TwoPoint.Bounds.PaddingDeletionComparison
import OAI.NumberTheory.TwoPoint.Bounds.RareRowSum
import OAI.NumberTheory.TwoPoint.Bounds.MaskedWeightPeriodicity
import OAI.NumberTheory.TwoPoint.Bounds.UniformResidueTranslation

namespace OAI

/-! Sum the literal positive cost over tuple/padding choices. The
comparison error counts pairs, while the product-model cost is bounded
by the already proved row second moment and rare-event probability. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def prohibitedPositiveRow {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (D : Finset ℕ)
    (padding : ℕ → Finset ℕ) (n : ℤ) : ℝ :=
  ∑ d ∈ D, ∑ q ∈ padding d,
    actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
      if (q : ℤ) ∣ n ∧ ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then 1 else 0

lemma prohibitedPositiveRow_nonneg {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (D : Finset ℕ)
    (padding : ℕ → Finset ℕ) (n : ℤ) : 0 ≤ prohibitedPositiveRow data s D padding n := by
  apply sum_nonneg
  intro d _
  apply sum_nonneg
  intro q _
  exact mul_nonneg (mul_nonneg (actualPaddingCoefficient_nonneg q)
    (positivePrimeWeight_nonneg _ _)) (by split_ifs <;> norm_num)

lemma ProhibitedPrimeFamily.prohibited_probability_translate {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s : ℕ) (site : ℤ) :
    (data.residueLaw B hB).probability (fun x =>
      ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x + site)) =
      (data.residueLaw B hB).probability (data.deletedEvent s B) := by
  let f := fun n : ℤ => if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n
    then (1 : ℝ) else 0
  have hf (n m : ℤ)
      (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) : f n = f m := by
    simp only [f, data.prohibitedSite_congr hB s n m hnm]
  have ht := data.residue_average_translate hB f hf site
  have he (x : ↥(data.P ∪ data.Q) → Fin B) :
      ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x) ↔
        data.deletedEvent s B x :=
    (data.deletedEvent_iff s B x (data.residueOrigin x) (data.residueOrigin_spec x)).symm
  simpa [FiniteLaw.probability, f, he] using ht

lemma prohibitedPositiveRow_le {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (s : ℕ) (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (D : Finset ℕ) (hD : D ⊆ primeTupleDivisors P)
    (padding : ℕ → Finset ℕ) (hpadding : ∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q)
    (n : ℤ) :
    prohibitedPositiveRow data s D padding n ≤ primeRowMajorant P data.Q n *
      if ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then 1 else 0 :=
  positive_rare_row_bound P hprime hdisjoint data.Q D data.primeQ hD padding hpadding n _

theorem BravermanDepth22Input.eventually_prohibited_row_comparison
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
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |uniformAverage (fun x : Fin N =>
          prohibitedPositiveRow data s D padding ((a + x.val : ℤ) + site)) -
        (data.residueLaw B hB).average (fun x =>
          prohibitedPositiveRow data s D padding (data.residueOrigin x + site))| ≤
          (∑ d ∈ D, (padding d).card : ℕ) * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_prohibited_cost_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B s cap data hB hpool hBL hs hcap hpair hdegree D hD hcard
    padding hpadding hqdegree site a N hN
  let μ := data.residueLaw B hB
  let atom := fun (d q : ℕ) (n : ℤ) => actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
    if (q : ℤ) ∣ n ∧ ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then 1 else 0
  have hinner (d : D) :
      |uniformAverage (fun x : Fin N => ∑ q : padding d.val, atom d.val q.val ((a + x.val : ℤ) + site)) -
        μ.average (fun x => ∑ q : padding d.val, atom d.val q.val (data.residueOrigin x + site))| ≤
          (padding d.val).card * Real.exp (-(L ^ 9)) := by
    simpa only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] using
      uniformFiniteLaw_sum_error μ
        (fun (q : padding d.val) (x : Fin N) => atom d.val q.val ((a + x.val : ℤ) + site))
        (fun (q : padding d.val) x => atom d.val q.val (data.residueOrigin x + site))
        (fun _ => Real.exp (-(L ^ 9)))
        (fun q => hb h J M B s cap data hB hpool hBL hs hcap hpair hdegree
          d.val.primeFactors (hD _ d.property) (hcard _ d.property) q.val
          (hpadding _ d.property q.property) (hqdegree _ d.property _ q.property) site a N hN)
  have ht := uniformFiniteLaw_sum_error μ
    (fun (d : D) (x : Fin N) => ∑ q : padding d.val, atom d.val q.val ((a + x.val : ℤ) + site))
    (fun (d : D) x => ∑ q : padding d.val, atom d.val q.val (data.residueOrigin x + site))
    (fun d => (padding d.val).card * Real.exp (-(L ^ 9))) hinner
  have hqsum (d : ℕ) (n : ℤ) :
      (∑ q : padding d, atom d q.val n) = ∑ q ∈ padding d, atom d q n :=
    sum_coe_sort (padding d) (fun q : ℕ => atom d q n)
  have hdsum (n : ℤ) :
      (∑ d : D, ∑ q : padding d.val, atom d.val q.val n) =
        prohibitedPositiveRow data s D padding n := by
    simp only [hqsum]
    exact sum_coe_sort D (fun d : ℕ => ∑ q ∈ padding d, atom d q n)
  have herror : (∑ d : D, (padding d.val).card * Real.exp (-(L ^ 9))) =
      (∑ d ∈ D, (padding d).card : ℕ) * Real.exp (-(L ^ 9)) := by
    rw [sum_coe_sort D (fun d : ℕ => (padding d).card * Real.exp (-(L ^ 9))), ← sum_mul,
      Nat.cast_sum]
  simpa only [hdsum, herror, μ] using ht

end TwoPointCorrelations

end OAI
