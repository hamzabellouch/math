import OAI.NumberTheory.TwoPoint.Bounds.DivisorEndpointSymmetry
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedRowComparison

namespace OAI

/-! Exact equality of the two endpoint deletion costs in the actual
product law. The whole padding weight need not be periodic across an
edge: only the fixed q and tuple divisor tests are transported. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma positivePrimeWeight_residue_congr (S : Finset ℕ) (n m : ℤ)
    (hnm : ∀ p ∈ S, (n : ZMod p) = (m : ZMod p)) :
    positivePrimeWeight S n = positivePrimeWeight S m := by
  unfold positivePrimeWeight
  apply prod_congr rfl
  intro p hp
  have he : (p : ℤ) ∣ n ↔ (p : ℤ) ∣ m := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hnm p hp]
  simp only [he]

lemma ProhibitedPrimeFamily.positive_divisor_event_average_endpoint {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (d q : ℕ) (hd : d.primeFactors ⊆ data.P ∪ data.Q)
    (hq : q ∈ retainedPrimeDivisors data.Q) (c : ℤ) (bad : ℤ → Prop)
    (hbad : ∀ n m, (∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) →
      (bad n ↔ bad m)) :
    (data.residueLaw B hB).average (fun x =>
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (data.residueOrigin x) *
        if (q : ℤ) ∣ data.residueOrigin x ∧ bad (data.residueOrigin x + (d * q : ℕ) * c)
          then 1 else 0) =
    (data.residueLaw B hB).average (fun x =>
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (data.residueOrigin x) *
        if (q : ℤ) ∣ data.residueOrigin x ∧ bad (data.residueOrigin x) then 1 else 0) := by
  let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n *
    if (q : ℤ) ∣ n ∧ bad n then 1 else 0
  have hF (n m : ℤ)
      (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) : F n = F m := by
    have hw := positivePrimeWeight_residue_congr d.primeFactors n m
      (fun p hp => hnm ⟨p, hd hp⟩)
    have hdiv := squarefree_divisor_congr data.Q q
      (retainedPrimeDivisor_squarefree data.Q data.primeQ hq)
      (retainedPrimeDivisor_factors data.Q data.primeQ hq) n m
      (fun p hp => hnm ⟨p, mem_union_right _ hp⟩)
    simp only [F, hw, hdiv, hbad n m hnm]
  calc
    _ = (data.residueLaw B hB).average (fun x => F (data.residueOrigin x + (d * q : ℕ) * c)) := by
      apply congrArg (data.residueLaw B hB).average
      funext x
      exact positive_divisor_endpoint d q (data.residueOrigin x) c bad
    _ = _ := data.residue_average_translate hB F hF ((d * q : ℕ) * c)

lemma ProhibitedPrimeFamily.prohibited_average_endpoint {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s d q : ℕ) (hd : d.primeFactors ⊆ data.P ∪ data.Q)
    (hq : q ∈ retainedPrimeDivisors data.Q) (c : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (data.residueOrigin x) *
        if (q : ℤ) ∣ data.residueOrigin x ∧
          ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs)
            (data.residueOrigin x + (d * q : ℕ) * c) then 1 else 0) =
    (data.residueLaw B hB).average (fun x =>
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors (data.residueOrigin x) *
        if (q : ℤ) ∣ data.residueOrigin x ∧
          ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x)
          then 1 else 0) :=
  data.positive_divisor_event_average_endpoint hB d q hd hq c _
    (fun n m hnm => data.prohibitedSite_congr hB s n m hnm)

end TwoPointCorrelations

end OAI
