import OAI.NumberTheory.TwoPoint.Bounds.EndpointResidueAverage
import OAI.NumberTheory.TwoPoint.Bounds.PaddingDeletionIdentity

namespace OAI

/-! Periodicity needed to shift each numerical pair separately before
averaging its nonnegative deletion cost. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma ProhibitedPrimeFamily.paddingRejectionAtom_congr {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (S R : Finset ℕ)
    (hS : S ⊆ data.P ∪ data.Q) (hR : R ⊆ retainedPrimeDivisors data.Q)
    (eligible : ℕ → Prop) (L K : ℝ) (q : ℕ) (hq : q ∈ retainedPrimeDivisors data.Q)
    (n m : ℤ)
    (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) :
    paddingRejectionAtom data.Q S R eligible L K q n =
      paddingRejectionAtom data.Q S R eligible L K q m := by
  have hw := positivePrimeWeight_residue_congr S n m (fun p hp => hnm ⟨p, hS hp⟩)
  have hd := squarefree_divisor_congr data.Q q
    (retainedPrimeDivisor_squarefree data.Q data.primeQ hq)
    (retainedPrimeDivisor_factors data.Q data.primeQ hq) n m
    (fun p hp => hnm ⟨p, mem_union_right _ hp⟩)
  have hk := actualPaddingKeep_residue_congr data.Q data.primeQ R hR eligible L K n m
    (fun p hp => hnm ⟨p, mem_union_right _ hp⟩)
  simp only [paddingRejectionAtom, hw, hd, hk]

lemma ProhibitedPrimeFamily.padding_rejection_average_translate {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S R : Finset ℕ) (hS : S ⊆ data.P ∪ data.Q) (hR : R ⊆ retainedPrimeDivisors data.Q)
    (eligible : ℕ → Prop) (L K : ℝ) (q : ℕ) (hq : q ∈ retainedPrimeDivisors data.Q)
    (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      paddingRejectionAtom data.Q S R eligible L K q (data.residueOrigin x + site)) =
    (data.residueLaw B hB).average (fun x =>
      paddingRejectionAtom data.Q S R eligible L K q (data.residueOrigin x)) :=
  data.residue_average_translate hB _
    (fun n m hnm => data.paddingRejectionAtom_congr S R hS hR eligible L K q hq n m hnm) site

lemma ProhibitedPrimeFamily.prohibited_cost_average_translate {h J M B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hS : S ⊆ data.P ∪ data.Q) (s q : ℕ)
    (hq : q ∈ retainedPrimeDivisors data.Q) (site : ℤ) :
    (data.residueLaw B hB).average (fun x => actualPaddingCoefficient q *
      positivePrimeWeight S (data.residueOrigin x + site) *
        if (q : ℤ) ∣ data.residueOrigin x + site ∧
          ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x + site)
          then 1 else 0) =
    (data.residueLaw B hB).average (fun x => actualPaddingCoefficient q *
      positivePrimeWeight S (data.residueOrigin x) *
        if (q : ℤ) ∣ data.residueOrigin x ∧
          ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) (data.residueOrigin x)
          then 1 else 0) := by
  let F := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S n *
    if (q : ℤ) ∣ n ∧ ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n then 1 else 0
  have hF (n m : ℤ)
      (hnm : ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = (m : ZMod p.val)) : F n = F m := by
    have hw := positivePrimeWeight_residue_congr S n m (fun p hp => hnm ⟨p, hS hp⟩)
    have hd := squarefree_divisor_congr data.Q q
      (retainedPrimeDivisor_squarefree data.Q data.primeQ hq)
      (retainedPrimeDivisor_factors data.Q data.primeQ hq) n m
      (fun p hp => hnm ⟨p, mem_union_right _ hp⟩)
    have hp := data.prohibitedSite_congr hB s n m hnm
    simp only [F, hw, hd, hp]
  exact data.residue_average_translate hB F hF site

end TwoPointCorrelations

end OAI
