import OAI.NumberTheory.CubicMoment.Estimates.PrimeStoppingLabels
import OAI.NumberTheory.CubicMoment.Estimates.SelectedPrimeCanonical

namespace OAI

/-! Inverting the independent stopping predicates reconstructs the exact
selected divisor and complementary divisor of the original squarefree term. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeFactors_disjoint_of_squarefree_mul {d e : Eisenstein}
    (hd : primary d) (he : primary e) (hs : Squarefree (d*e)) :
    Disjoint (primaryPrimeFactors d) (primaryPrimeFactors e) := by
  have hc : IsCoprime d e := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hpd := primaryPrimeFactor_spec hd hp
  have hpe := primaryPrimeFactor_spec he hq
  exact hpd.1.2.not_isUnit (hc.isUnit_of_dvd' hpd.2 hpe.2)

/-- The independent selected and remaining predicates give an actual
selection in the original factor set, with the exact two products and
exact inverse-binomial denominator. -/
theorem stopping_pair_reconstruction {d e r : Eisenstein}
    (hd : primary d) (he : primary e) (hs : Squarefree (d*e))
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k l : ℕ) (Z : ℝ)
    (hselected : stoppingSideTest bin ell j k Z r d)
    (hremaining : stoppingRemainingTest bin j l e) :
    ∃ t ∈ (primeBin (primaryPrimeFactors (d*e)) bin j).powersetCard k,
      (∏ p ∈ stoppingSelected (primaryPrimeFactors (d*e)) bin j t, p) = d ∧
      (∏ p ∈ stoppingRemainder (primaryPrimeFactors (d*e)) bin j t, p) = e ∧
      (primeBin (primaryPrimeFactors (d*e)) bin j).card = k+l ∧
      (norm r*primeSurrogate
          (stoppingSelected (primaryPrimeFactors (d*e)) bin j t) bin ell/ell j < Z ∧
        Z ≤ norm r*primeSurrogate
          (stoppingSelected (primaryPrimeFactors (d*e)) bin j t) bin ell) := by
  let t := primeBin (primaryPrimeFactors d) bin j
  have hsel : stoppingSelected (primaryPrimeFactors (d*e)) bin j t =
      primaryPrimeFactors d := by
    rw [primaryPrimeFactors_mul_union hd he]
    exact stoppingSelected_of_separated_bins _ _ bin j hselected.1 hremaining.1
  have hrem : stoppingRemainder (primaryPrimeFactors (d*e)) bin j t =
      primaryPrimeFactors e := by
    rw [primaryPrimeFactors_mul_union hd he]
    exact stoppingRemainder_of_separated_bins _ _ bin j
      (primeFactors_disjoint_of_squarefree_mul hd he hs) hselected.1 hremaining.1
  have ht : t ∈ (primeBin (primaryPrimeFactors (d*e)) bin j).powersetCard k := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_,hselected.2.1⟩
    intro p hp
    obtain ⟨hpd,hpj⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    rw [primaryPrimeFactors_mul_union hd he]
    exact ⟨Finset.mem_union_left _ hpd,hpj⟩
  have hsd : Squarefree d := hs.of_mul_left
  have hse : Squarefree e := hs.of_mul_right
  refine ⟨t,ht,?_,?_,?_,?_⟩
  · rw [hsel,primaryPrimeFactors_prod hd hsd]
  · rw [hrem,primaryPrimeFactors_prod he hse]
  · have hc := stopping_occupancies_add ht
    rw [hrem,hremaining.2] at hc
    exact hc.symm
  · rw [hsel]
    exact hselected.2.2

end CubicFirstMoment

end

end OAI
