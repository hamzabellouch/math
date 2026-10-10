import OAI.NumberTheory.CubicMoment.Estimates.LargestPrimeCanonical
import OAI.NumberTheory.CubicMoment.Estimates.LargestPrimeRoles

namespace OAI

/-! Exact identification of the selected-bin largest-prime role. The
largest prime of the full product is used throughout; its occurrence in
the selected divisor is proved equivalent to the free-prime row test. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_mul_union {r d : Eisenstein} (hr : primary r) (hd : primary d) :
    primaryPrimeFactors (r*d) = primaryPrimeFactors r ∪ primaryPrimeFactors d := by
  ext p
  rw [primaryPrime_mem_factors_iff (primary_mul hr hd),Finset.mem_union,
    primaryPrime_mem_factors_iff hr,primaryPrime_mem_factors_iff hd]
  constructor
  · rintro ⟨hp,hpd⟩
    rcases hp.2.dvd_or_dvd hpd with hpr | hpd
    · exact Or.inl ⟨hp,hpr⟩
    · exact Or.inr ⟨hp,hpd⟩
  · rintro (⟨hp,hpr⟩ | ⟨hp,hpd⟩)
    · exact ⟨hp,dvd_mul_of_dvd_left hpr d⟩
    · exact ⟨hp,dvd_mul_of_dvd_right hpd r⟩

lemma largestPrimeChoice_dvd_right_iff {r d : Eisenstein}
    (hr : primary r) (hd : primary d) (hne : (primaryPrimeFactors d).Nonempty) :
    largestPrimeChoice (r*d) ∣ d ↔ largestPrimeChoice (r*d) = largestPrimeChoice d := by
  have hsub : primaryPrimeFactors d ⊆ primaryPrimeFactors (r*d) := by
    rw [primaryPrimeFactors_mul_union hr hd]
    exact Finset.subset_union_right
  have hne' : (primaryPrimeFactors (r*d)).Nonempty := hne.mono hsub
  have hfull := largestPrimeChoice_spec hne'
  have hright := largestPrimeChoice_spec hne
  have hp := (primaryPrimeFactor_spec (primary_mul hr hd) hfull.1).1
  constructor
  · intro hdiv
    have hm : largestPrimeChoice (r*d) ∈ primaryPrimeFactors d :=
      (primaryPrime_mem_factors_iff hd).mpr ⟨hp,hdiv⟩
    exact largestPrime_unique primeTieCode_injective hm hright.1
      (fun q hq => hfull.2 q (hsub hq)) hright.2
  · intro he
    rw [he]
    exact (primaryPrimeFactor_spec hd hright.1).2

lemma selected_largest_free_prime_iff {r p c : Eisenstein}
    (hr : primary r) (hp : primaryPrime p) (hc : primary c)
    (hs : Squarefree (r*(p*c)))
    (hl : largestPrimePredicate primeTieCode (primaryPrimeFactors c) p) :
    largestPrimeChoice (r*(p*c)) ∣ p*c ↔
      largestPrimePredicate primeTieCode (primaryPrimeFactors (r*c)) p := by
  have hsd : Squarefree (p*c) := (squarefree_mul_iff.mp hs).2.2
  have hsc : Squarefree c := (squarefree_mul_iff.mp hsd).2.2
  have hpc : ¬p ∣ c := by
    have hcop : IsCoprime p c := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hsd).1
    exact fun h => hp.2.not_isUnit (hcop.isUnit_of_dvd h)
  have he : r*(p*c) = p*(r*c) := by ring
  have hs' : Squarefree (p*(r*c)) := he ▸ hs
  have hsrc : Squarefree (r*c) := (squarefree_mul_iff.mp hs').2.2
  have hprc : ¬p ∣ r*c := by
    have hcop : IsCoprime p (r*c) :=
      isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs').1
    exact fun h => hp.2.not_isUnit (hcop.isUnit_of_dvd h)
  have hchoice := (largestPrimeChoice_prime_mul hp hc hsc hpc hl).1
  have hne : (primaryPrimeFactors (p*c)).Nonempty := by
    rw [primaryPrimeFactors_prime_mul hp hc hsc hpc]
    exact Finset.insert_nonempty _ _
  rw [largestPrimeChoice_dvd_right_iff hr (primary_mul hp.1 hc) hne,hchoice,he]
  exact largestPrimeChoice_mul_eq_iff hp (primary_mul hr hc) hsrc hprc

/-- Reindexing the selected-bin role retains the original divisor
support and introduces exactly the full-complement largest-prime test. -/
theorem selected_largest_sum_reindex (r : Eisenstein) (hr : primary r)
    (D : Finset Eisenstein) (B : ℝ)
    (hD : ∀ d ∈ D, primary d ∧ Squarefree (r*d) ∧ norm d ≤ B)
    (hne : ∀ d ∈ D, (primaryPrimeFactors d).Nonempty)
    (F : Eisenstein → ℂ) :
    (∑ d ∈ D, if largestPrimeChoice (r*d) ∣ d then F d else 0) =
      ∑ t ∈ ((primeCutoff B) ×ˢ (primaryElementBall B)).filter
        (fun t => t.1*t.2 ∈ D ∧ ¬t.1 ∣ t.2 ∧
          largestPrimePredicate primeTieCode (primaryPrimeFactors t.2) t.1),
        if largestPrimePredicate primeTieCode (primaryPrimeFactors (r*t.2)) t.1
          then F (t.1*t.2) else 0 := by
  rw [sum_largestPrime_reindex D B
    (fun d hd => ⟨(hD d hd).1,(squarefree_mul_iff.mp (hD d hd).2.1).2.2,(hD d hd).2.2⟩) hne]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨ht,hcond⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp,hc⟩ := Finset.mem_product.mp ht
  rw [selected_largest_free_prime_iff hr (mem_primeCutoff.mp hp).1
    (mem_primaryElementBall.mp hc).1 (hD _ hcond.1).2.1 hcond.2.2]

end CubicFirstMoment

end

end OAI
