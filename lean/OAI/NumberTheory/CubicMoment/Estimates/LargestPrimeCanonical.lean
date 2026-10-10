import OAI.NumberTheory.CubicMoment.Estimates.LargestPrimeReindex

namespace OAI

/-! Canonical functions for the exact largest-prime change of variables.
They allow predicates on the original product to be rewritten after the
finite reindexing, without a choice-dependent coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largestPrimeChoice (n : Eisenstein) : Eisenstein :=
  if h : (primaryPrimeFactors n).Nonempty then selectedLargestPrime (primaryPrimeFactors n) h else 1

def largestPrimeRemainder (n : Eisenstein) : Eisenstein :=
  ∏ q ∈ (primaryPrimeFactors n).erase (largestPrimeChoice n), q

lemma largestPrimeChoice_spec {n : Eisenstein} (h : (primaryPrimeFactors n).Nonempty) :
    largestPrimeChoice n ∈ primaryPrimeFactors n ∧
      largestPrimePredicate primeTieCode (primaryPrimeFactors n) (largestPrimeChoice n) := by
  simpa only [largestPrimeChoice,dite_eq_left h] using selectedLargestPrime_spec (primaryPrimeFactors n) h

lemma largestPrimeChoice_prime_mul {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c)
    (hl : largestPrimePredicate primeTieCode (primaryPrimeFactors c) p) :
    largestPrimeChoice (p*c) = p ∧ largestPrimeRemainder (p*c) = c := by
  have hf := primaryPrimeFactors_prime_mul hp hc hs hpc
  have hp_mem : p ∈ primaryPrimeFactors (p*c) := by rw [hf]; exact Finset.mem_insert_self _ _
  have hne : (primaryPrimeFactors (p*c)).Nonempty := ⟨p,hp_mem⟩
  have hlarge : largestPrimePredicate primeTieCode (primaryPrimeFactors (p*c)) p := by
    rw [hf]
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Or.inr ⟨rfl,le_rfl⟩
    · exact hl q hq
  have hchoice : largestPrimeChoice (p*c) = p :=
    largestPrime_unique primeTieCode_injective (largestPrimeChoice_spec hne).1 hp_mem
      (largestPrimeChoice_spec hne).2 hlarge
  refine ⟨hchoice,?_⟩
  have hnot : p ∉ primaryPrimeFactors c := fun h => hpc (primaryPrimeFactor_spec hc h).2
  rw [largestPrimeRemainder,hchoice,hf,Finset.erase_insert hnot,primaryPrimeFactors_prod hc hs]

lemma largestPrimeChoice_mul_eq_iff {p c : Eisenstein} (hp : primaryPrime p)
    (hc : primary c) (hs : Squarefree c) (hpc : ¬p ∣ c) :
    largestPrimeChoice (p*c) = p ↔ largestPrimePredicate primeTieCode (primaryPrimeFactors c) p := by
  constructor
  · intro he q hq
    have hf := primaryPrimeFactors_prime_mul hp hc hs hpc
    have hmem : p ∈ primaryPrimeFactors (p*c) := by rw [hf]; exact Finset.mem_insert_self _ _
    have hl := (largestPrimeChoice_spec (show (primaryPrimeFactors (p*c)).Nonempty from ⟨p,hmem⟩)).2
    rw [he] at hl
    exact hl q (by rw [hf]; exact Finset.mem_insert_of_mem hq)
  · exact fun h => (largestPrimeChoice_prime_mul hp hc hs hpc h).1

theorem sum_largestPrime_canonical_reindex (D : Finset Eisenstein) (B : ℝ)
    (hD : ∀ d ∈ D, primary d ∧ Squarefree d ∧ norm d ≤ B)
    (hne : ∀ d ∈ D, (primaryPrimeFactors d).Nonempty)
    (F : Eisenstein → Eisenstein → Eisenstein → ℂ) :
    (∑ d ∈ D, F d (largestPrimeChoice d) (largestPrimeRemainder d)) =
      ∑ t ∈ ((primeCutoff B) ×ˢ (primaryElementBall B)).filter
        (fun t => t.1*t.2 ∈ D ∧ ¬t.1 ∣ t.2 ∧
          largestPrimePredicate primeTieCode (primaryPrimeFactors t.2) t.1),
        F (t.1*t.2) t.1 t.2 := by
  rw [sum_largestPrime_reindex D B hD hne]
  apply Finset.sum_congr rfl
  intro t ht
  obtain ⟨ht,hcond⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp,hc⟩ := Finset.mem_product.mp ht
  have h := largestPrimeChoice_prime_mul (mem_primeCutoff.mp hp).1
    (mem_primaryElementBall.mp hc).1 (squarefree_mul_iff.mp (hD _ hcond.1).2.1).2.2
    hcond.2.1 hcond.2.2
  rw [h.1,h.2]

end CubicFirstMoment

end

end OAI
