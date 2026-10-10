import OAI.NumberTheory.TotientAsymptotic.FordCofactorCoordinates

namespace OAI

/-! The leading Ford prime is exactly the largest prime factor, with padding 1. -/
noncomputable section
namespace TotientAsymptotic

lemma fordPrime_zero_eq_largest (n : ℕ) : fordPrime n 0=largestPrimeFactor n := by
  apply le_antisymm
  · by_cases hi : 0 < n.primeFactorsList.length
    · rw [fordPrime_eq_get hi]
      exact primeFactor_le_largest (List.mem_reverse.mp (List.getElem_mem _))
    · have he : fordPrime n 0=1 := by
        unfold fordPrime
        rw [List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]
        rfl
      rw [he]
      exact le_max_left _ _
  · apply largestPrimeFactor_le_of_prime_divisors (fordPrime_pos n 0)
    intro p hp hpn hn
    have hm : p ∈ n.primeFactorsList.reverse :=
      List.mem_reverse.mpr ((Nat.mem_primeFactorsList_iff_dvd hn hp).mpr hpn)
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hm
    have hi' : i < n.primeFactorsList.length := by simpa using hi
    simpa only [fordPrime_eq_get hi'] using fordPrime_antitone (by omega) hi' (Nat.zero_le i)

end TotientAsymptotic

end

end OAI
