import Mathlib
import OAI.Computability.QuantumFactoring.PrimalityCorrectness
import OAI.Computability.QuantumFactoring.CRTLevels

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The randomized splitter is invoked only after the prime and perfect-power
cases. Such an input has two genuinely different prime-power components. -/
lemma exists_distinct_components {m : ℕ} (hm : 2 ≤ m) (hc : ¬m.Prime)
    (hp : ¬Primality.PerfectPower m) : ∃ p₀ p₁ : Component m, p₁≠p₀ := by
  obtain ⟨p,hp₀⟩ := Nat.nonempty_primeFactors.mpr (by omega : 1 < m)
  by_cases hh : ∀ q∈m.primeFactors,q=p
  · have hs : m.factorization.support ⊆ {p} := by
      intro q hq
      rw [Nat.support_factorization] at hq
      exact Finset.mem_singleton.mpr (hh q hq)
    have hpow : p^(m.factorization p)=m := by
      have he := m.factorization.prod_of_support_subset hs (fun p e => p^e)
        (by intro i _; simp)
      simpa only [Finset.prod_singleton] using he.symm.trans (Nat.prod_factorization_pow_eq_self (by omega))
    have hprime := (Nat.mem_primeFactors.mp hp₀).1
    have hexp : m.factorization p≠0 := by
      apply Finsupp.mem_support_iff.mp
      simpa only [Nat.support_factorization] using hp₀
    by_cases he : m.factorization p=1
    · rw [he,pow_one] at hpow
      exact False.elim (hc (hpow ▸ hprime))
    · exact False.elim (hp ⟨p,m.factorization p,hprime.two_le,by omega,hpow⟩)
  · push Not at hh
    obtain ⟨q,hq,hne⟩ := hh
    exact ⟨⟨p,hp₀⟩,⟨q,hq⟩,fun h => hne (congrArg Subtype.val h)⟩

end ExactQuantumFactoring


end

end OAI
