import OAI.NumberTheory.TotientAsymptotic.PublishedComparison
import OAI.NumberTheory.TotientAsymptotic.DyadicCollisionMass

namespace OAI

/-!
Ford, The distribution of totients, revised arXiv:1104.3264v2 (2013),
Lemma 2.6, p. 9. The author-hosted PDF states uniformity for x > 3 and
S > 2: https://www.ford126.web.illinois.edu/wwwpapers/totients.pdf .
Only this count of exceptional primes is assumed. Reciprocal-weight and
actual good-witness discard estimates are derived separately.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def nonNormalPrimes (S : ℝ) (N : ℕ) : Finset ℕ :=
  (Nat.primesLE N).filter (fun p => ¬ IsNormalPrime S p)

/-- The precise published exceptional-prime estimate, at integer endpoints. -/
def FordLemma26Input : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 2 < S → ∀ N : ℕ, 3 < N →
    ((nonNormalPrimes S N).card : ℝ) ≤
      C*(N : ℝ)/Real.log N*(B N)^5*(Real.log S)^(-1/6 : ℝ)

lemma normal_two {S : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S) : IsNormalPrime S 2 := by
  refine ⟨Nat.prime_two,?_,?_⟩
  · simp only [show (2 : ℕ)-1=1 from rfl,omegaIn,Nat.primeFactorsList_one,List.filter_nil,
      List.length_nil,Nat.cast_zero]
    linarith
  · intro U T hSU hUT hT
    norm_num at hT
    linarith

end TotientAsymptotic

end

end OAI
