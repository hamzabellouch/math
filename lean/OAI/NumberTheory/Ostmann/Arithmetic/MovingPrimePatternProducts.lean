import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternArithmeticComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeInternalProduct

namespace OAI

/-! # The original pattern products in the two-prime environment -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingPatternPrimeLineProduct {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → A) : ℂ :=
  ∏ c, (movingSampledInternalPrimeProbability prime hprime
    (movingPatternFinData e n t small bulk pattern) x (e.symm (.inr c)) : ℂ)

noncomputable def movingPatternPrimeHaarProduct {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → A) : ℂ :=
  let T := movingPatternFinData e n t small bulk pattern
  letI : ∀ c : C, Fact (prime (x (e.symm (.inr c)))).Prime := fun _ => ⟨hprime _⟩
  ∏ c, movingInternalPrimeAverage (fun i => prime (x i)) T (prime (x (e.symm (.inr c))))

noncomputable def movingPatternPrimeFlagProduct {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (x : Fin (N + 1) → A) : ℂ :=
  let T := movingPatternFinData e n t small bulk pattern
  let base := movingPatternFinRepresentative e n t small bulk pattern rep
  ∏ c, (internalLineFlagWeight false (prime (x (e.symm (.inr c))))
    (fun s => arithmeticTestFlag (lineTestPolynomials
      (movingIndexedLine T (e.symm (.inr c)) (base c))
      ⟨(base c).1, (base c).2.val⟩ s = 0)) : ℂ)

end Ostmann

end OAI
