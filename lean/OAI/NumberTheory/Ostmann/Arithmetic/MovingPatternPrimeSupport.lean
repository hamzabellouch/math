import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPriorRanges
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternFrequencyModulus
import OAI.NumberTheory.Ostmann.Arithmetic.MovingArithmeticModulus

namespace OAI

/-! # The concrete prime support of a nonzero original pattern coefficient -/

namespace Ostmann
open scoped Classical BigOperators

/-- The original coefficient can only be nonzero on its representative
product prior. This implication does not replace repeated samples by
independent ones. -/
theorem movingPattern_nonzero_prior {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (E : ℝ)
    (hprime : ∀ a, (prime a).Prime) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern G x ≠ 0) :
    productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0 := by
  intro hz
  have h := movingPattern_coefficient_zero_of_prior e μ ν prime pattern rep E
    hprime hμ hν hbound x hz
  apply hx
  change _ * movingPatternInjectionGuard e G x = 0
  rw [h, zero_mul]

theorem movingPattern_nonzero_internal_injective {A B C : Type*} [Fintype B] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (hinj : Function.Injective prime)
    (pattern : Bool × MovingSampleIndex n → C)
    (G : (Fin (N + 1) → A) → ℂ) (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern G x ≠ 0) :
    Function.Injective (fun c => prime (x (e.symm (.inr c)))) := by
  have hg : movingPatternInjectionGuard e G x ≠ 0 := (mul_ne_zero_iff.mp hx).2
  exact hinj.comp (movingPatternInjectionGuard_nonzero e G x hg).1

/-- All prime coprimality conditions against the actual history modulus
follow from the lower endpoint of the original product prior. -/
theorem movingPattern_prior_frequency_coprime {A B C : Type*}
    {N n : ℕ} (e : Fin (N + 1) ≃ B ⊕ C)
    (μ : ℕ → A → ℝ) (ν : B → A → ℝ) (prime : A → ℕ)
    (hprime : ∀ a, (prime a).Prime)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (S : Finset ℤ) (V : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V)
    (hμ : ∀ j a, μ j a ≠ 0 → V < prime a)
    (hν : ∀ j a, ν j a ≠ 0 → V < prime a)
    (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
    ∀ i, (prime (x i)).Coprime (frequencyModelBase S n t) := by
  intro i
  have hi := Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ _)
  apply prime_coprime_frequencyModelBase S V (prime (x i)) n (hprime _)
  · cases he : e i with
    | inl b => exact hν b (x i) (by simpa only [he, Sum.elim_inl] using hi)
    | inr c => exact hμ _ (x i) (by simpa only [he, Sum.elim_inr] using hi)
  · exact hS

noncomputable def movingPatternInternalPrimes {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (x : Fin (N + 1) → A) : Finset ℕ :=
  Finset.univ.image (fun c : C => prime (x (e.symm (.inr c))))

theorem movingPatternInternalPrimes_prime {A B C : Type*} [Fintype C] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (x : Fin (N + 1) → A) :
    ∀ p ∈ movingPatternInternalPrimes e prime x, p.Prime := by
  intro p hp
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hp
  exact hprime _

/-- Distinct spectators and the prior's elementary prime coprimality give
pairwise coprimality of every actual giant CRT block. -/
theorem movingPattern_prime_moduli_coprime {A B C I : Type*} [Fintype C] [Fintype I] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (x : Fin (N + 1) → A) (r : ℕ) (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hr : ∀ i, r.Coprime (prime (x i))) (hrp : ∀ i, r.Coprime (p i))
    (hsep : ∀ i j, prime (x j) ≠ p i) :
    Pairwise (fun a b =>
      (movingArithmeticModuli r p (movingPatternInternalPrimes e prime x) Finset.univ a).Coprime
      (movingArithmeticModuli r p (movingPatternInternalPrimes e prime x) Finset.univ b)) := by
  apply movingArithmeticModuli_coprime r p (movingPatternInternalPrimes e prime x) Finset.univ
    (movingPatternInternalPrimes_prime e prime hprime x) (fun i _ => hp i)
    (fun _ _ _ _ h => hinj h)
  · intro q hq
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    exact hr _
  · exact fun i _ => hrp i
  · intro q hq i _
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
    exact hsep i _

end Ostmann

end OAI
