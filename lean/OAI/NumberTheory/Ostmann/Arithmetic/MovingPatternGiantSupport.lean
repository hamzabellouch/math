import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeSupport
import OAI.NumberTheory.Ostmann.ZeroDensity.PageConductorProjection

namespace OAI

/-! # Range separation and conductor deletion for the actual giant comparison -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPattern_prior_lower {A B C : Type*} {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c}) (lo : ℕ)
    (hμ : ∀ j a, μ j a ≠ 0 → lo < prime a)
    (hν : ∀ j a, ν j a ≠ 0 → lo < prime a)
    (x : Fin (N + 1) → A)
    (hx : productPrior (fun i => Sum.elim ν
      (fun c => μ (movingSampleTier (rep c).val.2)) (e i)) x ≠ 0) :
    ∀ i, lo < prime (x i) := by
  intro i
  have hi := Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ _)
  cases he : e i with
  | inl b => exact hν b (x i) (by simpa only [he, Sum.elim_inl] using hi)
  | inr c => exact hμ _ (x i) (by simpa only [he, Sum.elim_inr] using hi)

/-- The original prior supplies all prime-range and frequency-unit conditions
for the giant comparison, including the protected bulk coordinates. -/
theorem movingPattern_prior_giant_support {A B C I : Type*}
    [Fintype A] [Fintype B] [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (μ : ℕ → A → ℝ) (ν : B → A → ℝ)
    (prime : A → ℕ) (hinj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (pattern : Bool × MovingSampleIndex n → C)
    (rep : ∀ c, {i : Bool × MovingSampleIndex n // pattern i = c})
    (tier : A → ℕ) (tierB : B → ℕ)
    (hμtier : ∀ j, j < n → ∀ a, μ j a ≠ 0 → tier a = j)
    (hνtier : ∀ j a, ν j a ≠ 0 → tier a = tierB j) (hB : ∀ b, n ≤ tierB b)
    (S : Finset ℤ) (V lo : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hVlo : V ≤ lo)
    (hμlo : ∀ j a, μ j a ≠ 0 → lo < prime a)
    (hνlo : ∀ j a, ν j a ≠ 0 → lo < prime a)
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hplo : ∀ i, p i ≤ lo)
    (E : ℝ) (hμ : ∀ j a, 0 ≤ μ j a) (hν : ∀ j a, 0 ≤ ν j a)
    (hbound : ∀ j a, (prime a : ℝ) * μ j a ≤ E)
    (x : Fin (N + 1) → A)
    (hx : movingOriginalPatternWeight e μ ν prime n pattern (fun _ => 1) x ≠ 0) :
    let R := frequencyModelBase S n t
    (∀ i j, (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e i) ≠
      (Sum.elim tierB (fun c => movingSampleTier (rep c).val.2)) (e j) →
        prime (x i) ≠ prime (x j)) ∧
    (∀ i, V < prime (x i)) ∧
    (∀ i, IsCoprime (prime (x i) : ℤ) (R : ℤ)) ∧
    (∀ i, (R ^ (n - 1 + 2)).Coprime (prime (x i))) ∧
    (∀ i j, (prime (x j) : ZMod (p i)) ≠ 0) := by
  intro R
  have hprior := movingPattern_nonzero_prior e μ ν prime pattern rep E hprime hμ hν hbound
    (fun _ => 1) x hx
  have hlarge := movingPattern_prior_lower e μ ν prime pattern rep lo hμlo hνlo x hprior
  have hlargeV (i) : V < prime (x i) := hVlo.trans_lt (hlarge i)
  have hcop := movingPattern_prior_frequency_coprime e μ ν prime hprime pattern rep S V t hS
    (fun j a ha => hVlo.trans_lt (hμlo j a ha))
    (fun j a ha => hVlo.trans_lt (hνlo j a ha)) x hprior
  refine ⟨(movingPattern_prior_prime_separation e μ ν pattern rep tier tierB prime hinj
    hμtier hνtier hB x hprior).1, hlargeV, ?_, ?_, ?_⟩
  · intro i
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast]
    exact hcop i
  · intro i
    exact ((hcop i).pow_right _).symm
  · intro i j hz
    have hd := (ZMod.natCast_eq_zero_iff (prime (x j)) (p i)).mp hz
    have heq := (Nat.prime_dvd_prime_iff_eq (hp i) (hprime _)).mp hd
    have hlt := (hplo i).trans_lt (hlarge j)
    omega

/-- Deleting the selected large conductor prime confines the actual Page
correction to the history-frequency modulus, including all its powers. -/
theorem frequencyModel_page_projection {I : Type*} [Fintype I]
    (S : Finset ℤ) (n V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (P : Finset ℕ) (p : I → ℕ) (z : Option PrimitiveRealZero)
    (hP : ∀ q ∈ P, q.Prime ∧ cutoff ≤ q) (hp : ∀ i, (p i).Prime ∧ cutoff ≤ p i)
    (hdeleteP : ∀ e, z = some e → ∀ q, deletedConductorPrime e.modulus cutoff = some q → q ∉ P)
    (hdeletep : ∀ e, z = some e → ∀ q, deletedConductorPrime e.modulus cutoff = some q → ∀ i, q ≠ p i) :
    pageAtModulus (∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
      p P Finset.univ b) z = pageAtModulus (frequencyModelBase S n t ^ (n - 1 + 2)) z := by
  let R := frequencyModelBase S n t ^ (n - 1 + 2)
  let C := (∏ q ∈ P, q) ^ 2 * ∏ i, p i
  have heq : (∏ b, movingArithmeticModuli R p P Finset.univ b) = R * C :=
    movingArithmeticModuli_product R p P Finset.univ
  change pageAtModulus (∏ b, movingArithmeticModuli R p P Finset.univ b) z = _
  rw [heq]
  apply pageAtModulus_mul_eq z R C cutoff
  · intro q hq hd
    by_contra hh
    have hVq : V < q := hcut.trans_le (Nat.le_of_not_lt hh)
    have hc := (prime_coprime_frequencyModelBase S V q n hq hVq hS t).pow_right (n - 1 + 2)
    exact (hq.coprime_iff_not_dvd.mp hc) hd
  · intro q hq hd
    rcases hq.dvd_mul.mp hd with hleft | hright
    · obtain ⟨a, ha, hqa⟩ := (hq.prime.dvd_finsetProd_iff (fun a : ℕ => a)).mp
        (hq.dvd_of_dvd_pow hleft)
      have he := (Nat.prime_dvd_prime_iff_eq hq (hP a ha).1).mp hqa
      simpa only [he] using (hP a ha).2
    · obtain ⟨i, _, hqi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hright
      have he := (Nat.prime_dvd_prime_iff_eq hq (hp i).1).mp hqi
      simpa only [he] using (hp i).2
  · intro e he q hq hd
    have hprime := (deletedConductorPrime_spec hq).1
    rcases hprime.dvd_mul.mp hd with hleft | hright
    · obtain ⟨a, ha, hqa⟩ := (hprime.prime.dvd_finsetProd_iff (fun a : ℕ => a)).mp
        (hprime.dvd_of_dvd_pow hleft)
      have heq := (Nat.prime_dvd_prime_iff_eq hprime (hP a ha).1).mp hqa
      exact hdeleteP e he q hq (heq.symm ▸ ha)
    · obtain ⟨i, _, hqi⟩ := (hprime.prime.dvd_finsetProd_iff p).mp hright
      exact hdeletep e he q hq i ((Nat.prime_dvd_prime_iff_eq hprime (hp i).1).mp hqi)

end Ostmann

end OAI
