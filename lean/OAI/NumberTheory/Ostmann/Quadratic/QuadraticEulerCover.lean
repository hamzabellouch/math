import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMainCoefficients

namespace OAI

/-! # A finite Euler product covering the original small squarefree indices -/

namespace Ostmann

open scoped Classical BigOperators

private def quadraticEulerPrimes (D K : ℕ) : Finset ℕ :=
  (Finset.Icc 1 K).filter (fun p => p.Prime ∧ p ≠ 2 ∧ ¬p ∣ D)

private def quadraticEulerCover (D K : ℕ) : ℕ :=
  ∏ p ∈ quadraticEulerPrimes D K, p

private theorem prime_product_squarefree (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) : Squarefree (∏ p ∈ P, p) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hprime := hP p (Finset.mem_insert_self p P)
    have hrest : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply (Nat.coprime_primes hprime (hrest q hq)).mpr
      intro heq
      exact hp (heq ▸ hq)
    rw [Finset.prod_insert hp]
    exact (Nat.squarefree_mul hcop).mpr ⟨hprime.squarefree, ih hrest⟩

private theorem quadraticEulerCover_squarefree (D K : ℕ) :
    Squarefree (quadraticEulerCover D K) := by
  apply prime_product_squarefree
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1

private theorem quadraticEulerCover_odd (D K : ℕ) : Odd (quadraticEulerCover D K) := by
  have hh : ∀ P : Finset ℕ, (∀ p ∈ P, Odd p) → Odd (∏ p ∈ P, p) := by
    intro P hP
    induction P using Finset.induction_on with
    | empty => simp
    | @insert p P hp ih =>
      rw [Finset.prod_insert hp]
      exact (hP p (Finset.mem_insert_self p P)).mul
        (ih (fun q hq => hP q (Finset.mem_insert_of_mem hq)))
  apply hh
  intro p hp
  obtain ⟨_, hprime, htwo, _⟩ := Finset.mem_filter.mp hp
  exact hprime.odd_of_ne_two htwo

private theorem quadraticEulerCover_coprime (D K : ℕ) :
    D.Coprime (quadraticEulerCover D K) := by
  apply Nat.Coprime.prod_right
  intro p hp
  obtain ⟨_, hprime, _, hD⟩ := Finset.mem_filter.mp hp
  exact (hprime.coprime_iff_not_dvd.mpr hD).symm

private theorem quadraticEulerCover_covers {D K : ℕ} (hD : D ≠ 0) :
    oddSquarefreeRange K ⊆ (D * quadraticEulerCover D K).divisors := by
  intro b hb
  obtain ⟨hrange, hodd, hsf⟩ := Finset.mem_filter.mp hb
  have hn : D * quadraticEulerCover D K ≠ 0 :=
    mul_ne_zero hD (quadraticEulerCover_squarefree D K).ne_zero
  have hdiv : (∏ p ∈ b.primeFactors, p) ∣ D * quadraticEulerCover D K := by
    apply (Nat.prod_primeFactors_dvd_iff hn).mpr
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpdiv := Nat.dvd_of_mem_primeFactors hp
    have hpDR : p ∣ D * quadraticEulerCover D K := by
      by_cases hpD : p ∣ D
      · exact dvd_mul_of_dvd_left hpD _
      · have hpK : p ≤ K := (Nat.le_of_dvd (Finset.mem_Icc.mp hrange).1 hpdiv).trans
          (Finset.mem_Icc.mp hrange).2
        have hp2 : p ≠ 2 := by
          intro heq
          subst p
          exact hodd.not_two_dvd_nat hpdiv
        have hpP : p ∈ quadraticEulerPrimes D K :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprime.pos, hpK⟩, hprime, hp2, hpD⟩
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun p => p) hpP) _
    exact Nat.mem_primeFactors.mpr ⟨hprime, hpDR, hn⟩
  exact Nat.mem_divisors.mpr ⟨by simpa only [Nat.prod_primeFactors_of_squarefree hsf] using hdiv, hn⟩

/-- The literal alpha and beta coefficients agree at every index below the
cutoff. There is no auxiliary covering hypothesis. -/
theorem quadratic_main_coefficient_eq {D K w : ℕ} (hD : Squarefree D)
    (hDo : Odd D) (hw : w ≤ K) : quadraticMainAlpha D K w = quadraticMainBeta D K w :=
  quadratic_main_coefficient_eq_of_cover hD (quadraticEulerCover_squarefree D K)
    (quadraticEulerCover_coprime D K) hDo (quadraticEulerCover_odd D K)
    (quadraticEulerCover_covers hD.ne_zero) hw

 theorem quadratic_main_gamma_zero {D K w : ℕ} (hD : Squarefree D)
    (hDo : Odd D) (hw : w ≤ K) : quadraticMainGamma D K w = 0 := by
  rw [quadraticMainGamma, quadratic_main_coefficient_eq hD hDo hw, sub_self]

end Ostmann

end OAI
