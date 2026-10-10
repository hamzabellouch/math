import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternGiantSupport
import OAI.NumberTheory.Ostmann.ZeroDensity.PageRegularAverage

namespace OAI

/-! # Conductor deletion for the separated diagonal modulus -/

namespace Ostmann
open scoped Classical BigOperators

/-- Prime factors in a regular block are disjoint from the frequency,
internal and spectator factors of the separated modulus. -/
theorem movingArithmeticModuli_coprime_product {I J : Type*} [Fintype I] [Fintype J]
    (r : ℕ) (p : I → ℕ) (P : Finset ℕ) (reg : J → ℕ)
    (hp : ∀ i, (p i).Prime) (hP : ∀ q ∈ P, q.Prime) (hreg : ∀ j, (reg j).Prime)
    (hr : ∀ j, (reg j).Coprime r)
    (hregP : ∀ j q, q ∈ P → reg j ≠ q) (hregp : ∀ j i, reg j ≠ p i) :
    (∏ j, reg j).Coprime (∏ b, movingArithmeticModuli r p P Finset.univ b) := by
  rw [movingArithmeticModuli_product]
  apply Nat.coprime_prod_left_iff.mpr
  intro j _
  apply (hr j).mul_right
  apply Nat.Coprime.mul_right
  · apply Nat.Coprime.pow_right
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    exact (hreg j).coprime_iff_not_dvd.mpr (fun h => hregP j q hq
      ((Nat.prime_dvd_prime_iff_eq (hreg j) (hP q hq)).mp h))
  · apply Nat.coprime_prod_right_iff.mpr
    intro i _
    exact (hreg j).coprime_iff_not_dvd.mpr (fun h => hregp j i
      ((Nat.prime_dvd_prime_iff_eq (hreg j) (hp i)).mp h))

/-- The prescribed deleted conductor prime is coprime to the full separated
arithmetic block. The frequency part is smaller than the deletion threshold. -/
theorem frequencyModel_deleted_prime_coprime {I : Type*} [Fintype I]
    (S : Finset ℤ) (n V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (P : Finset ℕ) (p : I → ℕ) (hP : ∀ q ∈ P, q.Prime) (hp : ∀ i, (p i).Prime)
    (q : ℕ) (hq : q.Prime) (hlarge : cutoff ≤ q)
    (hneqP : q ∉ P) (hneqp : ∀ i, q ≠ p i) :
    q.Coprime (∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
      p P Finset.univ b) := by
  rw [movingArithmeticModuli_product]
  apply ((prime_coprime_frequencyModelBase S V q n hq (hcut.trans_le hlarge) hS t).pow_right _).mul_right
  apply Nat.Coprime.mul_right
  · apply Nat.Coprime.pow_right
    apply Nat.coprime_prod_right_iff.mpr
    intro a ha
    apply hq.coprime_iff_not_dvd.mpr
    intro hd
    exact hneqP (((Nat.prime_dvd_prime_iff_eq hq (hP a ha)).mp hd).symm ▸ ha)
  · apply Nat.coprime_prod_right_iff.mpr
    intro i _
    exact hq.coprime_iff_not_dvd.mpr (fun hd => hneqp i
      ((Nat.prime_dvd_prime_iff_eq hq (hp i)).mp hd))

/-- The regular block contributes no Page correction under exactly the
conductor-prime deletion used to construct the original priors. -/
theorem frequencyModel_regular_page_projection {I J : Type*} [Fintype I] [Fintype J]
    (S : Finset ℤ) (n V cutoff : ℕ) (t : FrequencyTree (S × S) n)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ V) (hcut : V < cutoff)
    (P : Finset ℕ) (p : I → ℕ) (reg : J → ℕ) (z : Option PrimitiveRealZero)
    (hP : ∀ q ∈ P, q.Prime) (hp : ∀ i, (p i).Prime)
    (hreg : ∀ j, (reg j).Prime ∧ cutoff ≤ reg j)
    (hdeleteP : ∀ e, z = some e → ∀ q,
      deletedConductorPrime e.modulus cutoff = some q → q ∉ P)
    (hdeletep : ∀ e, z = some e → ∀ q,
      deletedConductorPrime e.modulus cutoff = some q → ∀ i, q ≠ p i)
    (hdeletereg : ∀ e, z = some e → ∀ q,
      deletedConductorPrime e.modulus cutoff = some q → ∀ j, q ≠ reg j) :
    pageAtModulus ((∏ j, reg j) *
      ∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2)) p P Finset.univ b) z =
    pageAtModulus (∏ b, movingArithmeticModuli (frequencyModelBase S n t ^ (n - 1 + 2))
      p P Finset.univ b) z := by
  apply pageAtModulus_regular_factor z _ _ cutoff
  · intro q hq hd
    obtain ⟨j, _, hj⟩ := (hq.prime.dvd_finsetProd_iff reg).mp hd
    have he := (Nat.prime_dvd_prime_iff_eq hq (hreg j).1).mp hj
    exact he.symm ▸ (hreg j).2
  · intro e he q hq hd
    have hs := deletedConductorPrime_spec hq
    have harith := frequencyModel_deleted_prime_coprime S n V cutoff t hS hcut P p hP hp
      q hs.1 hs.2.2 (hdeleteP e he q hq) (hdeletep e he q hq)
    have hr : q.Coprime (∏ j, reg j) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro j _
      exact hs.1.coprime_iff_not_dvd.mpr (fun h => hdeletereg e he q hq j
        ((Nat.prime_dvd_prime_iff_eq hs.1 (hreg j).1).mp h))
    exact hs.1.coprime_iff_not_dvd.mp (hr.mul_right harith) hd

end Ostmann

end OAI
