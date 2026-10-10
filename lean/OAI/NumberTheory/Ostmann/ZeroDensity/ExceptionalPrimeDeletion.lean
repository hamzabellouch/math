import OAI.NumberTheory.Ostmann.Characters.PrimitiveCharacterReduction
import OAI.NumberTheory.Ostmann.Characters.SparseBandMass

namespace OAI

/-! # Removing at most one prime excludes the exceptional conductor -/
namespace Ostmann
open scoped Classical BigOperators

theorem PrimitiveComplexCharacter.modulus_one_lt (χ : PrimitiveComplexCharacter) :
    1 < χ.modulus := by
  have : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hc : χ.character.conductor ≠ 1 := by
    intro h
    exact χ.nontrivial (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have hh := χ.primitive
  change χ.character.conductor = χ.modulus at hh
  have hp := χ.positive
  omega

theorem prime_mem_of_dvd_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q : ℕ) (hq : q.Prime) (hd : q ∣ ∏ p ∈ P, p) : q ∈ P := by
  induction P using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty] at hd
    exact (hq.ne_one (Nat.dvd_one.mp hd)).elim
  | @insert p P hp ih =>
    rw [Finset.prod_insert hp] at hd
    rcases hq.dvd_mul.mp hd with hd | hd
    · have he : q = p := ((Nat.dvd_prime (hP p (Finset.mem_insert_self _ _))).mp hd).resolve_left hq.ne_one
      simp [he]
    · exact Finset.mem_insert_of_mem (ih (fun r hr => hP r (Finset.mem_insert_of_mem hr)) hd)

theorem exists_prime_deletion_avoiding (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (d : ℕ) (hd : 1 < d) :
    ∃ Q : Finset ℕ, Q ⊆ P ∧ P.card ≤ Q.card + 1 ∧ ¬ d ∣ ∏ p ∈ Q, p := by
  by_cases hdiv : d ∣ ∏ p ∈ P, p
  · obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
    have hqP := prime_mem_of_dvd_prime_product P hP q hq (hqd.trans hdiv)
    refine ⟨P.erase q, Finset.erase_subset _ _, ?_, ?_⟩
    · have hh := Finset.card_erase_add_one hqP
      omega
    · intro hh
      have hmem := prime_mem_of_dvd_prime_product (P.erase q)
        (fun p hp => hP p (Finset.mem_erase.mp hp).2) q hq (hqd.trans hh)
      exact (Finset.mem_erase.mp hmem).1 rfl
  · exact ⟨P, Finset.Subset.refl _, by omega, hdiv⟩

theorem exists_exceptional_prime_deletion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (exception : Option PrimitiveComplexCharacter) :
    ∃ Q : Finset ℕ, Q ⊆ P ∧ P.card ≤ Q.card + 1 ∧
      ∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ p ∈ Q, p := by
  cases exception with
  | none => exact ⟨P, Finset.Subset.refl _, by omega, by intro ρ h; contradiction⟩
  | some ρ =>
    obtain ⟨Q, hQP, hcard, hd⟩ := exists_prime_deletion_avoiding P hP ρ.modulus ρ.modulus_one_lt
    exact ⟨Q, hQP, hcard, by intro σ h; cases Option.some.inj h; exact hd⟩

theorem prime_deletion_harmonic_loss (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQP : Q ⊆ P) (hcard : P.card ≤ Q.card + 1) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) + 1 / 2 := by
  have hc : (P \ Q).card ≤ 1 := by
    have hh := Finset.card_sdiff_of_subset hQP
    have hle := Finset.card_le_card hQP
    omega
  have hs : (∑ p ∈ P \ Q, (p : ℝ)⁻¹) ≤ 1 / 2 := by
    calc
      _ ≤ ∑ _p ∈ P \ Q, (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p (Finset.mem_sdiff.mp hp).1).two_le
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
      _ ≤ 1 / 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hc' : ((P \ Q).card : ℝ) ≤ 1 := by exact_mod_cast hc
        linarith
  have hsum : (∑ p ∈ P \ Q, (p : ℝ)⁻¹) + (∑ p ∈ Q, (p : ℝ)⁻¹) =
      (∑ p ∈ P, (p : ℝ)⁻¹) := Finset.sum_sdiff hQP
  linarith

theorem exists_exceptional_prime_deletion_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (exception : Option PrimitiveComplexCharacter) (L : ℝ) (hL : 50 ≤ L)
    (hmass : (69 / 100 : ℝ) * L ≤ ∑ p ∈ P, (p : ℝ)⁻¹) :
    ∃ Q : Finset ℕ, Q ⊆ P ∧
      (17 / 25 : ℝ) * L ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
      ∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ p ∈ Q, p := by
  obtain ⟨Q, hQP, hcard, havoid⟩ := exists_exceptional_prime_deletion P hP exception
  refine ⟨Q, hQP, ?_, havoid⟩
  have hh := prime_deletion_harmonic_loss P Q hP hQP hcard
  linarith

end Ostmann

end OAI
