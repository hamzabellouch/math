import OAI.NumberTheory.Ostmann.QuadraticCenter.RationalReduction

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem reduced_common_center_from_lift_moments {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (a : ℕ) (ha : 0 < a)
    (t : ℕ → ℤ) (lift : ι → ℤ) (hinj : Function.Injective lift)
    (n lo cutoff k mass Z H : ℕ) (haZ : a < Z) (hlarge : ∀ p ∈ P, Z ≤ p)
    (hlifts : ∀ i, (lift i).natAbs ≤ H)
    (hlo : lo ≤ n + 1) (hpos : 0 < mass)
    (hmoment : mass + cutoff ^ (n + 1 - lo) *
        ∑ i, (matchingPrimes P a (lift i) t).card.descFactorial lo ≤
        ∑ i, (matchingPrimes P a (lift i) t).card.descFactorial (n + 1))
    (hbound : ∀ i j, i ≠ j → (lift i - lift j).natAbs < Z ^ (k + 1))
    (hgap : 2 * k * P.card ≤ cutoff ^ 2) :
    ∃ h : ℤ, ∃ m : ℕ, ∃ P₀ : Finset ℕ,
      0 < m ∧ m ≤ a ∧ IsCoprime h (m : ℤ) ∧ h.natAbs ≤ H ∧
      P₀ ⊆ P ∧ cutoff ≤ P₀.card ∧
      (mass : ℝ) ≤ 2 * (P.card : ℝ) * (P₀.card : ℝ) ^ n ∧
      ∀ p ∈ P₀, (p : ℤ) ∣ h - (m : ℤ) * t p := by
  obtain ⟨i, hsize, hmass⟩ := common_integer_lift_from_moments P hP a t lift hinj
    n lo cutoff k mass Z (by omega) hlarge hlo hpos hmoment hbound hgap
  obtain ⟨h, m, hmpos, hma, hcop, hnum, hmatch⟩ :=
    reduced_fraction_preserves_matching ha (lift i)
  refine ⟨h, m, matchingPrimes P a (lift i) t, hmpos, hma, hcop,
    hnum.trans (hlifts i), ?_, hsize, hmass, ?_⟩
  · intro p hp
    exact (mem_matchingPrimes.mp hp).1
  · intro p hp
    rcases mem_matchingPrimes.mp hp with ⟨hpP, hpd⟩
    have hpa : ¬ p ∣ a := Nat.not_dvd_of_pos_of_lt ha (haZ.trans_le (hlarge p hpP))
    exact hmatch p (hP p hpP) hpa (t p) hpd

end Ostmann.QuadraticCenter

end OAI
