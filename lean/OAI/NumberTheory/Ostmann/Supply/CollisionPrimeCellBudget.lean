import OAI.NumberTheory.Ostmann.Construction.GoodPrimeLogCells
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDefectSelection

namespace OAI

/-! # Good cells from the proved collision-stability budget -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def collisionExceptionalPrimes (P : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ) : Finset ℕ :=
  P.filter (fun p => 1 / 4 < (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p))

theorem collisionExceptionalPrimes_log_mass (P : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ) (E : ℝ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card ≤ p)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E) :
    (∑ p ∈ collisionExceptionalPrimes P S T μ ν, Real.log (p : ℝ) / p) ≤ 4 * E := by
  have h := weighted_cost_exception_bound P (fun p => Real.log (p : ℝ) / p)
    (fun p => (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) (1 / 4)
    (fun p hp => div_nonneg (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le))
      (Nat.cast_nonneg _))
    (fun p hp => mul_nonneg (Nat.cast_nonneg _)
      (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p hp)))
  have heq : (∑ p ∈ P, Real.log (p : ℝ) / p *
      ((p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p))) =
      ∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
    field_simp
  rw [heq] at h
  change (1 / 4 : ℝ) * (∑ p ∈ collisionExceptionalPrimes P S T μ ν,
    Real.log (p : ℝ) / p) ≤ _ at h
  linarith

theorem collision_bad_cell_count (P I : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ) (E : ℝ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card ≤ p)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E) :
    ((badPrimeLogCells I (collisionExceptionalPrimes P S T μ ν)).card : ℝ) ≤ 64 * E := by
  have hm := collisionExceptionalPrimes_log_mass P S T μ ν E hprime hS hT hcard hbudget
  have hc := badPrimeLogCells_card I (collisionExceptionalPrimes P S T μ ν)
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
  linarith

theorem collision_retained_prime_balanced (P : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (p : ℕ) (hp : p ∈ P \ collisionExceptionalPrimes P S T μ ν) :
    (p : ℝ) / 3 ≤ (S p).card ∧ ((S p).card : ℝ) ≤ 2 * p / 3 := by
  obtain ⟨hpP, hpnot⟩ := Finset.mem_sdiff.mp hp
  have hsmall : (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) ≤ 1 / 4 := by
    by_contra! hh
    exact hpnot (Finset.mem_filter.mpr ⟨hpP, hh⟩)
  exact small_defect_balances_supports p (S p) (T p) (μ p) (ν p)
    (hS p hpP) (hT p hpP) (hcard p hpP) hsmall

end Ostmann

end OAI
