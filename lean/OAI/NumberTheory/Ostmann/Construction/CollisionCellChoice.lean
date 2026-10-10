import OAI.NumberTheory.Ostmann.Supply.CollisionPrimeCellBudget

namespace OAI

/-! # A nearby cell with balanced retained primes -/

namespace Ostmann
open scoped Classical BigOperators

/-- The collision estimate and the published ordinary prime interval estimate
give a cell near every sufficiently large prescribed center. -/
theorem PublishedProgressionInput.collision_cell_near (P0 : PublishedProgressionInput) :
    ∃ H : ℝ, ∀ (P : Finset ℕ) (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
      (E target : ℝ), 0 ≤ E → H ≤ target →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, (S p).Nonempty) → (∀ p ∈ P, (T p).Nonempty) →
      (∀ p ∈ P, (S p).card + (T p).card = p) →
      (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E →
      (∀ h : ℕ, target ≤ h → (h : ℝ) ≤ target + 64 * E + 1 →
        primeLogCellSet 1 0 h ((h : ℝ) + 1) ⊆ P) →
      ∃ h : ℕ, target ≤ h ∧ (h : ℝ) ≤ target + 64 * E + 1 ∧
        1 / (4 * ((h : ℝ) + 1)) ≤
          ∑ p ∈ primeLogCellSet 1 0 h ((h : ℝ) + 1) \
            collisionExceptionalPrimes P S T μ ν, (p : ℝ)⁻¹ ∧
        (∀ p ∈ primeLogCellSet 1 0 h ((h : ℝ) + 1) \
            collisionExceptionalPrimes P S T μ ν,
          (p : ℝ) / 3 ≤ (S p).card ∧ ((S p).card : ℝ) ≤ 2 * p / 3) := by
  obtain ⟨H, hmass⟩ := P0.good_prime_log_cell_mass
  refine ⟨max H 1, ?_⟩
  intro P S T μ ν E target hE ht hprime hS hT hcard hbudget hcover
  let I := Finset.range ⌈target + 64 * E + 2⌉₊
  let bad := collisionExceptionalPrimes P S T μ ν
  let D := badPrimeLogCells I bad
  have hD : (D.card : ℝ) ≤ 64 * E :=
    collision_bad_cell_count P I S T μ ν E hprime hS hT (fun p hp => (hcard p hp).le) hbudget
  have ht0 : 0 ≤ target := by linarith [(le_max_right H 1).trans ht]
  obtain ⟨h, hgood, hlo, hhi⟩ := nat_cell_center_avoiding D target ht0
  have hupper : (h : ℝ) ≤ target + 64 * E + 1 := by linarith
  have hhI : h ∈ I := by
    apply Finset.mem_range.mpr
    have hceil := Nat.le_ceil (target + 64 * E + 2)
    have hh : (h : ℝ) < (⌈target + 64 * E + 2⌉₊ : ℕ) := by linarith
    exact_mod_cast hh
  refine ⟨h, hlo, hupper, hmass h ((le_max_left H 1).trans (ht.trans hlo)) I bad hhI hgood, ?_⟩
  intro p hp
  obtain ⟨hpQ, hpbad⟩ := Finset.mem_sdiff.mp hp
  exact collision_retained_prime_balanced P S T μ ν hS hT hcard p
    (Finset.mem_sdiff.mpr ⟨hcover h hlo hupper hpQ, hpbad⟩)

end Ostmann

end OAI
