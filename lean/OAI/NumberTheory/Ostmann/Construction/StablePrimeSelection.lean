import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDefectSelection

namespace OAI

/-! # Selecting stable primes directly from the total collision budget -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def stableBiasPrimes (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ) (δ : ℝ) : Finset ℕ :=
  P.filter fun p => (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) ≤ δ ^ 2 / 64

theorem stableBiasPrimes_weight (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ) (δ E : ℝ) (hδ : 0 < δ)
    (hP : ∀ p ∈ P, p.Prime) (hS : ∀ p ∈ P, (S p).Nonempty)
    (hT : ∀ p ∈ P, (T p).Nonempty) (hcard : ∀ p ∈ P, (S p).card + (T p).card ≤ p)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E) :
    (∑ p ∈ P, Real.log (p : ℝ) / p) - 64 * E / δ ^ 2 ≤
      ∑ p ∈ stableBiasPrimes P S T μ ν δ, Real.log (p : ℝ) / p := by
  let w := fun p : ℕ => Real.log (p : ℝ) / p
  let cost := fun p : ℕ => (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)
  have hw (p : ℕ) (hp : p ∈ P) : 0 ≤ w p :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)) (Nat.cast_nonneg _)
  have hc (p : ℕ) (hp : p ∈ P) : 0 ≤ cost p :=
    mul_nonneg (Nat.cast_nonneg _) (collisionDefect_nonneg (S p) (T p) (μ p) (ν p)
      (hS p hp) (hT p hp) (hcard p hp))
  have hsum : (∑ p ∈ P, w p * cost p) =
      ∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
    dsimp [w, cost]
    field_simp
  have hb := weighted_cost_exception_bound P w cost (δ ^ 2 / 64) hw hc
  rw [hsum] at hb
  have hbad : (∑ p ∈ P.filter (fun p => ¬ cost p ≤ δ ^ 2 / 64), w p) ≤ 64 * E / δ ^ 2 := by
    apply (le_div_iff₀ (pow_pos hδ 2)).mpr
    have hb' : δ ^ 2 / 64 * (∑ p ∈ P.filter (fun p => ¬ cost p ≤ δ ^ 2 / 64), w p) ≤ E := by
      simpa only [not_le] using hb.trans hbudget
    nlinarith only [hb']
  exact weighted_good_mass P w (fun p => cost p ≤ δ ^ 2 / 64) _ _ le_rfl hbad

theorem stableBiasPrimes_pointwise (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν f g : ℕ → ℕ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδU : δ ≤ 1)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (hf : ∀ p ∈ P, ∀ r ∈ S p, |f p r| ≤ 1)
    (hg : ∀ p ∈ P, ∀ r ∈ T p, |g p r| ≤ 1) :
    ∀ p ∈ stableBiasPrimes P S T μ ν δ,
      (p : ℝ) / 3 ≤ (S p).card ∧ ((S p).card : ℝ) ≤ 2 * p / 3 ∧
      |residueTestError (S p) (μ p) (f p)| ≤ δ / 8 ∧
      |residueTestError (T p) (ν p) (g p)| ≤ δ / 8 := by
  intro p hp
  obtain ⟨hpP, hsmall⟩ := Finset.mem_filter.mp hp
  have hsmall' : (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) ≤ 1 / 4 := by
    have hδsq : δ ^ 2 ≤ 1 := by nlinarith
    linarith
  have hbalanced := small_defect_balances_supports p (S p) (T p) (μ p) (ν p)
    (hS p hpP) (hT p hpP) (hcard p hpP) hsmall'
  have herrors := small_defect_controls_test_errors p (S p) (T p) (μ p) (ν p) (f p) (g p)
    (hS p hpP) (hT p hpP) (hcard p hpP).le (hf p hpP) (hg p hpP) δ hδ hsmall
  exact ⟨hbalanced.1, hbalanced.2, herrors.1, herrors.2⟩

end Ostmann

end OAI
