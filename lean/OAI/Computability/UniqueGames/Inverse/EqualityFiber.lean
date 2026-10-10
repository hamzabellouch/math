import Mathlib.Data.Fintype.BigOperators
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

/-!
Finite equality-fiber extraction for the Grassmann-to-matrix route.

These elementary results do not assume a shortcode inverse theorem.  They
separate the equality test, the retention of a nonempty output fiber, and the
subsequent removal of zero perturbation factors.  The dimension-uniform
Grassmann expansion theorem remains a separate mathematical obligation.
-/

namespace UniqueGamesTheorem.Inverse.EqualityFiber

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Information

variable {X Y : Type*} [Fintype X] [Fintype Y]

def fiberMass (p : X → ℝ) (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ∑ x, if f x = y then p x else 0

def fiberFlow (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ∑ x, p x * ∑ x', k x x' * if f x = y ∧ f x' = y then 1 else 0

def equalityAcceptance (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) : ℝ := by
  classical
  exact ∑ x, p x * ∑ x', k x x' * if f x = f x' then 1 else 0

theorem sum_fiberMass (p : X → ℝ) (f : X → Y) :
    ∑ y, fiberMass p f y = ∑ x, p x := by
  classical
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

omit [Fintype Y] in
theorem fiberMass_nonneg (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : X → Y) (y : Y) : 0 ≤ fiberMass p f y := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split
  · exact hp x
  · exact le_rfl

omit [Fintype Y] in
theorem fiberFlow_nonneg (p : X → ℝ) (k : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x x', 0 ≤ k x x')
    (f : X → Y) (y : Y) : 0 ≤ fiberFlow p k f y := by
  classical
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (hp x)
  apply Finset.sum_nonneg
  intro x' _
  apply mul_nonneg (hk x x')
  split <;> norm_num

omit [Fintype Y] in
theorem fiberFlow_le_mass (p : X → ℝ) (k : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x, IsProbability (k x))
    (f : X → Y) (y : Y) : fiberFlow p k f y ≤ fiberMass p f y := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases h : f x = y
  · simp only [h, true_and, ite_true]
    have hinner : (∑ x', k x x' * if f x' = y then 1 else 0) ≤ 1 := by
      calc
        _ ≤ ∑ x', k x x' := by
          apply Finset.sum_le_sum
          intro x' _
          split <;> simp [(hk x).1 x']
        _ = 1 := (hk x).2
    simpa using mul_le_mul_of_nonneg_left hinner (hp x)
  · simp [h]

private theorem sum_sameFiber_indicator (a b : Y) :
    (∑ y, if a = y ∧ b = y then (1 : ℝ) else 0) =
      if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro y _
    have h' : ¬ (a = y ∧ b = y) := fun hy => h (hy.1.trans hy.2.symm)
    simp [h']

theorem sum_fiberFlow (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) :
    ∑ y, fiberFlow p k f y = equalityAcceptance p k f := by
  classical
  unfold fiberFlow equalityAcceptance
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x' _
  rw [← Finset.mul_sum, sum_sameFiber_indicator]

/-- A probability-weighted average at least `η` contains a positive-weight
fiber whose unnormalized flow is at least `η` times its mass. -/
theorem exists_positive_mass_le_flow (mass flow : Y → ℝ)
    (hmass : IsProbability mass) (_hflow : ∀ y, 0 ≤ flow y)
    (hzero : ∀ y, mass y = 0 → flow y = 0)
    {η : ℝ} (haccept : η ≤ ∑ y, flow y) :
    ∃ y, 0 < mass y ∧ η * mass y ≤ flow y := by
  classical
  by_contra hnone
  have hless (y : Y) (hy : 0 < mass y) : flow y < η * mass y := by
    apply lt_of_not_ge
    intro h
    exact hnone ⟨y, hy, h⟩
  have hle (y : Y) : flow y ≤ η * mass y := by
    rcases eq_or_lt_of_le (hmass.1 y) with hz | hz
    · simp [← hz, hzero y hz.symm]
    · exact (hless y hz).le
  have hex : ∃ y, 0 < mass y := by
    by_contra hn
    have hall (y : Y) : mass y = 0 := le_antisymm (le_of_not_gt (fun hy => hn ⟨y, hy⟩))
      (hmass.1 y)
    have := hmass.2
    simp [hall] at this
  obtain ⟨y, hy⟩ := hex
  have hstrict : (∑ y, flow y) < ∑ y, η * mass y := by
    exact Finset.sum_lt_sum (fun y _ => hle y) ⟨y, Finset.mem_univ y, hless y hy⟩
  rw [← Finset.mul_sum, hmass.2, mul_one] at hstrict
  exact (not_lt_of_ge haccept) hstrict

/-- Equality acceptance supplies a nonempty output fiber with the claimed
retention.  The kernel is the actual sampling kernel; no conditioned sampling
law is silently substituted. -/
theorem exists_fiber_retention (p : X → ℝ) (k : X → X → ℝ)
    (hp : IsProbability p) (hk : ∀ x, IsProbability (k x))
    (f : X → Y) {η : ℝ} (haccept : η ≤ equalityAcceptance p k f) :
    ∃ y, 0 < fiberMass p f y ∧ η ≤ fiberFlow p k f y / fiberMass p f y := by
  have hmass : IsProbability (fiberMass p f) :=
    ⟨fiberMass_nonneg p hp.1 f, (sum_fiberMass p f).trans hp.2⟩
  have hflow := fiberFlow_nonneg p k hp.1 (fun x => (hk x).1) f
  have hzero (y : Y) (hy : fiberMass p f y = 0) : fiberFlow p k f y = 0 := by
    apply le_antisymm _ (hflow y)
    simpa [hy] using fiberFlow_le_mass p k hp.1 hk f y
  obtain ⟨y, hy, hret⟩ := exists_positive_mass_le_flow (fiberMass p f)
    (fiberFlow p k f) hmass hflow hzero (by simpa [sum_fiberFlow] using haccept)
  exact ⟨y, hy, (le_div_iff₀ hy).2 hret⟩

/-- Removing a self-loop mass `p₀ ≤ η/2` leaves retention at least `η/2`.
This is the precise algebra needed when one or both rank-one factors may be
zero in the unconditioned test. -/
theorem nonzero_retention_ge_half {η p₀ R : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hp₀ : 0 ≤ p₀) (hp₀η : p₀ ≤ η / 2)
    (haccept : η ≤ p₀ + (1 - p₀) * R) : η / 2 ≤ R := by
  have hp₀1 : p₀ < 1 := by linarith
  have hden : 0 < 1 - p₀ := by linarith
  have hprod : η / 2 * (1 - p₀) ≤ (1 - p₀) * R := by nlinarith
  nlinarith

theorem chart_retention_ge_quarter {η R : ℝ} (h : η / 2 ≤ R) : η / 4 ≤ R / 2 := by
  linarith

end
end UniqueGamesTheorem.Inverse.EqualityFiber

end

end OAI
