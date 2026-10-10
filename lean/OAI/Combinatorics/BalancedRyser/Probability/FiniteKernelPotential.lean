import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

namespace Balanced.FiniteKernelPotential

noncomputable section

variable {X : Type*} [Fintype X]

def advance (K : X → X → ℝ) (w : X → ℝ) (y : X) : ℝ :=
  ∑ x, w x * K x y

def weights (K : ℕ → X → X → ℝ) (w₀ : X → ℝ) : ℕ → X → ℝ
  | 0 => w₀
  | t + 1 => advance (K t) (weights K w₀ t)

@[simp] theorem weights_zero (K : ℕ → X → X → ℝ) (w₀ : X → ℝ) :
    weights K w₀ 0 = w₀ := rfl

@[simp] theorem weights_succ (K : ℕ → X → X → ℝ) (w₀ : X → ℝ) (t : ℕ) :
    weights K w₀ (t + 1) = advance (K t) (weights K w₀ t) := rfl

 theorem advance_nonneg (K : X → X → ℝ) (w : X → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (hw : ∀ x, 0 ≤ w x) (y : X) :
    0 ≤ advance K w y := by
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (hw x) (hK x y)

 theorem weights_nonneg (K : ℕ → X → X → ℝ) (w₀ : X → ℝ)
    (hK : ∀ t x y, 0 ≤ K t x y) (hw₀ : ∀ x, 0 ≤ w₀ x)
    (t : ℕ) (x : X) : 0 ≤ weights K w₀ t x := by
  induction t generalizing x with
  | zero => exact hw₀ x
  | succ t ih =>
    exact advance_nonneg (K t) (weights K w₀ t) (hK t)
      ih x

theorem advance_pairing (K : X → X → ℝ) (w Φ : X → ℝ) :
    ∑ y, advance K w y * Φ y = ∑ x, w x * ∑ y, K x y * Φ y := by
  simp only [advance, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem advance_potential_le (K : X → X → ℝ) (w Φ Ψ : X → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hstep : ∀ x, ∑ y, K x y * Ψ y ≤ Φ x) :
    ∑ y, advance K w y * Ψ y ≤ ∑ x, w x * Φ x := by
  rw [advance_pairing]
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_left (hstep x) (hw x)

theorem expected_potential_le (K : ℕ → X → X → ℝ) (w₀ : X → ℝ)
    (Φ : ℕ → X → ℝ)
    (hK : ∀ t x y, 0 ≤ K t x y) (hw₀ : ∀ x, 0 ≤ w₀ x)
    (hstep : ∀ t x, ∑ y, K t x y * Φ (t + 1) y ≤ Φ t x)
    (T : ℕ) :
    ∑ y, weights K w₀ T y * Φ T y ≤ ∑ x, w₀ x * Φ 0 x := by
  induction T with
  | zero => exact le_rfl
  | succ T ih =>
    exact (advance_potential_le (K T) (weights K w₀ T) (Φ T) (Φ (T + 1))
      (weights_nonneg K w₀ hK hw₀ T) (hstep T)).trans ih

theorem payoff_le (K : ℕ → X → X → ℝ) (w₀ : X → ℝ)
    (Φ : ℕ → X → ℝ) (payoff : X → ℝ)
    (hK : ∀ t x y, 0 ≤ K t x y) (hw₀ : ∀ x, 0 ≤ w₀ x)
    (hstep : ∀ t x, ∑ y, K t x y * Φ (t + 1) y ≤ Φ t x)
    (T : ℕ) (hpayoff : ∀ x, payoff x ≤ Φ T x) :
    ∑ y, weights K w₀ T y * payoff y ≤ ∑ x, w₀ x * Φ 0 x := by
  calc
    _ ≤ ∑ y, weights K w₀ T y * Φ T y := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hpayoff y) (weights_nonneg K w₀ hK hw₀ T y)
    _ ≤ _ := expected_potential_le K w₀ Φ hK hw₀ hstep T

def pointMass [DecidableEq X] (x₀ : X) (x : X) : ℝ := if x = x₀ then 1 else 0

omit [Fintype X] in
theorem pointMass_nonneg [DecidableEq X] (x₀ x : X) :
    0 ≤ pointMass x₀ x := by unfold pointMass; split_ifs <;> norm_num

@[simp] theorem pointMass_pairing [DecidableEq X] (x₀ : X) (f : X → ℝ) :
    ∑ x, pointMass x₀ x * f x = f x₀ := by simp [pointMass]

theorem pointMass_potential_le [DecidableEq X]
    (K : ℕ → X → X → ℝ) (x₀ : X) (Φ : X → ℝ)
    (hK : ∀ t x y, 0 ≤ K t x y)
    (hstep : ∀ t x, ∑ y, K t x y * Φ y ≤ Φ x) (T : ℕ) :
    ∑ y, weights K (pointMass x₀) T y * Φ y ≤ Φ x₀ := by
  simpa using expected_potential_le K (pointMass x₀) (fun _ => Φ) hK
    (pointMass_nonneg x₀) hstep T

theorem pointMass_payoff_le [DecidableEq X]
    (K : ℕ → X → X → ℝ) (x₀ : X) (Φ payoff : X → ℝ)
    (hK : ∀ t x y, 0 ≤ K t x y)
    (hstep : ∀ t x, ∑ y, K t x y * Φ y ≤ Φ x)
    (T : ℕ) (hpayoff : ∀ x, payoff x ≤ Φ x) :
    ∑ y, weights K (pointMass x₀) T y * payoff y ≤ Φ x₀ := by
  simpa using payoff_le K (pointMass x₀) (fun _ => Φ) payoff hK
    (pointMass_nonneg x₀) hstep T hpayoff

theorem weights_eq_of_recurrence (K : ℕ → X → X → ℝ) (w : ℕ → X → ℝ)
    (hrec : ∀ t y, w (t + 1) y = ∑ x, w t x * K t x y) (T : ℕ) :
    weights K (w 0) T = w T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    funext y
    simp only [weights_succ, advance, ih]
    exact (hrec T y).symm

theorem evolution_payoff_le (K : ℕ → X → X → ℝ) (w : ℕ → X → ℝ)
    (Φ : ℕ → X → ℝ) (payoff : X → ℝ)
    (hrec : ∀ t y, w (t + 1) y = ∑ x, w t x * K t x y)
    (hK : ∀ t x y, 0 ≤ K t x y) (hw₀ : ∀ x, 0 ≤ w 0 x)
    (hstep : ∀ t x, ∑ y, K t x y * Φ (t + 1) y ≤ Φ t x)
    (T : ℕ) (hpayoff : ∀ x, payoff x ≤ Φ T x) :
    ∑ y, w T y * payoff y ≤ ∑ x, w 0 x * Φ 0 x := by
  rw [← weights_eq_of_recurrence K w hrec T]
  exact payoff_le K (w 0) Φ payoff hK hw₀ hstep T hpayoff

theorem pointMass_event_le [DecidableEq X]
    (K : ℕ → X → X → ℝ) (x₀ : X) (Φ : X → ℝ)
    (hK : ∀ t x y, 0 ≤ K t x y)
    (hstep : ∀ t x, ∑ y, K t x y * Φ y ≤ Φ x)
    (T : ℕ) (E : X → Prop) [DecidablePred E]
    (hE : ∀ x, (if E x then (1 : ℝ) else 0) ≤ Φ x) :
    (∑ y, if E y then weights K (pointMass x₀) T y else 0) ≤ Φ x₀ := by
  simpa only [mul_ite, mul_one, mul_zero] using
    pointMass_payoff_le K x₀ Φ (fun x => if E x then 1 else 0) hK hstep T hE

end
end Balanced.FiniteKernelPotential

end OAI
