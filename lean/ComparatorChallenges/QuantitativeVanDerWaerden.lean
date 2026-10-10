import Mathlib

namespace OAI

universe u

namespace QuantitativeVanDerWaerden

def MonoAP {α : Type u} (c : ℕ → α) (k a d : ℕ) : Prop :=
  ∀ j < k, c (a + j * d) = c a

def HasMonoAP {α : Type u} (c : ℕ → α) (k N : ℕ) : Prop :=
  ∃ a d, 0 < d ∧ a + (k - 1) * d < N ∧ MonoAP c k a d

def IsRamsey (α : Type u) (k N : ℕ) : Prop :=
  ∀ c : ℕ → α, HasMonoAP c k N

/-- The least positive Ramsey interval size. Statements about its Ramsey
property require a finiteness proof; no such proof is built into this definition. -/
noncomputable def W (r k : ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ IsRamsey (Fin r) k N}

open Filter

/-- An absolute quantitative lower bound, uniform over all color counts. -/
theorem uniform_lower_bound :
    ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ) := by
  sorry

end QuantitativeVanDerWaerden

end OAI
