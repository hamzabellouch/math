import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

structure FiniteReversibleChain (S : Type*) [Fintype S] where
  π : S → ℝ
  P : S → S → ℝ
  π_nonneg : ∀ s, 0 ≤ π s
  sum_π : ∑ s, π s = 1
  P_nonneg : ∀ s t, 0 ≤ P s t
  sum_P : ∀ s, ∑ t, P s t = 1
  balance : ∀ s t, π s * P s t = π t * P t s

abbrev StatePath (S : Type*) (n : ℕ) := Fin (n + 1) → S

def pathWeight {S : Type*} [Fintype S]
    (C : FiniteReversibleChain S) (n : ℕ) (ω : StatePath S n) : ℝ :=
  C.π (ω 0) * ∏ i : Fin n, C.P (ω i.castSucc) (ω i.succ)

def stateCost {S X : Type*} [Fintype S] [NormedAddCommGroup X]
    (C : FiniteReversibleChain S) (f : S → X) (p : ℝ) (n : ℕ) : ℝ :=
  ∑ ω : StatePath S n,
    pathWeight C n ω * Real.rpow (‖f (ω (Fin.last n)) - f (ω 0)‖) p

def MarkovTypeWith (p K : ℝ) (X : Type*) [NormedAddCommGroup X] : Prop :=
  0 < p ∧ 0 < K ∧
    ∀ (m : ℕ) (C : FiniteReversibleChain (Fin m)) (f : Fin m → X) (n : ℕ),
      1 ≤ n → stateCost C f p n ≤ Real.rpow K p * (n : ℝ) * stateCost C f p 1

def HasMarkovType (p : ℝ) (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ K : ℝ, MarkovTypeWith p K X

def HasNontrivialMarkovType (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∃ p : ℝ, 1 < p ∧ HasMarkovType p X

section

universe u

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

structure EquivalentNorm where
  p : Seminorm ℝ X
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  lower_bound : ∀ x, lower * ‖x‖ ≤ p x
  upper_bound : ∀ x, p x ≤ upper * ‖x‖

variable {X}

def UniformConvex (p : Seminorm ℝ X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 2 → ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : X, p x ≤ 1 → p y ≤ 1 → ε ≤ p (x - y) →
      p ((1 / 2 : ℝ) • (x + y)) ≤ 1 - δ

def HasEquivalentUCNorm (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ N : EquivalentNorm X, UniformConvex N.p

end

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem hasNontrivialMarkovType_iff_hasEquivalentUCNorm [CompleteSpace X] :
    HasNontrivialMarkovType X ↔ HasEquivalentUCNorm X := by
  sorry

end MarkovSuperreflexivity

end

end OAI
