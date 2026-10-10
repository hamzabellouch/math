import OAI.Analysis.MarkovType.FiniteProbability
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic

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

theorem pathWeight_nonneg {S : Type*} [Fintype S]
    (C : FiniteReversibleChain S) (n : ℕ) (ω : StatePath S n) :
    0 ≤ pathWeight C n ω := by
  exact mul_nonneg (C.π_nonneg _) (Finset.prod_nonneg fun i _ => C.P_nonneg _ _)

theorem stateCost_nonneg {S X : Type*} [Fintype S] [NormedAddCommGroup X]
    (C : FiniteReversibleChain S) (f : S → X) (p : ℝ) (n : ℕ) :
    0 ≤ stateCost C f p n := by
  exact Finset.sum_nonneg fun ω _ =>
    mul_nonneg (pathWeight_nonneg C n ω) (Real.rpow_nonneg (norm_nonneg _) _)

end MarkovSuperreflexivity

end

end OAI
