import OAI.Combinatorics.GraphThreshold.Model

namespace OAI

noncomputable section

namespace LeanBlast.SecondKahnKalai

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw

def expectation {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, μ.weight ω * f ω

def prob {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then μ.weight ω else 0

def IsPositive {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) : Prop :=
  ∀ ω, 0 < μ.weight ω

end FiniteLaw

def IsSpread {X B : Type*} [DecidableEq X] [Fintype B]
    (μ : FiniteLaw B) (A : B → Finset X) (a : ℝ) : Prop :=
  ∀ J : Finset X, J.Nonempty → μ.prob (fun b => J ⊆ A b) ≤ a ^ J.card

end LeanBlast.SecondKahnKalai

end

end OAI
