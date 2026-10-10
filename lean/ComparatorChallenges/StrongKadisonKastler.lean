import Mathlib

namespace OAI

/-! Theorem 1.1 of *Universal strong Kadison–Kastler stability*:
one tolerance gives small unitary conjugacies on every complex Hilbert space. -/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitBall (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {x | x ∈ M ∧ ‖x‖ ≤ 1}

noncomputable def kkDistance (M N : VonNeumannAlgebra H) : ℝ :=
  Metric.hausdorffDist (unitBall M) (unitBall N)

def unitaryConj (v : unitary (H →L[ℂ] H)) (x : H →L[ℂ] H) : H →L[ℂ] H :=
  (v : H →L[ℂ] H) * x * star (v : H →L[ℂ] H)

def Conjugates (v : unitary (H →L[ℂ] H)) (M N : VonNeumannAlgebra H) : Prop :=
  unitaryConj v '' (M : Set (H →L[ℂ] H)) = (N : Set (H →L[ℂ] H))

def NearConjugacy (M N : VonNeumannAlgebra H) (ε : ℝ) : Prop :=
  ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧ ‖(v : H →L[ℂ] H) - 1‖ < ε

def UniversalStrongStability : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      ∀ M N : VonNeumannAlgebra H,
        kkDistance M N < δ → NearConjugacy M N ε

theorem universal_strong_stability : UniversalStrongStability.{u} := by
  sorry

end

end KadisonKastler

end OAI
