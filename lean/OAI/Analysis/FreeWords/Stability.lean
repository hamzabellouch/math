import Mathlib

namespace OAI

noncomputable section

namespace UniversalStrongKK

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def algebraUnitBall (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {x | x ∈ M ∧ ‖x‖ ≤ 1}

noncomputable def directedGap (M N : VonNeumannAlgebra H) : ℝ :=
  sSup ((fun x : H →L[ℂ] H =>
    sInf ((fun y : H →L[ℂ] H => ‖x - y‖) '' algebraUnitBall N)) '' algebraUnitBall M)

noncomputable def kkDistance (M N : VonNeumannAlgebra H) : ℝ :=
  max (directedGap M N) (directedGap N M)

def Implements (u : H →L[ℂ] H) (M N : VonNeumannAlgebra H) : Prop :=
  (fun x : H →L[ℂ] H => u * x * star u) '' (M : Set (H →L[ℂ] H)) =
    (N : Set (H →L[ℂ] H))

def StrongKKStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (M N : VonNeumannAlgebra H),
    kkDistance M N < δ →
    ∃ u : H →L[ℂ] H, u ∈ unitary (H →L[ℂ] H) ∧
      Implements u M N ∧ ‖u - 1‖ < ε

end UniversalStrongKK
end

end OAI
