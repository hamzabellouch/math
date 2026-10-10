import OAI.Analysis.KadisonKastler.Basic

namespace OAI

/-!
# Universal strong Kadison–Kastler stability

The tolerance in Theorem 1.1 of *Universal strong Kadison–Kastler stability*
is chosen before the Hilbert space and the represented von Neumann algebras.
-/

namespace KadisonKastler

universe u

/-- Universal strong stability, at an arbitrary fixed universe level. -/
def UniversalStrongStability : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      ∀ M N : VonNeumannAlgebra H,
        kkDistance M N < δ → NearConjugacy M N ε

end KadisonKastler

end OAI
