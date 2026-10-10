import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymmetryGenerator

namespace OAI

/-! # The diagonal generator data on a fixed contour range -/

open scoped NNReal

namespace DefocusingNLS

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def HasSymmetryRangeGenerator (S : ℝ≥0 → V →L[ℂ] V) (P : V →L[ℂ] V)
    (hcomm : ∀ t, Commute (S t) P) : Prop :=
  ∃ G : P.range →L[ℂ] P.range,
    (∀ t, projectionSemigroupRestriction S P hcomm t = NormedSpace.exp ((t : ℝ) • G)) ∧
    (∀ (lam : ℂ) (u : P.range), u ≠ 0 → G u = lam • u → lam = 0 ∨ lam = 1 ∨ lam = 1 / 2) ∧
    (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam) = ⊤

end DefocusingNLS

end OAI
