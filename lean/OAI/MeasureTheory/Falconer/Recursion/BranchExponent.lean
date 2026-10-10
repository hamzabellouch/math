import OAI.MeasureTheory.Falconer.Recursion.BranchExponentAlgebra
import OAI.MeasureTheory.Falconer.Estimates.ActualRegularizedClasses

namespace OAI

namespace PlanarFalconer

theorem RegularizedProfileData.discrete_lipschitz {Q : DyadicSquare}
    {ρ : MeasureTheory.Measure Plane} {N B : ℕ} {δ lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N B δ lam m) :
    DiscreteProfileLipschitz (fun n => m n-(n:ℝ)/N) N := by
  intro i hi j hj
  exact h.adjusted j i (Nat.cast_nonneg _) (Nat.cast_le.mpr hj)
    (Nat.cast_nonneg _) (Nat.cast_le.mpr hi)

end PlanarFalconer

end OAI
