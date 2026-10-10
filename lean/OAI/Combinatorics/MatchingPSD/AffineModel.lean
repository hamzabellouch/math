import Mathlib
import OAI.Combinatorics.MatchingPSD.Model

namespace OAI

namespace PerfectMatchingPSD

noncomputable def matchingPoint {n : ℕ} (M : PerfectMatching n) : Edge n → ℝ := by
  classical
  exact fun e => if e ∈ M.1 then 1 else 0

noncomputable def matchingPolytope (n : ℕ) : Set (Edge n → ℝ) :=
  convexHull ℝ (Set.range (matchingPoint (n := n)))

def HasAffineLift (n r : ℕ) : Prop :=
  ∃ (L : AffineSubspace ℝ (Matrix (Fin r) (Fin r) ℝ))
    (T : Matrix (Fin r) (Fin r) ℝ →ᵃ[ℝ] (Edge n → ℝ)),
    T '' {X | X ∈ L ∧ X.PosSemidef} = matchingPolytope n

end PerfectMatchingPSD

end OAI
