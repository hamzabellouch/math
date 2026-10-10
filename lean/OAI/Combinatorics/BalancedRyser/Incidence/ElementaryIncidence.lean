import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import OAI.Combinatorics.BalancedRyser.Incidence.Affine

namespace OAI

namespace Balanced
noncomputable section

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def affineIntersectionCount (U : Finset (Point F)) (l : Line F) : ℕ :=
  (U.filter (fun p => OnLine p l)).card

def affineDirectionalVariance (U : Finset (Point F)) (d : Direction F) : ℝ :=
  (1 / (Fintype.card F : ℝ)) *
    ∑ b : F, ((affineIntersectionCount U (d, b) : ℝ) -
      (U.card : ℝ) / (Fintype.card F : ℝ)) ^ 2

def AffineSecondMoment (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  ∀ U : Finset (Point F),
    let q : ℝ := Fintype.card F
    let N : ℝ := U.card
    (∑ l : Line F, (affineIntersectionCount U l : ℝ)) = (q + 1) * N ∧
    (∑ l : Line F, (affineIntersectionCount U l : ℝ) ^ 2) = N ^ 2 + q * N ∧
    (∑ l : Line F, ((affineIntersectionCount U l : ℝ) - N / q) ^ 2) =
      q * N - N ^ 2 / q ∧
    (∑ l : Line F, ((affineIntersectionCount U l : ℝ) - N / q) ^ 2) ≤ q ^ 3 / 4 ∧
    (∑ d : Direction F, affineDirectionalVariance U d) = N - N ^ 2 / q ^ 2 ∧
    (∑ d : Direction F, affineDirectionalVariance U d) ≤ N ∧
    N ≤ q ^ 2

end
end Balanced

end OAI
