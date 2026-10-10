import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Basic.Real.Basic
import OAI.Combinatorics.BalancedRyser.Incidence.Projective

namespace OAI

namespace Balanced

universe u

def SzonyiWeinerStability : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
    Nat.Prime (Fintype.card F) →
    ∀ (B : Finset (ProjectivePoint F)) (β : ℝ), 0 < β →
      (B.card : ℝ) ≤ (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1) - β →
      ((skewProjective B).card : ℝ) < (2 / 9 : ℝ) * (β + 1) ^ 2 →
      ∃ l : ProjectiveLine F,
        (Fintype.card F : ℝ) - 2 * ((skewProjective B).card : ℝ) /
          ((Fintype.card F : ℝ) + 1) ≤
        ((B.filter (fun P => ProjectiveIncident P l)).card : ℝ)

end Balanced

end OAI
