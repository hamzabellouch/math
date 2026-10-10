import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

noncomputable section

namespace InternalCatalan

def catalan : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2

def MainClaim : Prop := Irrational catalan

theorem mainClaim_unfold :
    MainClaim =
      Irrational (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) := rfl

end InternalCatalan

end

end OAI
