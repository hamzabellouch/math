import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowEvaluationBalls
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.SlowFluid

namespace OAI

/-! A terminating evaluator for every mixed derivative of the slow force.
Its only inputs beyond the finite rational program are fast names for the
viscosity and the evaluation point. -/

namespace ForcedComputation
open ShearFlows Filter Set
open scoped Topology ContDiff

theorem slowCoarseTimeBound {y : SpaceTime} {b : ℕ → RationalSpaceTime}
    (hb : IsFastName b y) : |y.1 - ((b 7).1 : ℝ)| ≤ (1 / 128 : ℝ) := by
  have h := (norm_fst_le (y - rationalPoint (b 7))).trans (hb 7)
  norm_num [Prod.fst_sub, rationalPoint, Real.norm_eq_abs, errorTolerance] at h
  exact h

theorem slowCoarsePositive {y : SpaceTime} {b : ℕ → RationalSpaceTime}
    (hb : IsFastName b y) (h : ¬(b 7).1 ≤ 0) : -(1 / 2 : ℝ) < y.1 := by
  have hp : (0 : ℝ) < (b 7).1 := by exact_mod_cast lt_of_not_ge h
  linarith [(abs_le.mp (slowCoarseTimeBound hb)).1]

def evaluateSlowForce {ν : ℝ} {y : SpaceTime} (loader body : Input)
    (hl : ValidInput loader) (hb : ValidInput body) (α : List (Fin 4))
    (a : ℕ → ℚ) (ha : IsFastRealName a ν)
    (b : ℕ → RationalSpaceTime) (hname : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  if h : (b 7).1 ≤ 0 then 0
  else evaluateVectorBalls
    (slowEvaluationBalls loader body hl hb a b (slowCoarsePositive hname h) hname α)
    ε (vectorBallReady_exists
      (slowEvaluationBalls_converges hl hb ha b (slowCoarsePositive hname h) hname α) hε)

theorem evaluateSlowForce_spec {ν : ℝ} {y : SpaceTime} {loader body : Input}
    (hl : ValidInput loader) (hb : ValidInput body) (α : List (Fin 4))
    (a : ℕ → ℚ) (ha : IsFastRealName a ν)
    (b : ℕ → RationalSpaceTime) (hname : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (force ν (slowFromRest (initializedProgram loader body))) α y -
      rationalVector (evaluateSlowForce loader body hl hb α a ha b hname ε hε)‖ ≤
        (ε : ℝ) := by
  unfold evaluateSlowForce
  split
  · rename_i h
    have htime : y.1 < (1 / 64 : ℝ) := by
      have hc : ((b 7).1 : ℝ) ≤ 0 := by exact_mod_cast h
      linarith [(abs_le.mp (slowCoarseTimeBound hname)).2]
    have hz : ∀ t, t < (1 / 32 : ℝ) → ∀ x, initializedProgram loader body (t, x) = 0 :=
      fun _ ht x => initializedProgram_zero_extend loader body ht x
    have he : force ν (slowFromRest (initializedProgram loader body)) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(continuous_fst.tendsto y).eventually (eventually_lt_nhds htime)] with z hz'
      exact slowFromRest_force_zero hz ν hz' z.2
    rw [(mixedDerivative_eventuallyEq he α).self_of_nhds, mixedDerivative_zero]
    have heq : rationalVector (0 : RationalVector) = 0 := by
      ext j
      change ((0 : ℚ) : ℝ) = 0
      norm_num
    rw [heq, sub_self, norm_zero]
    exact_mod_cast hε.le
  · rename_i h
    exact evaluateVectorBalls_spec _
      (slowEvaluationBalls_converges hl hb ha b (slowCoarsePositive hname h) hname α)
      (slowEvaluationBalls_contains hl hb ha b (slowCoarsePositive hname h) hname α) ε hε

end ForcedComputation

end OAI
