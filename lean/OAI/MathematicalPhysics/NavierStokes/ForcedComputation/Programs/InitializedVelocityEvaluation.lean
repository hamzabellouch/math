import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedEffective

namespace OAI

/-! The finite two-table evaluator also evaluates every derivative of the
initialized velocity itself. This supplies the coefficients of the slowed
force evaluator. -/

namespace ForcedComputation
open ShearFlows Set Filter
open scoped Topology ContDiff

def evaluateInitializedVelocity (loader body : Input)
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (α : List (Fin 4)) (b : ℕ → RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  if (b 6).1 ≤ 0 then 0
  else if (b 6).1 ≤ 1 then
    loader.velocityExpr.evaluate (velocityExpr_valid hloader) α b ε hε
  else body.velocityExpr.evaluate (velocityExpr_valid hbody) α b ε hε

theorem evaluateInitializedVelocity_spec {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (α : List (Fin 4))
    {b : ℕ → RationalSpaceTime} {y : SpaceTime} (hb : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (initializedProgram loader body) α y -
      rationalVector (evaluateInitializedVelocity loader body hloader hbody α b ε hε)‖ ≤
        (ε : ℝ) := by
  have htime : |y.1 - ((b 6).1 : ℝ)| ≤ (1 / 64 : ℝ) := by
    have h := (norm_fst_le (y - rationalPoint (b 6))).trans (hb 6)
    norm_num [Prod.fst_sub, rationalPoint, Real.norm_eq_abs, errorTolerance] at h
    exact h
  unfold evaluateInitializedVelocity
  split
  · rename_i hz
    have ht : y.1 < (1 / 32 : ℝ) := by
      have hz' : ((b 6).1 : ℝ) ≤ 0 := by exact_mod_cast hz
      linarith [(abs_le.mp htime).2]
    have he : initializedProgram loader body =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(continuous_fst.tendsto y).eventually (eventually_lt_nhds ht)] with z hz
      exact initializedProgram_zero_extend loader body hz z.2
    rw [(mixedDerivative_eventuallyEq he α).self_of_nhds, mixedDerivative_zero]
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hzv : ShearFlows.rationalVector (0 : RationalVector) = 0 := by
      ext j
      change ((0 : ℚ) : ℝ) = 0
      norm_num
    change ‖(0 : Space) - ShearFlows.rationalVector 0‖ ≤ (ε : ℝ)
    rw [hzv, sub_self, norm_zero]
    exact hεR.le
  · rename_i hz
    split
    · rename_i ho
      have hzero : (0 : ℝ) < (b 6).1 := by exact_mod_cast lt_of_not_ge hz
      have hone : ((b 6).1 : ℝ) ≤ 1 := by exact_mod_cast ho
      have hl : -(1 / 32 : ℝ) < y.1 := by linarith [(abs_le.mp htime).1]
      have hr : y.1 < 1 + (1 / 32 : ℝ) := by linarith [(abs_le.mp htime).2]
      have he : initializedProgram loader body =ᶠ[𝓝 y] loader.realizingVelocity := by
        filter_upwards [(continuous_fst.tendsto y).eventually (Ioo_mem_nhds hl hr)] with z hz
        exact initializedProgram_loading_extend loader body hz z.2
      rw [(mixedDerivative_eventuallyEq he α).self_of_nhds,
        ← velocityExpr_val hloader]
      exact VelocityExpr.evaluate_spec (velocityExpr_valid hloader) α b hb ε hε
    · rename_i ho
      have hone : (1 : ℝ) < (b 6).1 := by exact_mod_cast lt_of_not_ge ho
      have hl : 1 - (1 / 32 : ℝ) < y.1 := by linarith [(abs_le.mp htime).1]
      have he : initializedProgram loader body =ᶠ[𝓝 y] body.realizingVelocity := by
        filter_upwards [(continuous_fst.tendsto y).eventually (eventually_gt_nhds hl)] with z hz
        exact initializedProgram_tail_extend loader body hz z.2
      rw [(mixedDerivative_eventuallyEq he α).self_of_nhds,
        ← velocityExpr_val hbody]
      exact VelocityExpr.evaluate_spec (velocityExpr_valid hbody) α b hb ε hε

end ForcedComputation

end OAI
