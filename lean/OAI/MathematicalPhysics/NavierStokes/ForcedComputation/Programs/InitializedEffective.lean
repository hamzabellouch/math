import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InitializedFluid
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ForceEvaluation

namespace OAI

/-! A terminating evaluator for the initialized force and every mixed derivative.
A single coarse time approximation chooses a valid local formula. The overlap
is supplied by the fixed zero collars, including at times zero and one. -/

namespace ForcedComputation

open ShearFlows Set Filter
open scoped Topology ContDiff

theorem force_germ_of_germ {U V : Velocity} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) {y : SpaceTime} (he : U =ᶠ[𝓝 y] V) (ν : ℝ) :
    force ν U =ᶠ[𝓝 y] force ν V := by
  filter_upwards [he.eventuallyEq_nhds] with z hz
  exact force_eq_of_eventuallyEq hU hV hz ν

theorem mixedForce_eq_of_germ {U V : Velocity} (hU : ContDiff ℝ ∞ U)
    (hV : ContDiff ℝ ∞ V) {y : SpaceTime} (he : U =ᶠ[𝓝 y] V)
    (ν : ℝ) (α : List (Fin 4)) :
    mixedDerivative (force ν U) α y = mixedDerivative (force ν V) α y :=
  (mixedDerivative_eventuallyEq (force_germ_of_germ hU hV he ν) α).self_of_nhds

/-- The two finite shear expressions are evaluated by their existing certified
algorithms; the extra time test only selects between overlapping exact germs. -/
def evaluateInitializedForce (loader body : Input)
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (α : List (Fin 4)) (a : ℕ → ℚ) (b : ℕ → RationalSpaceTime)
    (ε : ℚ) (hε : 0 < ε) : RationalVector :=
  if (b 6).1 ≤ 0 then 0
  else if (b 6).1 ≤ 1 then
    loader.velocityExpr.evaluateForce (velocityExpr_valid hloader) α a b ε hε
  else body.velocityExpr.evaluateForce (velocityExpr_valid hbody) α a b ε hε

theorem evaluateInitializedForce_spec {loader body : Input}
    (hloader : ValidInput loader) (hbody : ValidInput body)
    (α : List (Fin 4)) {ν : ℝ} {a : ℕ → ℚ} (ha : IsFastRealName a ν)
    {b : ℕ → RationalSpaceTime} {y : SpaceTime} (hb : IsFastName b y)
    (ε : ℚ) (hε : 0 < ε) :
    ‖mixedDerivative (force ν (initializedProgram loader body)) α y -
      rationalVector (evaluateInitializedForce loader body hloader hbody α a b ε hε)‖ ≤
        (ε : ℝ) := by
  have htime : |y.1 - ((b 6).1 : ℝ)| ≤ (1 / 64 : ℝ) := by
    have h := (norm_fst_le (y - rationalPoint (b 6))).trans (hb 6)
    norm_num [Prod.fst_sub, rationalPoint, Real.norm_eq_abs, errorTolerance] at h
    exact h
  have hU := initializedProgram_smooth hloader hbody
  unfold evaluateInitializedForce
  split
  · rename_i hz
    have ht : y.1 < (1 / 32 : ℝ) := by
      have hz' : ((b 6).1 : ℝ) ≤ 0 := by exact_mod_cast hz
      linarith [(abs_le.mp htime).2]
    have he : initializedProgram loader body =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [(continuous_fst.tendsto y).eventually (eventually_lt_nhds ht)] with z hz
      exact initializedProgram_zero_extend loader body hz z.2
    rw [mixedForce_eq_of_germ hU contDiff_const he ν α]
    have hzero : force ν (fun _ : SpaceTime => (0 : Space)) = fun _ => 0 := by
      funext z
      exact force_zero ν z
    rw [hzero, mixedDerivative_zero]
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
      rw [mixedForce_eq_of_germ hU (realizingVelocity_smooth hloader) he ν α,
        ← velocityExpr_val hloader]
      exact VelocityExpr.evaluateForce_spec (velocityExpr_valid hloader) α ha hb ε hε
    · rename_i ho
      have hone : (1 : ℝ) < (b 6).1 := by exact_mod_cast lt_of_not_ge ho
      have hl : 1 - (1 / 32 : ℝ) < y.1 := by linarith [(abs_le.mp htime).1]
      have he : initializedProgram loader body =ᶠ[𝓝 y] body.realizingVelocity := by
        filter_upwards [(continuous_fst.tendsto y).eventually (eventually_gt_nhds hl)] with z hz
        exact initializedProgram_tail_extend loader body hz z.2
      rw [mixedForce_eq_of_germ hU (realizingVelocity_smooth hbody) he ν α,
        ← velocityExpr_val hbody]
      exact VelocityExpr.evaluateForce_spec (velocityExpr_valid hbody) α ha hb ε hε

end ForcedComputation

end OAI
