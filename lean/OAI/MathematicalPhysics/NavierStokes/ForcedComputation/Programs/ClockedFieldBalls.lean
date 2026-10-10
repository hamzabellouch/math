import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LogarithmName

namespace OAI

/-! Certified rational balls for a periodic field evaluated at a smooth
clock. The outer evaluation is refined to an explicit dyadic tolerance;
the clock error uses the field's global derivative bound. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Filter
open scoped Topology

theorem QBall.converges_of_contains {b : ℕ → QBall} {x : ℝ}
    (hb : ∀ n, (b n).Contains x)
    (hr : Tendsto (fun n => ((b n).radius : ℝ)) atTop (𝓝 0)) : QBall.Converges b x := by
  refine ⟨?_, hr⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n => dist_nonneg)
    (fun n => ?_) hr
  simpa only [QBall.Contains, Real.dist_eq, abs_sub_comm] using hb n

namespace ClockedExpr

def fieldVector (e : FieldExpr) : VelocityExpr := fun _ => e

theorem fieldVector_valid {e : FieldExpr} (he : e.Valid) : (fieldVector e).Valid :=
  fun _ => he

def dyadic (n : ℕ) : ℚ := (2 : ℚ) ^ (-(n : ℤ))

theorem dyadic_pos (n : ℕ) : 0 < dyadic n := by unfold dyadic; positivity

theorem dyadic_cast (n : ℕ) : (dyadic n : ℝ) = errorTolerance n := by
  simp [dyadic, errorTolerance]

theorem dyadic_tendsto : Tendsto (fun n => (dyadic n : ℝ)) atTop (𝓝 0) := by
  simpa only [dyadic_cast] using errorTolerance_tendsto

def fieldBall (q : ProfileExpr) (e : FieldExpr) (he : e.Valid)
    (y : RationalSpaceTime) (n : ℕ) : QBall :=
  let b := q.enclose y.1 n
  let c := fieldVector e
  let v := c.evaluateRational (fieldVector_valid he) [] (b.center, y.2) (dyadic n) (dyadic_pos n)
  ⟨v 0, dyadic n + (c.modulusBound [] : ℚ) * b.radius⟩

theorem fieldBall_contains (q : ProfileExpr) {e : FieldExpr} (he : e.Valid)
    (y : RationalSpaceTime) (n : ℕ) :
    (fieldBall q e he y n).Contains (e.val (clockedPoint q (rationalPoint y))) := by
  let b := q.enclose y.1 n
  let c := fieldVector e
  let z : RationalSpaceTime := (b.center, y.2)
  let v := c.evaluateRational (fieldVector_valid he) [] z (dyadic n) (dyadic_pos n)
  have houter := c.evaluateRational_spec (fieldVector_valid he) [] z (dyadic n) (dyadic_pos n)
  have heval : |e.val (rationalPoint z) - (v 0 : ℝ)| ≤ (dyadic n : ℝ) := by
    exact (norm_le_pi_norm
      (mixedDerivative c.val [] (rationalPoint z) - rationalVector v) 0).trans houter
  have hclock := q.enclose_contains y.1 n
  have hdist : ‖clockedPoint q (rationalPoint y) - rationalPoint z‖ ≤ (b.radius : ℝ) := by
    apply norm_prod_le_iff.mpr
    constructor
    · exact hclock
    · change ‖(fun j => (y.2 j : ℝ)) - (fun j => (y.2 j : ℝ))‖ ≤ (b.radius : ℝ)
      rw [sub_self, norm_zero]
      exact_mod_cast QBall.radius_nonneg hclock
  have hspace := c.lipschitz_bound (fieldVector_valid he) []
    (clockedPoint q (rationalPoint y)) (rationalPoint z)
  have hval : |e.val (clockedPoint q (rationalPoint y)) - e.val (rationalPoint z)| ≤
      (c.modulusBound [] : ℝ) * (b.radius : ℝ) := by
    exact (norm_le_pi_norm
      (mixedDerivative c.val [] (clockedPoint q (rationalPoint y)) -
        mixedDerivative c.val [] (rationalPoint z)) 0).trans
      (hspace.trans (mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg _)))
  change |e.val (clockedPoint q (rationalPoint y)) - (v 0 : ℝ)| ≤ _
  calc
    _ ≤ |e.val (clockedPoint q (rationalPoint y)) - e.val (rationalPoint z)| +
        |e.val (rationalPoint z) - (v 0 : ℝ)| := abs_sub_le _ _ _
    _ ≤ (c.modulusBound [] : ℝ) * (b.radius : ℝ) + (dyadic n : ℝ) := add_le_add hval heval
    _ = _ := by
      change _ = ((dyadic n + (c.modulusBound [] : ℚ) * b.radius : ℚ) : ℝ)
      push_cast
      ring

theorem fieldBall_converges (q : ProfileExpr) {e : FieldExpr} (he : e.Valid)
    (y : RationalSpaceTime) :
    QBall.Converges (fieldBall q e he y) (e.val (clockedPoint q (rationalPoint y))) := by
  apply QBall.converges_of_contains (fieldBall_contains q he y)
  have hr := (q.enclose_converges y.1).2
  have h := dyadic_tendsto.add (hr.const_mul ((fieldVector e).modulusBound [] : ℝ))
  simpa only [fieldBall, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, mul_zero, add_zero] using h

end ClockedExpr
end ForcedComputation

end

end OAI
