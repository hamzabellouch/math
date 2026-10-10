import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.NumberTheory.Real.Irrational

namespace OAI

namespace InvariantProjection.CircleErgodicity

open MeasureTheory

theorem irrational_rotation_ergodic {θ : ℝ} (hθ : Irrational θ) :
    Ergodic (fun x : UnitAddCircle => x + (θ : UnitAddCircle)) volume := by
  apply AddCircle.ergodic_add_right.mpr
  apply AddCircle.denseRange_zsmul_iff.mp
  exact AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hθ)

theorem irrational_rotation_integer_ergodic {θ : ℝ} (hθ : Irrational θ)
    {q : ℤ} (hq : q ≠ 0) :
    Ergodic (fun x : UnitAddCircle =>
      x + (((q : ℝ) * θ : ℝ) : UnitAddCircle)) volume :=
  irrational_rotation_ergodic (hθ.intCast_mul hq)

theorem irrational_rotation_totalErgodic {θ : ℝ} (hθ : Irrational θ)
    {n : ℕ} (hn : 0 < n) :
    Ergodic (fun x : UnitAddCircle => x + (θ : UnitAddCircle))^[n] volume := by
  rw [add_right_iterate]
  have hcoe : (((n : ℝ) * θ : ℝ) : UnitAddCircle) = n • (θ : UnitAddCircle) := by
    simpa only [nsmul_eq_mul] using
      (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := n) (x := θ))
  simpa only [hcoe] using irrational_rotation_ergodic (hθ.natCast_mul (Nat.ne_of_gt hn))

end InvariantProjection.CircleErgodicity

end OAI
