import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace OAI

/-! # Derivatives of the logarithmic monomials in the Riesz expansion -/
namespace JointDickman

noncomputable def logRieszMonomial (β x : ℝ) : ℝ := x^2*(Real.log x)^β

noncomputable def logRieszDerivative (β x : ℝ) : ℝ :=
  x*(2*(Real.log x)^β+β*(Real.log x)^(β-1))

noncomputable def logRieszSecondDerivative (β x : ℝ) : ℝ :=
  2*(Real.log x)^β+3*β*(Real.log x)^(β-1)+β*(β-1)*(Real.log x)^(β-2)

theorem hasDerivAt_log_rpow (β : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y : ℝ => (Real.log y)^β) ((1/x)*β*(Real.log x)^(β-1)) x := by
  simpa only [one_div] using
    (Real.hasDerivAt_log (by linarith : x ≠ 0)).rpow_const (p := β)
      (Or.inl (Real.log_pos hx).ne')

theorem hasDerivAt_logRieszMonomial (β : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (logRieszMonomial β) (logRieszDerivative β x) x := by
  have h := ((hasDerivAt_id x).pow 2).mul (hasDerivAt_log_rpow β hx)
  convert h using 1
  · rfl
  · dsimp [logRieszDerivative]
    field_simp

theorem hasDerivAt_logRieszDerivative (β : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (logRieszDerivative β) (logRieszSecondDerivative β x) x := by
  have h := (hasDerivAt_id x).mul
    (((hasDerivAt_log_rpow β hx).const_mul 2).add
      ((hasDerivAt_log_rpow (β-1) hx).const_mul β))
  convert h using 1
  · rfl
  · dsimp [logRieszSecondDerivative]
    rw [show β-1-1 = β-2 by ring]
    field_simp
    ring

end JointDickman

end OAI
