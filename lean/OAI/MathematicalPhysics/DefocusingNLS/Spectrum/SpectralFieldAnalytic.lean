import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFieldOperator
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace OAI

/-! Holomorphic dependence of the actual coupled coefficient operator on the spectral parameter. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

local instance : IsBoundedSMul ℂ (CircularTailSpace →L[ℂ] CircularTailSpace) := by
  convert! (NormedSpace.toIsBoundedSMul (𝕜 := ℂ)
    (E := CircularTailSpace →L[ℂ] CircularTailSpace))

theorem circularBoundedField_shift_eq (νp νm η lam : ℂ) (m : ℕ) (q : ℂ) (z : E₄) :
    circularBoundedField (νp-2*lam) (νm-2*lam) η m q z=
      circularBoundedField νp νm η m q z+
      (lam/2) • (circularBoundedField (νp-2) (νm-2) η m q z-
        circularBoundedField (νp+2) (νm+2) η m q z)+
      (lam^2/2) • (circularBoundedField (νp-2) (νm-2) η m q z+
        circularBoundedField (νp+2) (νm+2) η m q z-
        (2 : ℂ) • circularBoundedField νp νm η m q z) := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [circularBoundedField,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  all_goals ring

theorem circularFieldOperator_shift_eq (νp νm η lam : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ →ᵇ ℂ) :
    circularFieldOperator (νp-2*lam) (νm-2*lam) η m hm q=
      circularFieldOperator νp νm η m hm q+
      (lam/2) • (circularFieldOperator (νp-2) (νm-2) η m hm q-
        circularFieldOperator (νp+2) (νm+2) η m hm q)+
      (lam^2/2) • (circularFieldOperator (νp-2) (νm-2) η m hm q+
        circularFieldOperator (νp+2) (νm+2) η m hm q-
        (2 : ℂ) • circularFieldOperator νp νm η m hm q) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · apply BoundedContinuousFunction.ext
    intro t
    exact congrArg Prod.fst (circularBoundedField_shift_eq νp νm η lam m (q t)
      (circularTailEvaluation v t))
  · apply BoundedContinuousFunction.ext
    intro t
    exact congrArg Prod.snd (circularBoundedField_shift_eq νp νm η lam m (q t)
      (circularTailEvaluation v t))

theorem circularFieldOperator_analyticAt (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (q : ℝ →ᵇ ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun lam => circularFieldOperator (νp-2*lam) (νm-2*lam) η m hm q) z := by
  simp_rw [circularFieldOperator_shift_eq]
  have hi : AnalyticAt ℂ (fun lam : ℂ => lam) z := analyticAt_id
  exact (analyticAt_const.add (hi.div_const.smul analyticAt_const)).add
    ((hi.pow 2).div_const.smul analyticAt_const)

end DefocusingNLS

end OAI
