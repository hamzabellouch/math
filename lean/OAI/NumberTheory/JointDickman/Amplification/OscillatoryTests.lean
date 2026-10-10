import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace OAI

/-! # The smooth oscillatory tests used in the coefficient estimate -/

namespace JointDickman

noncomputable def additivePhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

theorem norm_additivePhase (x : ℝ) : ‖additivePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_additivePhase (x : ℝ) :
    HasDerivAt additivePhase (additivePhase x * ((2 * Real.pi : ℝ) * Complex.I)) x := by
  have h := (((hasDerivAt_id x).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  simpa only [mul_one, id_eq] using! h

theorem continuous_additivePhase : Continuous additivePhase :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_additivePhase x).continuousAt)

noncomputable def oscillatoryTest (w : ℝ → ℝ) (ξ : ℝ) (t : ℝ) : ℂ :=
  (w t : ℂ) * additivePhase (ξ * t)

noncomputable def oscillatoryTestDeriv (w w' : ℝ → ℝ) (ξ : ℝ) (t : ℝ) : ℂ :=
  (w' t : ℂ) * additivePhase (ξ * t) +
    (w t : ℂ) * (additivePhase (ξ * t) * ((2 * Real.pi : ℝ) * Complex.I) * ξ)

theorem hasDerivAt_oscillatoryTest {w : ℝ → ℝ} {w' ξ t : ℝ}
    (hw : HasDerivAt w w' t) :
    HasDerivAt (oscillatoryTest w ξ) (oscillatoryTestDeriv w (fun _ => w') ξ t) t := by
  have hp := (hasDerivAt_additivePhase (ξ * t)).scomp t (hasDerivAt_const_mul ξ)
  simpa only [oscillatoryTest, oscillatoryTestDeriv, Function.comp_def, Complex.real_smul,
    mul_comm (ξ : ℂ)] using! hw.ofReal_comp.mul hp

theorem oscillatoryTest_norm (w : ℝ → ℝ) (ξ t : ℝ) :
    ‖oscillatoryTest w ξ t‖ = |w t| := by
  simp only [oscillatoryTest, norm_mul, norm_additivePhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

theorem oscillatoryTestDeriv_norm_le (w w' : ℝ → ℝ) (ξ t : ℝ) :
    ‖oscillatoryTestDeriv w w' ξ t‖ ≤ |w' t| + 2 * Real.pi * |ξ| * |w t| := by
  unfold oscillatoryTestDeriv
  calc
    _ ≤ ‖(w' t : ℂ) * additivePhase (ξ * t)‖ +
        ‖(w t : ℂ) * (additivePhase (ξ * t) * ((2 * Real.pi : ℝ) * Complex.I) * ξ)‖ :=
      norm_add_le _ _
    _ = _ := by
      simp only [norm_mul, norm_additivePhase, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_I, mul_one, one_mul, abs_of_pos Real.pi_pos, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem oscillatoryTestDeriv_continuousOn {w w' : ℝ → ℝ} {s : Set ℝ}
    (hw : ContinuousOn w s) (hw' : ContinuousOn w' s) (ξ : ℝ) :
    ContinuousOn (oscillatoryTestDeriv w w' ξ) s := by
  unfold oscillatoryTestDeriv
  have hp : ContinuousOn (fun t => additivePhase (ξ * t)) s :=
    (continuous_additivePhase.comp (continuous_const.mul continuous_id)).continuousOn
  exact ((Complex.continuous_ofReal.comp_continuousOn hw').mul hp).add
    ((Complex.continuous_ofReal.comp_continuousOn hw).mul ((hp.mul_const _).mul_const _))

end JointDickman

end OAI
