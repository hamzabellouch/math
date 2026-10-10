import OAI.MathematicalPhysics.DefocusingNLS.Certificates.FreeRadialProfile
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.OrderClosed

namespace OAI

/-! The limiting profile has a continuously matching first radial derivative. -/

open Set
namespace DefocusingNLS

noncomputable def freeRadialDerivative (b Z r : ℝ) : ℂ :=
  (-Complex.I*((r/2 : ℝ) : ℂ))*
    deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6)
      (-Complex.I*((r^2/4 : ℝ) : ℂ)) /
    regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))

theorem continuousOn_freeRadialDerivative (b Z : ℝ) :
    ContinuousOn (freeRadialDerivative b Z) (Ioi 0) := by
  intro r hr
  have hq : -1 < (-Complex.I*(b : ℂ)).re := by simp
  have hx : -Complex.I*((r^2/4 : ℝ) : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.2
    right
    simp only [neg_mul,Complex.neg_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add]
    have hr' : 0 < r := hr
    nlinarith [sq_pos_of_pos hr']
  have hc := (analyticOnNhd_regularizedSlowSolution_slit (-Complex.I*(b : ℂ)) 6 hq).deriv _ hx
  have ha : Continuous (fun t : ℝ => -Complex.I*((t^2/4 : ℝ) : ℂ)) := by fun_prop
  have ht : Continuous (fun t : ℝ => -Complex.I*((t/2 : ℝ) : ℂ)) := by fun_prop
  have hh : ContinuousAt (fun t : ℝ => deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6)
      (-Complex.I*((t^2/4 : ℝ) : ℂ))) r :=
    hc.continuousAt.comp (f := fun t : ℝ => -Complex.I*((t^2/4 : ℝ) : ℂ)) ha.continuousAt
  exact ((ht.continuousAt.mul hh).div_const _).continuousWithinAt

theorem contDiff_freeRadialProfile (b Z : ℝ) (hZ : 0 < Z)
    (hH : regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ)) ≠ 0)
    (hD : deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ))=0) :
    ContDiff ℝ 1 (freeRadialProfile b Z) := by
  apply contDiff_one_iff_deriv.2
  refine ⟨differentiable_freeRadialProfile b Z hZ hH hD,?_⟩
  have heq : deriv (freeRadialProfile b Z) =
      fun r => if r ≤ freeProfileRadius Z then 0 else freeRadialDerivative b Z r := by
    funext r
    by_cases hr : r ≤ freeProfileRadius Z
    · rw [ite_eq_left hr]
      rcases hr.eq_or_lt with rfl | hr
      · exact (hasDerivAt_freeRadialProfile_at_radius b Z hZ hH hD).deriv
      · exact (hasDerivAt_freeRadialProfile_inside b Z r hr).deriv
    · rw [ite_eq_right hr]
      exact (hasDerivAt_freeRadialProfile_outside b Z r hZ (not_le.mp hr)).deriv
  rw [heq]
  apply continuous_if_le continuous_id continuous_const continuousOn_const
  · apply (continuousOn_freeRadialDerivative b Z).mono
    intro r hr
    exact (freeProfileRadius_pos hZ).trans_le hr
  · intro r hr
    change r = freeProfileRadius Z at hr
    subst r
    simp only [freeRadialDerivative,freeProfileRadius_sq hZ.le,hD,mul_zero,zero_div]

end DefocusingNLS

end OAI
