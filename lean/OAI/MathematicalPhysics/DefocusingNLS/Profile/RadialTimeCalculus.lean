import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTranslationEigenpair
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGaugeNonlinearity

namespace OAI

/-! Radial differentiation and the odd-power cancellation in the time mode. -/

open scoped ContDiff
namespace DefocusingNLS

noncomputable def radialAffineEuler (c : ℂ) (Q : ℝ → ℂ) (r : ℝ) : ℂ :=
  c*Q r+(r : ℂ)/2*deriv Q r

theorem radialAffineEuler_hasDerivAt (c : ℂ) (Q : ℝ → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (r : ℝ) :
    HasDerivAt (radialAffineEuler c Q)
      (radialAffineEuler (c+1/2) (deriv Q) r) r := by
  have h0 := (hQ.differentiable (by simp) r).hasDerivAt
  have hQ1 : ContDiff ℝ ∞ (deriv Q) := hQ.deriv'
  have h1 := (hQ1.differentiable (by simp) r).hasDerivAt
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)/2) (1/2 : ℂ) r := by
    simpa only [id_eq,Complex.ofReal_one] using
      ((hasDerivAt_id r).ofReal_comp).div_const (2 : ℂ)
  convert! (h0.const_mul c).add (ht.mul h1) using 1
  dsimp only [radialAffineEuler]
  ring

theorem radialAffineEuler_deriv (c : ℂ) (Q : ℝ → ℂ)
    (hQ : ContDiff ℝ ∞ Q) :
    deriv (radialAffineEuler c Q)=radialAffineEuler (c+1/2) (deriv Q) := by
  funext r
  exact (radialAffineEuler_hasDerivAt c Q hQ r).deriv

theorem radialAffineEuler_second (c : ℂ) (Q : ℝ → ℂ)
    (hQ : ContDiff ℝ ∞ Q) :
    deriv (deriv (radialAffineEuler c Q))=
      radialAffineEuler (c+1) (deriv (deriv Q)) := by
  rw [radialAffineEuler_deriv c Q hQ,radialAffineEuler_deriv _ _ hQ.deriv']
  congr 1
  ring

theorem oddPower_time_cancellation (a b : ℝ) (m : ℕ) (h : 2*(m : ℝ)*a=1)
    (q : ℂ) :
    oddPowerDerivative m q (((a : ℂ)-Complex.I*(b : ℂ))*q)=
      ((a : ℂ)-Complex.I*(b : ℂ))*oddPowerNonlinearity m q+
        oddPowerNonlinearity m q := by
  have hp := oddPowerDerivative_gauge_real m q a (-b)
  have hc : (a : ℂ)+Complex.I*((-b : ℝ) : ℂ)=(a : ℂ)-Complex.I*(b : ℂ) := by
    push_cast
    ring
  rw [hc] at hp
  have hs : 2*(m : ℝ)*‖q‖^(2*m)*a=‖q‖^(2*m) := by
    calc
      _ = (2*(m : ℝ)*a)*‖q‖^(2*m) := by ring
      _ = _ := by rw [h,one_mul]
  rw [hs,← oddPowerNonlinearity_eq] at hp
  have he : ((a : ℂ)-Complex.I*(b : ℂ))*q=q*((a : ℂ)-Complex.I*(b : ℂ)) := mul_comm _ _
  rw [he]
  linear_combination hp

end DefocusingNLS

end OAI
