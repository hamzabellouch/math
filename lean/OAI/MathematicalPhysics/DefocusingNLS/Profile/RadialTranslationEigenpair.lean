import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSymmetryConjugate
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedEvenProfile

namespace OAI

/-! Differentiating the actual stationary radial equation produces the
degree-one translation eigenpair with eigenvalue one half. -/

open Filter Topology Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_translation_eigenpair (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    IsHarmonicRadialEigenpair (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) (n+radialInnerShootingThreshold)
      (radialMatchedProfile n z) 11 (1/2)
      (deriv (radialMatchedEvenProfile n z))
      (fun r => star (deriv (radialMatchedEvenProfile n z) r)) := by
  have heta : ((11 : ℝ) : ℂ)=(11 : ℂ) := by norm_num
  have hlam : ((1/2 : ℝ) : ℂ)=(1/2 : ℂ) := by push_cast; rfl
  rw [← heta,← hlam]
  apply harmonicRadialEigenpair_of_real_first
    (eta := 11) (lam := 1/2)
  intro r hr
  let Q := radialMatchedEvenProfile n z
  let m := n+radialInnerShootingThreshold
  let a := radialShootingA n
  let b := radialShootingB (profileMatchingParameter z)
  have hQ : ContDiff ℝ ∞ Q := radialMatchedEvenProfile_contDiff n z hX hz
  have hQ1 : ContDiff ℝ ∞ (deriv Q) := hQ.deriv'
  have hQ2 : ContDiff ℝ ∞ (deriv (deriv Q)) := hQ1.deriv'
  have h0 := (hQ.differentiable (by simp) r).hasDerivAt
  have h1 := (hQ1.differentiable (by simp) r).hasDerivAt
  have h2 := (hQ2.differentiable (by simp) r).hasDerivAt
  have hc : HasDerivAt (fun t : ℝ => ((11/t : ℝ) : ℂ))
      (-11/(r : ℂ)^2) r := by
    convert! ((hasDerivAt_const r (11 : ℝ)).div (hasDerivAt_id r) hr.ne').ofReal_comp using 1
    dsimp only [id]
    push_cast
    ring
  have ht := ((hasDerivAt_id r).div_const (2 : ℝ)).ofReal_comp
  have hN : HasDerivAt (fun t => oddPowerNonlinearity m (Q t))
      ((((m+1 : ℕ) : ℂ)*Q r^m*star (Q r)^m)*deriv Q r+
        ((m : ℂ)*Q r^(m+1)*star (Q r)^(m-1))*star (deriv Q r)) r := by
    convert! (hasFDerivAt_oddPowerNonlinearity m (Q r)).comp_hasDerivAt r h0 using 1
  let S := fun t : ℝ => Complex.I*(deriv (deriv Q) t+(11/t : ℝ)*deriv Q t)-
    (t/2 : ℝ)*deriv Q t+(-(a : ℂ)+Complex.I*(b : ℂ))*Q t-
    Complex.I*oddPowerNonlinearity m (Q t)
  have hS : S =ᶠ[𝓝 r] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hr] with t htr
    have h := radialMatchedEvenProfile_stationary n z hX hz t htr
    dsimp only [S,a,b,m,Q]
    rw [oddPowerNonlinearity_eq]
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,mul_assoc] using h
  have hd := (((h2.add (hc.mul h1)).const_mul Complex.I).sub (ht.mul h1)).add
    (h0.const_mul (-(a : ℂ)+Complex.I*(b : ℂ)))
  have hD := hd.sub (hN.const_mul Complex.I)
  change HasDerivAt S _ r at hD
  have he := hD.unique ((hasDerivAt_const r (0 : ℂ)).congr_of_eventuallyEq hS)
  have hQr : Q r=radialMatchedProfile n z r := radialMatchedEvenProfile_nonneg n z r hr.le
  change ((1/2 : ℝ) : ℂ)*deriv Q r = _
  rw [← hQr]
  dsimp only [a,b,m,id] at he
  push_cast at he ⊢
  linear_combination -he

end DefocusingNLS

end OAI
