import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeParameterEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreePhysicalShear

namespace OAI

/-! The certified free H columns have the actual forced physical parameter equation. -/

open Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralFreeFirstPhysical_parameter_equation (ell : ℕ) (νp νm z : ℂ)
    (hq : -1 < (((ell : ℂ)-νp)/2+z).re) (r : ℝ) (hr : 0 < r)
    (hrt : max 0 (Real.log 4/2) < Real.log r) :
    let Y := fun lam => spectralFreeFirstColumn ell (((ell : ℂ)-νp)/2+lam)
    let V := fun lam => spectralPhysicalPair (νp-2*lam) (νm-2*lam) (Y lam)
    HasDerivAt (fun s => deriv (fun lam => V lam s) z)
      (spectralPhysicalCircularField (νp-2*z) (νm-2*z) ((ell*(ell+10) : ℕ) : ℂ) 1 0 r
        (deriv (fun lam => V lam r) z) +
        ((0,-Complex.I*(V z r).1.1),(0,Complex.I*(V z r).2.1))) r := by
  let Y := fun lam => spectralFreeFirstColumn ell (((ell : ℂ)-νp)/2+lam)
  let V := fun lam => spectralPhysicalPair (νp-2*lam) (νm-2*lam) (Y lam)
  let D := fun t => deriv (fun lam => Y lam t) z
  let W := spectralPhysicalPair (νp-2*z) (νm-2*z)
    (fun t => circularParameterShear t (Y z t) (D t))
  have hP := spectralFreeFirst_parameter_equation ell νp νm z hq
  have he (s : ℝ) (hs : max 0 (Real.log 4/2) ≤ Real.log s) :
      deriv (fun lam => V lam s) z = W s := by
    exact (spectralPhysicalPair_hasParameterDerivAt νp νm z Y D s
      (hP.1 (Real.log s) hs).differentiableAt.hasDerivAt).deriv
  have hparam : (ell : ℂ)-2*(((ell : ℂ)-νp)/2+z)=νp-2*z := by ring
  have hY := spectralFreeFirstColumn_hasDerivAt ell (((ell : ℂ)-νp)/2+z) (νm-2*z) hq (Real.log r)
  rw [hparam] at hY
  have hd := spectralPhysicalFreeShear_hasDerivAt νp νm z ((ell*(ell+10) : ℕ) : ℂ)
    (Y z) D r hr hY (hP.2 (Real.log r) hrt)
  have htime : (fun s => deriv (fun lam => V lam s) z) =ᶠ[𝓝 r] W := by
    filter_upwards [(Real.continuousAt_log hr.ne').eventually (lt_mem_nhds hrt)] with s hs
    exact he s hs.le
  have hh := hd.congr_of_eventuallyEq htime
  change HasDerivAt (fun s => deriv (fun lam => V lam s) z)
    (spectralPhysicalCircularField (νp-2*z) (νm-2*z) ((ell*(ell+10) : ℕ) : ℂ) 1 0 r
      (deriv (fun lam => V lam r) z) +
      ((0,-Complex.I*(V z r).1.1),(0,Complex.I*(V z r).2.1))) r
  rw [he r hrt.le]
  exact hh

theorem spectralFreeSecondPhysical_parameter_equation (ell : ℕ) (νp νm z : ℂ)
    (hq : -1 < (((ell : ℂ)-νm)/2+z).re) (r : ℝ) (hr : 0 < r)
    (hrt : max 0 (Real.log 4/2) < Real.log r) :
    let Y := fun lam => spectralFreeSecondColumn ell (((ell : ℂ)-νm)/2+lam)
    let V := fun lam => spectralPhysicalPair (νp-2*lam) (νm-2*lam) (Y lam)
    HasDerivAt (fun s => deriv (fun lam => V lam s) z)
      (spectralPhysicalCircularField (νp-2*z) (νm-2*z) ((ell*(ell+10) : ℕ) : ℂ) 1 0 r
        (deriv (fun lam => V lam r) z) +
        ((0,-Complex.I*(V z r).1.1),(0,Complex.I*(V z r).2.1))) r := by
  let Y := fun lam => spectralFreeSecondColumn ell (((ell : ℂ)-νm)/2+lam)
  let V := fun lam => spectralPhysicalPair (νp-2*lam) (νm-2*lam) (Y lam)
  let D := fun t => deriv (fun lam => Y lam t) z
  let W := spectralPhysicalPair (νp-2*z) (νm-2*z)
    (fun t => circularParameterShear t (Y z t) (D t))
  have hP := spectralFreeSecond_parameter_equation ell νp νm z hq
  have he (s : ℝ) (hs : max 0 (Real.log 4/2) ≤ Real.log s) :
      deriv (fun lam => V lam s) z = W s := by
    exact (spectralPhysicalPair_hasParameterDerivAt νp νm z Y D s
      (hP.1 (Real.log s) hs).differentiableAt.hasDerivAt).deriv
  have hparam : (ell : ℂ)-2*(((ell : ℂ)-νm)/2+z)=νm-2*z := by ring
  have hY := spectralFreeSecondColumn_hasDerivAt ell (((ell : ℂ)-νm)/2+z) (νp-2*z) hq (Real.log r)
  rw [hparam] at hY
  have hd := spectralPhysicalFreeShear_hasDerivAt νp νm z ((ell*(ell+10) : ℕ) : ℂ)
    (Y z) D r hr hY (hP.2 (Real.log r) hrt)
  have htime : (fun s => deriv (fun lam => V lam s) z) =ᶠ[𝓝 r] W := by
    filter_upwards [(Real.continuousAt_log hr.ne').eventually (lt_mem_nhds hrt)] with s hs
    exact he s hs.le
  have hh := hd.congr_of_eventuallyEq htime
  change HasDerivAt (fun s => deriv (fun lam => V lam s) z)
    (spectralPhysicalCircularField (νp-2*z) (νm-2*z) ((ell*(ell+10) : ℕ) : ℂ) 1 0 r
      (deriv (fun lam => V lam r) z) +
      ((0,-Complex.I*(V z r).1.1),(0,Complex.I*(V z r).2.1))) r
  rw [he r hrt.le]
  exact hh

end DefocusingNLS

end OAI
