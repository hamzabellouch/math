import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularKernel
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! The regular Volterra primitive solves the radial equation, including its initial jet. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralRegularDensity (d : ℕ) (h r : ℝ) : ℂ :=
  (r : ℂ)^d*Complex.exp (Complex.I*(h*r^2/4 : ℝ))

theorem spectralRegularDensity_ne_zero (d : ℕ) (h r : ℝ) (hr : r ≠ 0) :
    spectralRegularDensity d h r ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr)) (Complex.exp_ne_zero _)

theorem spectralRegularDensity_hasDerivAt (d : ℕ) (h r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (spectralRegularDensity d h)
      (spectralRegularDensity d h r*((d : ℂ)/(r : ℂ)+Complex.I*(h*r/2 : ℝ))) r := by
  have hp : HasDerivAt (fun s : ℝ => (s : ℂ)^d) ((d : ℂ)*(r : ℂ)^d/(r : ℂ)) r := by
    cases d with
    | zero => simpa using hasDerivAt_const r (1 : ℂ)
    | succ d =>
      convert! ((hasDerivAt_id r).ofReal_comp.pow (d+1)) using 1
      simp only [Nat.add_sub_cancel,id_eq,Complex.ofReal_one,mul_one]
      rw [pow_succ]
      field_simp [Complex.ofReal_ne_zero.mpr hr]
  have hs : HasDerivAt (fun s : ℝ => h*s^2/4) (h*r/2) r := by
    convert! (((hasDerivAt_id r).pow 2).const_mul h).div_const 4 using 1
    simp only [id_eq]
    ring
  have he := (hs.ofReal_comp.const_mul Complex.I).cexp
  apply (hp.mul he).congr_deriv
  unfold spectralRegularDensity
  ring

theorem spectralRegularSlope_hasDerivAt (d : ℕ) (h : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => (s : ℂ)*spectralRegularAverage d h f s)
      (f r-((d : ℂ)/(r : ℂ)+Complex.I*(h*r/2 : ℝ))*
        ((r : ℂ)*spectralRegularAverage d h f r)) r := by
  let F : ℝ → ℂ := fun s => spectralRegularDensity d h s*f s
  let J : ℝ → ℂ := fun s => ∫ t in (0 : ℝ)..s, F t
  have hF : Continuous F := by unfold F spectralRegularDensity; fun_prop
  have hJ : HasDerivAt J (F r) r :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 r)
      hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have he (s : ℝ) (hs : s ≠ 0) :
      J s/spectralRegularDensity d h s=(s : ℂ)*spectralRegularAverage d h f s := by
    apply (div_eq_iff (spectralRegularDensity_ne_zero d h s hs)).mpr
    have hi := spectralRegularAverage_scaling d h s f
    change _=∫ t in (0 : ℝ)..s, F t at hi
    change _=J s at hi
    rw [← hi]
    unfold spectralRegularDensity
    rw [pow_succ]
    ring
  have hevent : (fun s => J s/spectralRegularDensity d h s) =ᶠ[nhds r]
      (fun s : ℝ => (s : ℂ)*spectralRegularAverage d h f s) := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact he s (ne_of_gt hs)
  have hd := (hJ.div (spectralRegularDensity_hasDerivAt d h r hr.ne')
    (spectralRegularDensity_ne_zero d h r hr.ne')).congr_of_eventuallyEq hevent.symm
  apply hd.congr_deriv
  change (spectralRegularDensity d h r*f r*spectralRegularDensity d h r-
      J r*(spectralRegularDensity d h r*
        ((d : ℂ)/(r : ℂ)+Complex.I*(h*r/2 : ℝ))))/(spectralRegularDensity d h r)^2=_
  rw [← he r hr.ne']
  field_simp [spectralRegularDensity_ne_zero d h r hr.ne']

theorem spectralRegularPrimitive_equation (d : ℕ) (h : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (r : ℝ) (hr : 0 < r) :
    deriv (deriv (spectralRegularPrimitive d h f)) r+
      ((d : ℂ)/(r : ℂ)+Complex.I*(h*r/2 : ℝ))*
        deriv (spectralRegularPrimitive d h f) r=f r := by
  have he : deriv (spectralRegularPrimitive d h f)=
      fun s : ℝ => (s : ℂ)*spectralRegularAverage d h f s := by
    funext s
    exact (spectralRegularPrimitive_hasDerivAt d h f hf s).deriv
  rw [he,(spectralRegularSlope_hasDerivAt d h f hf r hr).deriv]
  ring

theorem spectralRegularPrimitive_initial (d : ℕ) (h : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) :
    spectralRegularPrimitive d h f 0=0 ∧ deriv (spectralRegularPrimitive d h f) 0=0 := by
  constructor
  · simp [spectralRegularPrimitive]
  · rw [(spectralRegularPrimitive_hasDerivAt d h f hf 0).deriv]
    simp

end DefocusingNLS

end OAI
