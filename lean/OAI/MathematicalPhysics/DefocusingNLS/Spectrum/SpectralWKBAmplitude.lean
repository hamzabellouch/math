import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBFrame
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Construct the WKB amplitude by an actual scalar integral. Its normalization
is propagated by differentiation; no choice of a logarithm branch is needed. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralWKBAmplitude (R : ℝ) (a₀ : ℂ) (p v : ℝ → ℂ) (r : ℝ) : ℂ :=
  a₀*Complex.exp (∫ t in R..r, -(v t/(2*p t)))

theorem spectralShellPrimitive_hasDerivAt (R E : ℝ) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc R E)) (r : ℝ) (hr : r ∈ Ioo R E) :
    HasDerivAt (fun s => ∫ t in R..s, f t) (f r) r := by
  have hi : IntervalIntegrable f volume R r := ContinuousOn.intervalIntegrable_of_Icc hr.1.le
    (hf.mono (Icc_subset_Icc le_rfl hr.2.le))
  have hc : ContinuousAt f r := hf.continuousAt (Icc_mem_nhds hr.1 hr.2)
  have hm : StronglyMeasurableAtFilter f (nhds r) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hf.mono Ioo_subset_Icc_self) r hr
  exact intervalIntegral.integral_hasDerivAt_right hi hm hc

theorem spectralWKBAmplitude_initial (R : ℝ) (a₀ : ℂ) (p v : ℝ → ℂ) :
    spectralWKBAmplitude R a₀ p v R=a₀ := by
  simp only [spectralWKBAmplitude,intervalIntegral.integral_same,Complex.exp_zero,mul_one]

theorem spectralWKBAmplitude_continuousOn (R E : ℝ) (hRE : R≤ E)
    (a₀ : ℂ) (p v : ℝ → ℂ) (hp : ContinuousOn p (Icc R E))
    (hv : ContinuousOn v (Icc R E)) (hp0 : ∀ r ∈ Icc R E, p r≠0) :
    ContinuousOn (spectralWKBAmplitude R a₀ p v) (Icc R E) := by
  have hq : ContinuousOn (fun t => -(v t/(2*p t))) (Icc R E) :=
    (hv.div (continuousOn_const.mul hp) (fun t ht => mul_ne_zero (by norm_num) (hp0 t ht))).neg
  have hi : IntervalIntegrable (fun t => -(v t/(2*p t))) volume R E :=
    ContinuousOn.intervalIntegrable_of_Icc hRE hq
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (show R ∈ uIcc R E from left_mem_uIcc)
  rw [uIcc_of_le hRE] at hc
  exact continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn hc)

theorem spectralWKBAmplitude_hasDerivAt (R E : ℝ)
    (a₀ : ℂ) (p v : ℝ → ℂ) (hp : ContinuousOn p (Icc R E))
    (hv : ContinuousOn v (Icc R E)) (hp0 : ∀ r ∈ Icc R E, p r≠0)
    (r : ℝ) (hr : r ∈ Ioo R E) :
    HasDerivAt (spectralWKBAmplitude R a₀ p v)
      (-(v r/(2*p r))*spectralWKBAmplitude R a₀ p v r) r := by
  have hq : ContinuousOn (fun t => -(v t/(2*p t))) (Icc R E) :=
    (hv.div (continuousOn_const.mul hp) (fun t ht => mul_ne_zero (by norm_num) (hp0 t ht))).neg
  have hd := (spectralShellPrimitive_hasDerivAt R E _ hq r hr).cexp.const_mul a₀
  apply hd.congr_deriv
  dsimp only [spectralWKBAmplitude]
  ring

theorem spectralWKBAmplitude_normalization (R E : ℝ) (hRE : R≤ E)
    (a₀ : ℂ) (p v : ℝ → ℂ) (hp : ContinuousOn p (Icc R E))
    (hv : ContinuousOn v (Icc R E)) (hp0 : ∀ r ∈ Icc R E, p r≠0)
    (hpD : ∀ r ∈ Ioo R E, HasDerivAt p (v r) r) (ha₀ : p R*a₀^2=1)
    (r : ℝ) (hr : r ∈ Icc R E) :
    p r*(spectralWKBAmplitude R a₀ p v r)^2=1 := by
  have hac := spectralWKBAmplitude_continuousOn R E hRE a₀ p v hp hv hp0
  have hprod : ContinuousOn (fun t => p t*(spectralWKBAmplitude R a₀ p v t)^2) (Icc R E) := hp.mul (hac.pow 2)
  have hd (t : ℝ) (ht : t ∈ Ioo R E) :
      HasDerivAt (fun s => p s*(spectralWKBAmplitude R a₀ p v s)^2) 0 t := by
    apply ((hpD t ht).mul ((spectralWKBAmplitude_hasDerivAt R E a₀ p v hp hv hp0 t ht).pow 2)).congr_deriv
    simp only [Pi.pow_apply]
    field_simp [hp0 t ⟨ht.1.le,ht.2.le⟩]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1
    (hprod.mono (Icc_subset_Icc le_rfl hr.2))
    (fun t ht => hd t ⟨ht.1,ht.2.trans_le hr.2⟩)
    (continuous_const.intervalIntegrable R r)
  rw [intervalIntegral.integral_zero,spectralWKBAmplitude_initial,ha₀] at hi
  exact sub_eq_zero.mp hi.symm

end DefocusingNLS

end OAI
