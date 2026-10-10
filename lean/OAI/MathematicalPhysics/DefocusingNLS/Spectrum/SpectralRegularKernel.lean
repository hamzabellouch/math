import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGreenOperator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! The nonsingular integral kernel for a regular angular spectral mode at the origin. -/

open Set MeasureTheory intervalIntegral
namespace DefocusingNLS

noncomputable def spectralRegularAverage (d : ℕ) (h : ℝ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (t : ℂ)^d*
    Complex.exp (Complex.I*(h*r^2*(t^2-1)/4 : ℝ))*f (r*t)

noncomputable def spectralRegularPrimitive (d : ℕ) (h : ℝ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..r, (s : ℂ)*spectralRegularAverage d h f s

theorem spectralRegularAverage_continuous (d : ℕ) (h : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) : Continuous (spectralRegularAverage d h f) := by
  apply continuous_parametric_intervalIntegral_of_continuous' _ 0 1
  unfold Function.uncurry
  fun_prop

theorem spectralRegularPrimitive_hasDerivAt (d : ℕ) (h : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (r : ℝ) :
    HasDerivAt (spectralRegularPrimitive d h f)
      ((r : ℂ)*spectralRegularAverage d h f r) r := by
  have hg : Continuous (fun s : ℝ => (s : ℂ)*spectralRegularAverage d h f s) :=
    Complex.continuous_ofReal.mul (spectralRegularAverage_continuous d h f hf)
  exact intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 r)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem spectralRegularPrimitive_continuous (d : ℕ) (h : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) : Continuous (spectralRegularPrimitive d h f) :=
  continuous_iff_continuousAt.mpr (fun r => (spectralRegularPrimitive_hasDerivAt d h f hf r).continuousAt)

theorem spectralRegularAverage_bound (d : ℕ) (h R M r : ℝ) (f : ℝ → ℂ)
    (hr : r ∈ Icc 0 R) (_hM : 0 ≤ M) (hf : ∀ s ∈ Icc 0 R, ‖f s‖ ≤ M) :
    ‖spectralRegularAverage d h f r‖ ≤ M := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M)
    (f := fun t : ℝ => (t : ℂ)^d*
      Complex.exp (Complex.I*(h*r^2*(t^2-1)/4 : ℝ))*f (r*t)) (fun t ht => ?_)
  · simpa only [spectralRegularAverage,sub_zero,abs_one,mul_one] using hb
  · have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨ht.1.le,ht.2⟩
    have hrt : r*t ∈ Icc 0 R :=
      ⟨mul_nonneg hr.1 ht'.1,(mul_le_of_le_one_right hr.1 ht'.2).trans hr.2⟩
    have he : ‖Complex.exp (Complex.I*(h*r^2*(t^2-1)/4 : ℝ))‖=1 := by
      rw [Complex.norm_exp]
      simp [pow_two]
    have hp : ‖(t : ℂ)^d‖ ≤ 1 := by
      rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht'.1]
      exact pow_le_one₀ ht'.1 ht'.2
    rw [norm_mul,norm_mul,he,mul_one]
    exact (mul_le_mul hp (hf _ hrt) (norm_nonneg _) zero_le_one).trans_eq (one_mul M)

theorem spectralRegularPrimitive_bound (d : ℕ) (h R M r : ℝ) (f : ℝ → ℂ)
    (hr : r ∈ Icc 0 R) (hM : 0 ≤ M) (hf : ∀ s ∈ Icc 0 R, ‖f s‖ ≤ M) :
    ‖spectralRegularPrimitive d h f r‖ ≤ R^2*M := by
  have hR : 0 ≤ R := hr.1.trans hr.2
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := r) (C := R*M)
    (f := fun s : ℝ => (s : ℂ)*spectralRegularAverage d h f s) (fun s hs => ?_)
  · change ‖spectralRegularPrimitive d h f r‖ ≤ _ at hb
    rw [sub_zero,abs_of_nonneg hr.1] at hb
    exact hb.trans (by
      calc R*M*r ≤ R*M*R := mul_le_mul_of_nonneg_left hr.2 (mul_nonneg hR hM)
           _ = R^2*M := by ring)
  · have hs' : s ∈ Icc 0 R := by
      rw [uIoc_of_le hr.1] at hs
      exact ⟨hs.1.le,hs.2.trans hr.2⟩
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs'.1]
    exact mul_le_mul hs'.2 (spectralRegularAverage_bound d h R M s f hs' hM hf)
      (norm_nonneg _) hR

theorem spectralRegularAverage_add (d : ℕ) (h : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (r : ℝ) :
    spectralRegularAverage d h (fun s => f s+g s) r=
      spectralRegularAverage d h f r+spectralRegularAverage d h g r := by
  have hif : IntervalIntegrable (fun t : ℝ => (t : ℂ)^d*
      Complex.exp (Complex.I*(h*r^2*(t^2-1)/4 : ℝ))*f (r*t)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hig : IntervalIntegrable (fun t : ℝ => (t : ℂ)^d*
      Complex.exp (Complex.I*(h*r^2*(t^2-1)/4 : ℝ))*g (r*t)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  simp only [spectralRegularAverage,mul_add]
  exact intervalIntegral.integral_add hif hig

theorem spectralRegularAverage_smul (d : ℕ) (h : ℝ) (a : ℂ) (f : ℝ → ℂ) (r : ℝ) :
    spectralRegularAverage d h (fun s => a*f s) r=a*spectralRegularAverage d h f r := by
  unfold spectralRegularAverage
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  ring

theorem spectralRegularPrimitive_add (d : ℕ) (h : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (r : ℝ) :
    spectralRegularPrimitive d h (fun s => f s+g s) r=
      spectralRegularPrimitive d h f r+spectralRegularPrimitive d h g r := by
  simp only [spectralRegularPrimitive,spectralRegularAverage_add d h f g hf hg,mul_add]
  apply intervalIntegral.integral_add
  · exact (Complex.continuous_ofReal.mul (spectralRegularAverage_continuous d h f hf)).intervalIntegrable _ _
  · exact (Complex.continuous_ofReal.mul (spectralRegularAverage_continuous d h g hg)).intervalIntegrable _ _

theorem spectralRegularPrimitive_smul (d : ℕ) (h : ℝ) (a : ℂ) (f : ℝ → ℂ) (r : ℝ) :
    spectralRegularPrimitive d h (fun s => a*f s) r=a*spectralRegularPrimitive d h f r := by
  simp only [spectralRegularPrimitive,spectralRegularAverage_smul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  ring

theorem spectralRegularAverage_scaling (d : ℕ) (h r : ℝ) (f : ℝ → ℂ) :
    (r : ℂ)^(d+1)*Complex.exp (Complex.I*(h*r^2/4 : ℝ))*
        spectralRegularAverage d h f r=
      ∫ t in (0 : ℝ)..r, (t : ℂ)^d*Complex.exp (Complex.I*(h*t^2/4 : ℝ))*f t := by
  let F : ℝ → ℂ := fun t => (t : ℂ)^d*Complex.exp (Complex.I*(h*t^2/4 : ℝ))*f t
  have hs := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) F r
  simp only [mul_zero,mul_one,Complex.real_smul] at hs
  have hfun : (fun t => F (r*t))=fun t : ℝ =>
      ((r : ℂ)^d*Complex.exp (Complex.I*(h*r^2/4 : ℝ)))*
        ((t : ℂ)^d*Complex.exp (Complex.I*(h*r^2*(t^2-1)/4 : ℝ))*f (r*t)) := by
    funext t
    have he : Complex.exp (Complex.I*(h*(r*t)^2/4 : ℝ))=
        Complex.exp (Complex.I*(h*r^2/4 : ℝ))*
          Complex.exp (Complex.I*(h*r^2*(t^2-1)/4 : ℝ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    dsimp only [F]
    rw [he]
    push_cast
    rw [mul_pow]
    ring
  rw [hfun,intervalIntegral.integral_const_mul] at hs
  rw [← hs]
  dsimp only [spectralRegularAverage]
  rw [pow_succ]
  ring

end DefocusingNLS

end OAI
