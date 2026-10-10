import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDirichletLinearity

namespace OAI

/-! A Bielecki estimate for the nonsingular radial initial-value integral. -/

open MeasureTheory Set
namespace DefocusingNLS

noncomputable def radialVolterra (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, t*radialAverage f t

theorem radialVolterra_eq_neg_kernel (f : ℝ → ℝ) (r : ℝ) :
    radialVolterra f r= -radialDirichletKernel 0 f r := by
  unfold radialVolterra radialDirichletKernel
  rw [intervalIntegral.integral_symm]

theorem hasDerivAt_radialVolterra (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ) :
    HasDerivAt (radialVolterra f) (r*radialAverage f r) r := by
  have he : radialVolterra f=fun t => -radialDirichletKernel 0 f t :=
    funext (radialVolterra_eq_neg_kernel f)
  rw [he]
  convert! (hasDerivAt_radialDirichletKernel 0 f hf r).neg using 1
  simp

theorem radialVolterra_sub (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (r : ℝ) :
    radialVolterra (f-g) r=radialVolterra f r-radialVolterra g r := by
  simp_rw [radialVolterra_eq_neg_kernel]
  rw [sub_eq_add_neg,radialDirichletKernel_add 0 r f (-g) hf hg.neg]
  have hn : (-g : ℝ → ℝ)=(-1 : ℝ) • g := by ext t; simp
  rw [hn,radialDirichletKernel_smul]
  ring

theorem radialVolterra_norm_le (f : ℝ → ℝ) (C r : ℝ) (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc 0 r, ‖f t‖ ≤ C) : ‖radialVolterra f r‖ ≤ C*r^2/24 := by
  simpa only [radialVolterra,radialDirichletKernel,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    sub_zero] using radialDirichletKernel_norm_le f r C 0 le_rfl hr hf

theorem radialAverage_exponential_bound (f : ℝ → ℝ) (C η r : ℝ)
    (hC : 0 ≤ C) (hη : 0 ≤ η) (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc 0 r, ‖f t‖ ≤ C*Real.exp (η*t)) :
    ‖radialAverage f r‖ ≤ C*Real.exp (η*r)/12 := by
  apply radialAverage_norm_le f r _ r hr le_rfl
  intro t ht
  exact (hf t ht).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hη)) hC)

theorem integral_exp_scale (η r : ℝ) (hη : 0 < η) :
    (∫ t in (0 : ℝ)..r, Real.exp (η*t))=(Real.exp (η*r)-1)/η := by
  have h := intervalIntegral.mul_integral_comp_mul_left (f := Real.exp)
    (a := (0 : ℝ)) (b := r) η
  rw [integral_exp] at h
  simp only [mul_zero,Real.exp_zero] at h
  apply (eq_div_iff hη.ne').2
  simpa only [mul_comm] using h

theorem radialVolterra_exponential_bound (f : ℝ → ℝ) (C η r : ℝ)
    (hC : 0 ≤ C) (hη : 0 < η) (hr : 0 ≤ r)
    (hf : ∀ t ∈ Icc 0 r, ‖f t‖ ≤ C*Real.exp (η*t)) :
    ‖radialVolterra f r‖ ≤ C*r/(12*η)*Real.exp (η*r) := by
  have hi : IntervalIntegrable (fun t : ℝ => (C*r/12)*Real.exp (η*t)) volume 0 r :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 r
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun t : ℝ => t*radialAverage f t)
    (g := fun t : ℝ => (C*r/12)*Real.exp (η*t)) hr
    (Filter.Eventually.of_forall fun t ht => ?_) hi
  · calc
      ‖radialVolterra f r‖ ≤ ∫ t in (0 : ℝ)..r, (C*r/12)*Real.exp (η*t) := h
      _ = (C*r/12)*((Real.exp (η*r)-1)/η) := by
        rw [intervalIntegral.integral_const_mul,integral_exp_scale η r hη]
      _ ≤ C*r/(12*η)*Real.exp (η*r) := by
        have hp : 0 ≤ C*r/(12*η) := by positivity
        have he : Real.exp (η*r)-1 ≤ Real.exp (η*r) := by linarith
        convert mul_le_mul_of_nonneg_left he hp using 1
        ring
  · have ht0 : 0 ≤ t := ht.1.le
    have ha := radialAverage_exponential_bound f C η t hC hη.le ht0
      (fun s hs => hf s ⟨hs.1,hs.2.trans ht.2⟩)
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ht0]
    calc
      t*‖radialAverage f t‖ ≤ t*(C*Real.exp (η*t)/12) :=
        mul_le_mul_of_nonneg_left ha ht0
      _ ≤ r*(C*Real.exp (η*t)/12) :=
        mul_le_mul_of_nonneg_right ht.2 (by positivity)
      _ = (C*r/12)*Real.exp (η*t) := by ring

end DefocusingNLS

end OAI
