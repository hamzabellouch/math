import OAI.MathematicalPhysics.Boltzmann.Jets.ColdGaussianFamily

namespace OAI

/-! # A lower bound for an integrable source with bounded loss -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.IntegralSurvival

/-- The integrating factor gives survival even when the source inequality holds only a.e. -/
theorem lower_bound {z : ℝ → ℝ} {a C T : ℝ} (hT : 0 ≤ T)
    (hi : IntervalIntegrable z volume 0 T)
    (hb : ∀ᵐ t, t ∈ Icc 0 T → -C * (a + ColdGronwall.primitive z t) ≤ z t) :
    ∀ t ∈ Icc 0 T, Real.exp (-C*t)*a ≤ a + ColdGronwall.primitive z t := by
  let V : ℝ → ℝ := fun t => a + ColdGronwall.primitive z t
  let W : ℝ → ℝ := fun t => Real.exp (C*t)*V t
  have hZ : AbsolutelyContinuousOnInterval (ColdGronwall.primitive z) 0 T :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hc : ContDiff ℝ 1 (fun _ : ℝ => a) := contDiff_const
  have hV : AbsolutelyContinuousOnInterval V 0 T :=
    hc.contDiffOn.absolutelyContinuousOnInterval.add hZ
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (C*t)) := by fun_prop
  have hW : AbsolutelyContinuousOnInterval W 0 T :=
    he.contDiffOn.absolutelyContinuousOnInterval.mul hV
  have hder : ∀ᵐ t, t ∈ Icc 0 T → 0 ≤ deriv W t := by
    filter_upwards [hi.ae_hasDerivAt_integral, hb] with t ht hbt hmem
    have hzt := (ht (by simpa only [uIcc_of_le hT] using hmem) 0 (by simp)).const_add a
    have het := ((hasDerivAt_id t).const_mul C).exp
    have hw := het.mul hzt
    change HasDerivAt W _ t at hw
    rw [hw.deriv]
    have hp := mul_le_mul_of_nonneg_left (hbt hmem) (Real.exp_pos (C*t)).le
    dsimp only [V, ColdGronwall.primitive, id] at hp ⊢
    nlinarith only [hp]
  intro t ht
  have hWt : AbsolutelyContinuousOnInterval W 0 t := by
    apply hW.mono
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    intro r hr
    exact ⟨hr.1, hr.2.trans ht.2⟩
  have hint : 0 ≤ ∫ r in 0..t, deriv W r := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    filter_upwards [ae_restrict_of_ae hder, ae_restrict_mem measurableSet_Icc] with r hr hrt
    exact hr ⟨hrt.1, hrt.2.trans ht.2⟩
  rw [hWt.integral_deriv_eq_sub] at hint
  have hW0 : W 0 = a := by simp [W, V, ColdGronwall.primitive]
  rw [hW0] at hint
  have hmul := mul_le_mul_of_nonneg_left (sub_nonneg.mp hint) (Real.exp_pos (-C*t)).le
  have hexp : Real.exp (-C*t)*Real.exp (C*t) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  simpa only [W, V, ← mul_assoc, hexp, one_mul] using hmul

end BoltzmannNonuniqueness.IntegralSurvival

end

end OAI
