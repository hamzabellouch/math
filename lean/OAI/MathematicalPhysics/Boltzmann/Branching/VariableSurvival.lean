import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBranchingBlocks

namespace OAI

/-! # Positive characteristic forcing with an integrable loss frequency -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem exp_absolutelyContinuous {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => Real.exp (f t)) a b := by
  obtain ⟨C,hC⟩ := hf.exists_bound
  obtain ⟨L,hL⟩ := (Real.contDiff_exp.contDiffOn :
    ContDiffOn ℝ 1 Real.exp (Icc (-C) C)).exists_lipschitzOnWith
      (by norm_num) (convex_Icc _ _) isCompact_Icc
  apply hL.comp_absolutelyContinuousOnInterval _ hf
  intro t ht
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hC t ht)

/-- The integrating factor keeps the positive forcing when the frequency is only integrable. -/
theorem variable_survival_with_source {T : ℝ} (hT : 0 ≤ T)
    {u r k g : ℝ → ℝ} (hu : AbsolutelyContinuousOnInterval u 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hg : IntervalIntegrable g volume 0 T)
    (hr : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt u (r t) t)
    (hb : ∀ᵐ t, t ∈ Icc 0 T → g t-k t*u t ≤ r t) :
    Real.exp (-(∫ t in 0..T, k t))*u 0 +
      (∫ t in 0..T, Real.exp (-((∫ s in 0..T, k s)-(∫ s in 0..t, k s)))*g t) ≤ u T := by
  let K : ℝ → ℝ := fun t => ∫ s in 0..t, k s
  let W : ℝ → ℝ := fun t => Real.exp (K t)*u t
  have hK : AbsolutelyContinuousOnInterval K 0 T :=
    hk.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have he := exp_absolutelyContinuous hK
  have hW : AbsolutelyContinuousOnInterval W 0 T := he.mul hu
  have hi : IntervalIntegrable (fun t => Real.exp (K t)*g t) volume 0 T :=
    hg.continuousOn_mul he.continuousOn
  have hd : ∀ᵐ t, t ∈ Icc 0 T → Real.exp (K t)*g t ≤ deriv W t := by
    filter_upwards [hk.ae_hasDerivAt_integral,hr,hb] with t ht hrt hbt hmem
    have hkt : HasDerivAt K (k t) t := ht (by simpa only [uIcc_of_le hT] using hmem)
      0 left_mem_uIcc
    have hwt := hkt.exp.mul (hrt hmem)
    change HasDerivAt W _ t at hwt
    rw [hwt.deriv]
    have hp := mul_le_mul_of_nonneg_left (hbt hmem) (Real.exp_pos (K t)).le
    nlinarith only [hp]
  have hint : (∫ t in 0..T, Real.exp (K t)*g t) ≤ ∫ t in 0..T, deriv W t := by
    apply intervalIntegral.integral_mono_ae_restrict hT hi hW.intervalIntegrable_deriv
    filter_upwards [ae_restrict_of_ae hd,ae_restrict_mem measurableSet_Icc] with t ht hm
    exact ht hm
  rw [hW.integral_deriv_eq_sub] at hint
  have hW0 : W 0 = u 0 := by simp [W,K]
  rw [hW0] at hint
  have hmul := mul_le_mul_of_nonneg_left hint (Real.exp_pos (-K T)).le
  have hcancel : Real.exp (-K T)*Real.exp (K T) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have heq : Real.exp (-K T)*(∫ t in 0..T, Real.exp (K t)*g t) =
      ∫ t in 0..T, Real.exp (-(K T-K t))*g t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [heq] at hmul
  dsimp only [W] at hmul
  rw [mul_sub,← mul_assoc,hcancel,one_mul] at hmul
  dsimp only [K] at hmul
  linarith

end BoltzmannNonuniqueness.TransportPrimitive

end

end OAI
