import OAI.NumberTheory.CubicMoment.Estimates.MellinNonvanishingTest

namespace OAI

/-! The fixed nonnegative partition test has a positive Mellin transform
at every real parameter. Its reciprocal is bounded on a compact real strip. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma normPartitionWeight_real_nonneg (x : ℝ) : 0 ≤ (normPartitionWeight x).re := by
  by_cases hx : x < 1
  · rw [normPartitionWeight_low hx]; simp
  · change 0 ≤ normPartitionStep x-normPartitionStep (3*x/4)
    exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

lemma normPartitionWeight_mellin_real_positive (σ : ℝ) :
    0 < (mellin normPartitionWeight (σ:ℂ)).re := by
  let W := mellinPhaseCancelWeight (2-(σ:ℂ))
  let f : ℝ → ℝ := fun x => (W x).re
  have he (x : ℝ) : W x =
      normPartitionWeight x*(Real.exp ((σ-1)*Real.log x):ℂ) := by
    dsimp [W,mellinPhaseCancelWeight]
    have h : (1-(2-(σ:ℂ)))*(Real.log x:ℂ) = (((σ-1)*Real.log x:ℝ):ℂ) := by
      push_cast; ring
    rw [h,Complex.ofReal_exp]
  have hf : Continuous f := Complex.continuous_re.comp
    (mellinPhaseCancelWeight_smooth (2-(σ:ℂ))).continuous
  have hfc : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact normPartitionWeight_compact.isCompact
    intro x hx
    apply subset_tsupport
    intro hn
    exact hx (by dsimp [f]; rw [he,hn,zero_mul]; simp)
  have hfn (x : ℝ) : 0 ≤ f x := by
    dsimp [f]
    rw [he]
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using
      mul_nonneg (normPartitionWeight_real_nonneg x) (Real.exp_pos _).le
  have hp : 0 < ∫ x : ℝ, f x := by
    apply integral_pos_of_integrable_nonneg_nonzero hf
      (hf.integrable_of_hasCompactSupport hfc) hfn (x := (4/3:ℝ))
    dsimp [f]
    rw [he]
    have hw : normPartitionWeight (4/3) = 1 := by
      simp only [normPartitionWeight,normPartitionStep_one le_rfl]
      norm_num [normPartitionStep]
    rw [hw,one_mul,Complex.ofReal_re]
    exact (Real.exp_pos _).ne'
  have hsupp : Function.support f ⊆ Ioi 0 := by
    intro x hx
    apply normPartitionWeight_positive_support
    apply subset_tsupport
    intro hn
    exact hx (by dsimp [f]; rw [he,hn,zero_mul]; simp)
  have hi : mellin normPartitionWeight (σ:ℂ) = ((∫ x : ℝ, f x : ℝ):ℂ) := by
    unfold mellin
    have heq (x : ℝ) (hx : x ∈ Ioi 0) :
        (x:ℂ)^((σ:ℂ)-1) • normPartitionWeight x = (f x:ℂ) := by
      rw [smul_eq_mul,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
        ←Complex.ofReal_log hx.le]
      have hexp : (Real.log x:ℂ)*((σ:ℂ)-1) = (((σ-1)*Real.log x:ℝ):ℂ) := by
        push_cast; ring
      rw [hexp,←Complex.ofReal_exp]
      dsimp [f]
      rw [he]
      have hw : ((normPartitionWeight x).re:ℂ) = normPartitionWeight x := by
        simp only [normPartitionWeight,Complex.ofReal_re]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
        Complex.ofReal_mul,hw]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq,integral_complex_ofReal,
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by by_contra hn; exact hx (hsupp hn))]
  rw [hi,Complex.ofReal_re]
  exact hp

theorem normPartitionWeight_mellin_inverse_bound (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc a b, ‖(mellin normPartitionWeight (σ:ℂ))⁻¹‖ ≤ C := by
  have hc : Continuous (fun σ : ℝ => ‖mellin normPartitionWeight (σ:ℂ)‖) :=
    ((smooth_mellin_entire normPartitionWeight normPartitionWeight_compact
      normPartitionWeight_positive_support normPartitionWeight_smooth.continuous).continuous.comp
      Complex.continuous_ofReal).norm
  obtain ⟨d,hd,hbound⟩ := isCompact_Icc.exists_forall_le' hc.continuousOn
    (a := (0:ℝ)) (fun σ _ => norm_pos_iff.mpr (fun hz => by
      have hp := normPartitionWeight_mellin_real_positive σ
      rw [hz,Complex.zero_re] at hp
      exact lt_irrefl _ hp))
  refine ⟨d⁻¹,inv_nonneg.mpr hd.le,?_⟩
  intro σ hσ
  rw [norm_inv]
  exact inv_anti₀ hd (hbound σ hσ)

end CubicFirstMoment

end

end OAI
