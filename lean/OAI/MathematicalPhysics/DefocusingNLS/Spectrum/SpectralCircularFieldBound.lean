import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularField

namespace OAI

/-! A uniform Lipschitz bound for the actual rescaled circular field on bounded profiles. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularRow_bound (A B C D : ℂ) (v w : ℂ × ℂ) :
    ‖(v.2,A*v.2+B*v.1+C*v.1+D*w.1)‖ ≤
      (1+‖A‖+‖B‖+‖C‖+‖D‖)*max ‖v‖ ‖w‖ := by
  have hv1 : ‖v.1‖ ≤ max ‖v‖ ‖w‖ := (norm_fst_le v).trans (le_max_left _ _)
  have hv2 : ‖v.2‖ ≤ max ‖v‖ ‖w‖ := (norm_snd_le v).trans (le_max_left _ _)
  have hw1 : ‖w.1‖ ≤ max ‖v‖ ‖w‖ := (norm_fst_le w).trans (le_max_right _ _)
  have hM : 0 ≤ max ‖v‖ ‖w‖ := (norm_nonneg v).trans (le_max_left _ _)
  change max ‖v.2‖ ‖A*v.2+B*v.1+C*v.1+D*w.1‖ ≤ _
  apply max_le
  · nlinarith [mul_nonneg (norm_nonneg A) hM,mul_nonneg (norm_nonneg B) hM,
      mul_nonneg (norm_nonneg C) hM,mul_nonneg (norm_nonneg D) hM]
  · calc
      _ ≤ ‖A*v.2+B*v.1+C*v.1‖+‖D*w.1‖ := norm_add_le _ _
      _ ≤ (‖A*v.2+B*v.1‖+‖C*v.1‖)+‖D*w.1‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖A*v.2‖+‖B*v.1‖)+‖C*v.1‖)+‖D*w.1‖ := by gcongr; exact norm_add_le _ _
      _ = ((‖A‖*‖v.2‖+‖B‖*‖v.1‖)+‖C‖*‖v.1‖)+‖D‖*‖w.1‖ := by simp only [norm_mul]
      _ ≤ ((‖A‖*max ‖v‖ ‖w‖+‖B‖*max ‖v‖ ‖w‖)+‖C‖*max ‖v‖ ‖w‖)+
          ‖D‖*max ‖v‖ ‖w‖ := by gcongr
      _ ≤ _ := by nlinarith

theorem circularFieldBound_nonneg (νp νm η : ℂ) (m : ℕ) (M : ℝ) :
    0 ≤ circularFieldBound νp νm η m M := by
  unfold circularFieldBound
  have hpow : 0 ≤ M^(2*m) := by rw [Nat.mul_comm 2 m,pow_mul]; exact sq_nonneg (M^m)
  positivity

theorem circularBoundedField_norm (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (M : ℝ) (q : ℂ) (hq : ‖q‖ ≤ M) (z : E₄) :
    ‖circularBoundedField νp νm η m q z‖ ≤ circularFieldBound νp νm η m M*‖z‖ := by
  have hpow := pow_le_pow_left₀ (norm_nonneg q) hq (2*m)
  have hP : ‖spectralDiagonalCoefficient m q‖+‖spectralCrossCoefficient m q‖ ≤
      (2*(m : ℝ)+1)*M^(2*m) := by
    rw [spectralDiagonalCoefficient_norm,spectralCrossCoefficient_norm m hm]
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2*(m : ℝ)+1 by positivity)
    nlinarith
  have hp := circularRow_bound (-(2*νp+10)) (-(νp*(νp+10)-η))
    (spectralDiagonalCoefficient m q) (spectralCrossCoefficient m q) z.1 z.2
  have hm' := circularRow_bound (-(2*νm+10)) (-(νm*(νm+10)-η))
    (star (spectralDiagonalCoefficient m q)) (star (spectralCrossCoefficient m q)) z.2 z.1
  simp only [norm_neg,norm_star] at hp hm'
  rw [max_comm ‖z.2‖ ‖z.1‖] at hm'
  change max ‖(z.1.2,-(2*νp+10)*z.1.2-(νp*(νp+10)-η)*z.1.1+
      spectralDiagonalCoefficient m q*z.1.1+spectralCrossCoefficient m q*z.2.1)‖
    ‖(z.2.2,-(2*νm+10)*z.2.2-(νm*(νm+10)-η)*z.2.1+
      star (spectralDiagonalCoefficient m q)*z.2.1+star (spectralCrossCoefficient m q)*z.1.1)‖ ≤ _
  apply max_le
  · apply (show _ ≤ (1+‖2*νp+10‖+‖νp*(νp+10)-η‖+
        ‖spectralDiagonalCoefficient m q‖+‖spectralCrossCoefficient m q‖)*‖z‖ by
      simpa only [Prod.norm_def,neg_mul,sub_eq_add_neg] using hp).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
    unfold circularFieldBound
    linarith [norm_nonneg (2*νm+10),norm_nonneg (νm*(νm+10)-η)]
  · apply (show _ ≤ (1+‖2*νm+10‖+‖νm*(νm+10)-η‖+
        ‖spectralDiagonalCoefficient m q‖+‖spectralCrossCoefficient m q‖)*‖z‖ by
      simpa only [Prod.norm_def,neg_mul,sub_eq_add_neg] using hm').trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
    unfold circularFieldBound
    linarith [norm_nonneg (2*νp+10),norm_nonneg (νp*(νp+10)-η)]

theorem circularBoundedField_difference (νp νm η : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (M : ℝ) (q : ℂ) (hq : ‖q‖ ≤ M) (z w : E₄) :
    ‖circularBoundedField νp νm η m q z-circularBoundedField νp νm η m q w‖ ≤
      circularFieldBound νp νm η m M*‖z-w‖ := by
  rw [← circularBoundedField_sub]
  exact circularBoundedField_norm νp νm η m hm M q hq (z-w)

end DefocusingNLS

end OAI
