import OAI.NumberTheory.JointDickman.Counting.CoefficientDensityRegularity
import OAI.NumberTheory.JointDickman.Counting.CoefficientFourierContinuity
import OAI.NumberTheory.JointDickman.Amplification.MajorArcErrorSum

namespace OAI

/-! # Freezing the slowly varying coefficient density inside one box -/

namespace JointDickman
open MeasureTheory Filter

noncomputable def testFourierTransform (w : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ s : ℝ, (w s : ℂ)*additivePhase (-ξ*s)

theorem compact_weighted_phase_integral {a b : ℝ} (hab : a ≤ b)
    {w : ℝ → ℝ} (hsupp : ∀ s, s ≤ a ∨ b < s → w s = 0)
    (ρ : ℝ → ℂ) (ξ : ℝ) :
    (∫ s : ℝ, (w s : ℂ)*ρ s*additivePhase (-ξ*s)) =
      ∫ s in a..b, (w s : ℂ)*ρ s*additivePhase (-ξ*s) := by
  rw [intervalIntegral.integral_of_le hab]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro s hs
  have h : s ≤ a ∨ b < s := by
    by_cases hsa : s ≤ a
    · exact Or.inl hsa
    · exact Or.inr (lt_of_not_ge (fun hsb => hs ⟨lt_of_not_ge hsa,hsb⟩))
  simp only [hsupp s h,Complex.ofReal_zero,zero_mul]

theorem coefficientDensity_log_difference (c : ℕ → ℝ) (H B : ℕ)
    {X s δ L : ℝ} (hB : 0 < B) (hX : 0 < X) (hs : 0 < s)
    (hx : δ ≤ Real.log X/B) (hsx : δ ≤ Real.log (s*X)/B)
    (hLip : ∀ u v : ℝ, δ ≤ u → δ ≤ v →
      |coefficientDensity c H B u-coefficientDensity c H B v| ≤ L*|u-v|) :
    |coefficientDensity c H B (Real.log (s*X)/B)-coefficientDensity c H B (Real.log X/B)| ≤
      L*|Real.log s|/B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := hLip _ _ hsx hx
  have he : Real.log (s*X)/(B : ℝ)-Real.log X/B = Real.log s/B := by
    rw [Real.log_mul hs.ne' hX.ne']
    ring
  simpa only [he,abs_div,abs_of_pos hB0,mul_div_assoc] using hh

theorem coefficientFourier_freeze_bound (c : ℕ → ℝ) (H B : ℕ)
    {X a b δ M L R : ℝ} (hB : 0 < B) (hX : 0 < X) (ha : 0 < a) (hab : a ≤ b)
    (haX : 1 < a*X) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hx : δ ≤ Real.log X/B) (hsx : ∀ s ∈ Set.Icc a b, δ ≤ Real.log (s*X)/B)
    (hLip : ∀ u v : ℝ, δ ≤ u → δ ≤ v →
      |coefficientDensity c H B u-coefficientDensity c H B v| ≤ L*|u-v|)
    {w : ℝ → ℝ} (hw : Continuous w) (hwb : ∀ s, |w s| ≤ M)
    (hsupp : ∀ s, s ≤ a ∨ b < s → w s = 0)
    (hlog : ∀ s ∈ Set.Icc a b, |Real.log s| ≤ R) (ξ : ℝ) :
    ‖coefficientFourierTransform c H B X w ξ-
      (coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ‖ ≤
      (b-a)*M*(L*R/B) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let f : ℝ → ℂ := fun s => (w s : ℂ)*additivePhase (-ξ*s)
  let g : ℝ → ℂ := fun s => (coefficientDensity c H B (Real.log (s*X)/B) : ℂ)
  let d : ℂ := (coefficientDensity c H B (Real.log X/B) : ℂ)
  have hf : Continuous f := (Complex.continuous_ofReal.comp hw).mul
    (continuous_additivePhase.comp (continuous_const.mul continuous_id))
  have hg : ContinuousOn g (Set.Icc a b) := Complex.continuous_ofReal.comp_continuousOn
    (coefficient_scaled_density_continuousOn c H B hB hX haX)
  have hi : IntervalIntegrable (fun s => f s*g s) volume a b :=
    (hf.continuousOn.mul hg).intervalIntegrable_of_Icc hab
  have hid : IntervalIntegrable (fun s => d*f s) volume a b :=
    (continuous_const.mul hf).intervalIntegrable a b
  have hc : coefficientFourierTransform c H B X w ξ = ∫ s in a..b, f s*g s := by
    rw [coefficientFourierTransform,compact_weighted_phase_integral hab hsupp]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp [f,g]
    ring
  have ht : testFourierTransform w ξ = ∫ s in a..b, f s := by
    simpa only [testFourierTransform,mul_one,f] using
      compact_weighted_phase_integral hab hsupp (fun _ => (1 : ℂ)) ξ
  rw [hc,ht,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hi hid]
  have hbound : ∀ s ∈ Set.uIoc a b, ‖f s*g s-d*f s‖ ≤ M*(L*R/B) := by
    intro s hs
    have hs' : s ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc hs
    have he := coefficientDensity_log_difference c H B hB hX (ha.trans_le hs'.1) hx
      (hsx s hs') hLip
    have he' : ‖g s-d‖ ≤ L*R/B := by
      dsimp [g,d]
      rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      exact he.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hlog s hs') hL) hB0.le)
    have hfb : ‖f s‖ ≤ M := by
      simpa only [f,norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs]
        using hwb s
    calc
      _ = ‖f s*(g s-d)‖ := by congr 1; ring
      _ = ‖f s‖*‖g s-d‖ := norm_mul _ _
      _ ≤ _ := mul_le_mul hfb he' (norm_nonneg _) hM
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab),mul_comm (M*(L*R/B)),mul_assoc] using hh

end JointDickman

end OAI
