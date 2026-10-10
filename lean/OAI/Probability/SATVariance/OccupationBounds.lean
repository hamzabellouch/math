import OAI.Probability.SATVariance.FiniteVariance

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma integrated_tail_subcritical {F : ℝ → ℝ} (hF : Antitone F)
    {A θ : ℝ} (hθ : θ < 1)
    (hbound : ∀ a ∈ Set.Ioo (0 : ℝ) 1, F a ≤ A * a^(-θ)) :
    (∫ a in (0 : ℝ)..1, F a) ≤ A / (1-θ) := by
  have hp : -1 < -θ := by linarith
  calc
    (∫ a in (0 : ℝ)..1, F a) ≤ ∫ a in (0 : ℝ)..1, A*a^(-θ) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
        hF.intervalIntegrable ((intervalIntegral.intervalIntegrable_rpow' hp).const_mul A)
      exact hbound
    _ = A/(1-θ) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hp),
        Real.one_rpow, Real.zero_rpow (by linarith : -θ+1 ≠ 0)]
      ring

lemma integrated_tail_critical {F : ℝ → ℝ} (hF : Antitone F)
    {A L : ℝ} (hA : 1 ≤ A) (hL : 1 ≤ L)
    (hmass : ∀ a, F a ≤ L)
    (hbound : ∀ a ∈ Set.Ioo (0 : ℝ) 1, F a ≤ A/a) :
    (∫ a in (0 : ℝ)..1, F a) ≤ A * (1+Real.log L) := by
  have hL₀ : 0 < L := by linarith
  have hd : 0 < L⁻¹ := inv_pos.mpr hL₀
  have hd1 : L⁻¹ ≤ 1 := (inv_le_one₀ hL₀).mpr hL
  have hleft : (∫ a in (0 : ℝ)..L⁻¹, F a) ≤ 1 := by
    calc
      _ ≤ ∫ _a in (0 : ℝ)..L⁻¹, L := by
        exact intervalIntegral.integral_mono_on hd.le hF.intervalIntegrable
          intervalIntegrable_const (fun a _ => hmass a)
      _ = 1 := by simp [intervalIntegral.integral_const, hL₀.ne']
  have hIi : IntervalIntegrable (fun a : ℝ => a⁻¹) volume L⁻¹ 1 := by
    apply intervalIntegral.intervalIntegrable_inv _ continuous_id.continuousOn
    intro a ha
    rw [Set.uIcc_of_le hd1] at ha
    exact (hd.trans_le ha.1).ne'
  have hright : (∫ a in L⁻¹..(1 : ℝ), F a) ≤ A*Real.log L := by
    calc
      _ ≤ ∫ a in L⁻¹..(1 : ℝ), A*a⁻¹ := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hd1 hF.intervalIntegrable
          (hIi.const_mul A)
        intro a ha
        simpa only [div_eq_mul_inv] using hbound a ⟨lt_trans hd ha.1, ha.2⟩
      _ = A*Real.log L := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hd (by norm_num)]
        simp
  calc
    _ = (∫ a in (0 : ℝ)..L⁻¹, F a) + (∫ a in L⁻¹..(1 : ℝ), F a) :=
      (intervalIntegral.integral_add_adjacent_intervals hF.intervalIntegrable
        hF.intervalIntegrable).symm
    _ ≤ 1 + A*Real.log L := add_le_add hleft hright
    _ ≤ A*(1+Real.log L) := by nlinarith

end RandomKSAT

end

end OAI
