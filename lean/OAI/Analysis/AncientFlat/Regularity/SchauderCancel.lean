import OAI.Analysis.AncientFlat.Kernel.ClassicalBase

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff BoundedContinuousFunction SchwartzMap
namespace ParabolicSchauder
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma norm_cancel_integral (k : V → E) (hk : Continuous k) (hz : ∫ z,k z=0)
    (B : V → ℝ) (hB : Integrable B) (_hBp : ∀ z,0≤B z) (hb : ∀ z,‖k z‖≤B z)
    (α : ℝ) (_hα : 0≤α) (hw : Integrable (fun z => ‖z‖^α*B z))
    (f : V →ᵇ ℂ) (H : ℝ) (hH : 0≤H)
    (hf : ∀ x y, ‖f x-f y‖≤H*‖x-y‖^α) (r : ℝ) (hr : 0<r) (x : V) :
    ‖∫ z, f (x-r • z) • k z‖≤H*r^α*(∫ z,‖z‖^α*B z) := by
  have hki : Integrable k := hB.mono' hk.aestronglyMeasurable (Eventually.of_forall hb)
  have hi : Integrable (fun z => f (x-r • z) • k z) := by
    apply (hB.const_mul ‖f‖).mono'
    · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul hk).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb z) (norm_nonneg _) (norm_nonneg _)
  have hz' : ∫ z,f x • k z=0 := by rw [integral_smul,hz,smul_zero]
  have hd (z : V) : ‖f (x-r • z)-f x‖≤H*r^α*‖z‖^α := by
    have hd : ‖(x-r • z)-x‖=r*‖z‖ := by
      rw [sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    simpa only [hd,Real.mul_rpow hr.le (norm_nonneg _),mul_assoc] using hf (x-r • z) x
  calc
    _ = ‖∫ z, (f (x-r • z)-f x) • k z‖ := by
      simp_rw [sub_smul]
      erw [integral_sub hi (hki.smul (f x)),hz',sub_zero]
    _ ≤ ∫ z, (H*r^α)*(‖z‖^α*B z) := by
      apply norm_integral_le_of_norm_le (hw.const_mul _)
      filter_upwards with z
      rw [norm_smul]
      calc
        _ ≤ (H*r^α*‖z‖^α)*B z := mul_le_mul (hd z) (hb z) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = _ := integral_const_mul ..

open SchwartzTimeScale SourceFrozenCancellation
omit [CompleteSpace E] in
lemma exists_normalized_time_diff (K : SchwartzMap V E) (N : ℕ) (hz : ∫ z,K z=0)
    (α : ℝ) (hα : 0≤α) (hα1 : α≤1) :
    ∃ D : ℝ, 0≤D ∧ ∀ a ∈ Icc (1:ℝ) 2, ∀ b ∈ Icc (1:ℝ) 2,
      ∀ (f : V →ᵇ ℂ) (H : ℝ), 0≤H →
      (∀ x y, ‖f x-f y‖≤H*‖x-y‖^α) → ∀ r : ℝ, 0<r → ∀ x,
      ‖(∫ z, f (x-r • z) • atTime K N a z)-(∫ z, f (x-r • z) • atTime K N b z)‖≤
        D*H*r^α*‖a-b‖ := by
  obtain ⟨B,hB,hBw,hBp,hb⟩ := parameter_envelope K N 1 2 zero_lt_one
  obtain ⟨C,hC,hCw,hCp,hc⟩ := parameter_lipschitz_envelope K N 1 2 zero_lt_one
  have hW := integrable_envelope_power C hC hCw hCp α hα hα1
  refine ⟨∫ z,‖z‖^α*C z,integral_nonneg (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hCp z)),?_⟩
  intro a ha b hb' f H hH hf r hr x
  have hp {a : ℝ} (ha : a∈Icc (1:ℝ) 2) : 0<a := zero_lt_one.trans_le ha.1
  have hi (a : ℝ) (ha : a∈Icc (1:ℝ) 2) : Integrable (fun z => atTime K N a z) :=
    hB.mono' (continuous_variable K N (fun _ => a) continuous_const (fun _ => hp ha)).aestronglyMeasurable
      (Eventually.of_forall (hb a ha))
  have hi' (a : ℝ) (ha : a∈Icc (1:ℝ) 2) : Integrable (fun z => f (x-r • z) • atTime K N a z) := by
    apply (hB.const_mul ‖f‖).mono'
    · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul
        (continuous_variable K N (fun _ => a) continuous_const (fun _ => hp ha))).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb a ha z) (norm_nonneg _) (norm_nonneg _)
  have hz' : ∫ z,atTime K N a z-atTime K N b z=0 := by
    rw [integral_sub (hi a ha) (hi b hb'),integral_atTime_zero K N a (hp ha) hz,
      integral_atTime_zero K N b (hp hb') hz,sub_self]
  rw [← integral_sub (hi' a ha) (hi' b hb')]
  simp_rw [← smul_sub]
  have he := norm_cancel_integral (fun z => atTime K N a z-atTime K N b z)
    ((continuous_variable K N (fun _ => a) continuous_const (fun _ => hp ha)).sub
      (continuous_variable K N (fun _ => b) continuous_const (fun _ => hp hb')))
    hz' (fun z => C z*‖a-b‖) (hC.mul_const _) (fun z => mul_nonneg (hCp z) (norm_nonneg _))
    (hc a ha b hb') α hα (by simpa only [mul_assoc] using hW.mul_const ‖a-b‖) f H hH hf r hr x
  apply he.trans_eq
  simp_rw [← mul_assoc]
  rw [integral_mul_const]
  ring
end ParabolicSchauder

end

end OAI
