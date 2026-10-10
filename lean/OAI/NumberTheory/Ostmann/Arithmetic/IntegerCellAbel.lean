import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCellCount

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.IntegerCell
open scoped BigOperators
open Set MeasureTheory PrimeProgression

theorem smooth_residue_error_identity (M : ℕ) [NeZero M] (a : ZMod M)
    (f D : ℝ → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hf : ∀ t ∈ Icc A B, HasDerivAt f (D t) t) (hD : ContinuousOn D (Icc A B)) :
    (∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, f n * residueIndicator M a n) -
        (∫ t in A..B, f t)/(M : ℝ) =
      f B*(cumulativeSum (residueIndicator M a) B-B/M) -
      f A*(cumulativeSum (residueIndicator M a) A-A/M) -
      ∫ t in A..B, D t*(cumulativeSum (residueIndicator M a) t-t/M) := by
  have hc : ContinuousOn f (Icc A B) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hderiv : IntegrableOn (deriv f) (Icc A B) :=
    hD.integrableOn_Icc.congr_fun (fun t ht => (hf t ht).deriv.symm) measurableSet_Icc
  have ha := sum_mul_eq_sub_sub_integral_mul (residueIndicator M a) hA hAB
    (fun t ht => (hf t ht).differentiableAt) hderiv
  rw [← intervalIntegral.integral_of_le hAB] at ha
  change (∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, f n * residueIndicator M a n) =
    f B*cumulativeSum (residueIndicator M a) B-f A*cumulativeSum (residueIndicator M a) A-
      ∫ t in A..B, deriv f t*cumulativeSum (residueIndicator M a) t at ha
  have hid : (∫ t in A..B, deriv f t*cumulativeSum (residueIndicator M a) t) =
      ∫ t in A..B, D t*cumulativeSum (residueIndicator M a) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [(hf t (by simpa only [uIcc_of_le hAB] using ht)).deriv]
  rw [hid] at ha
  have hmain := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (v := fun t : ℝ => t/M) (u' := D) (v' := fun _ => (M : ℝ)⁻¹)
    (by simpa only [uIcc_of_le hAB] using hc)
    (continuous_id.div_const (M : ℝ)).continuousOn
    (fun t ht => hf t (by
      simp only [min_eq_left hAB, max_eq_right hAB] at ht
      exact ⟨ht.1.le, ht.2.le⟩))
    (fun t _ => by simpa only [one_div, id_eq] using (hasDerivAt_id t).div_const (M : ℝ))
    (hD.intervalIntegrable_of_Icc hAB) intervalIntegrable_const
  rw [intervalIntegral.integral_mul_const] at hmain
  have hiC : IntervalIntegrable
      (fun t => D t*cumulativeSum (residueIndicator M a) t) volume A B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr
      (integrableOn_mul_sum_Icc (residueIndicator M a) hA hD.integrableOn_Icc)
  have hiM : IntervalIntegrable (fun t : ℝ => D t*(t/M)) volume A B :=
    (hD.mul (continuous_id.div_const (M : ℝ)).continuousOn).intervalIntegrable_of_Icc hAB
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hiC hiM, ha]
  rw [div_eq_mul_inv]
  rw [hmain]
  ring

theorem smooth_residue_error_bound (M : ℕ) [NeZero M] (a : ZMod M)
    (f D : ℝ → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hf : ∀ t ∈ Icc A B, HasDerivAt f (D t) t) (hD : ContinuousOn D (Icc A B)) :
    |(∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, f n * residueIndicator M a n) -
      (∫ t in A..B, f t)/(M : ℝ)| ≤
        2*(|f A|+|f B|+(∫ t in A..B, |D t|)) := by
  have hiC : IntervalIntegrable
      (fun t => D t*cumulativeSum (residueIndicator M a) t) volume A B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr
      (integrableOn_mul_sum_Icc (residueIndicator M a) hA hD.integrableOn_Icc)
  have hiM : IntervalIntegrable (fun t : ℝ => D t*(t/M)) volume A B :=
    (hD.mul (continuous_id.div_const (M : ℝ)).continuousOn).intervalIntegrable_of_Icc hAB
  have hiErr : IntervalIntegrable
      (fun t => D t*(cumulativeSum (residueIndicator M a) t-t/M)) volume A B := by
    simp_rw [mul_sub]
    exact hiC.sub hiM
  have he (t : ℝ) (ht : t ∈ Icc A B) :=
    cumulative_residue_error M a t (hA.trans ht.1)
  have hI : |∫ t in A..B, D t*(cumulativeSum (residueIndicator M a) t-t/M)| ≤
      2*(∫ t in A..B, |D t|) := by
    calc
      _ ≤ ∫ t in A..B, |D t*(cumulativeSum (residueIndicator M a) t-t/M)| :=
        intervalIntegral.abs_integral_le_integral_abs hAB
      _ ≤ ∫ t in A..B, 2*|D t| := by
        apply intervalIntegral.integral_mono_on hAB hiErr.abs
          ((hD.abs.const_mul 2).intervalIntegrable_of_Icc hAB)
        intro t ht
        rw [abs_mul, mul_comm 2]
        exact mul_le_mul_of_nonneg_left (he t ht) (abs_nonneg _)
      _ = _ := intervalIntegral.integral_const_mul _ _
  have heA : |f A*(cumulativeSum (residueIndicator M a) A-A/M)| ≤ 2*|f A| := by
    rw [abs_mul, mul_comm 2]
    exact mul_le_mul_of_nonneg_left (he A ⟨le_rfl, hAB⟩) (abs_nonneg _)
  have heB : |f B*(cumulativeSum (residueIndicator M a) B-B/M)| ≤ 2*|f B| := by
    rw [abs_mul, mul_comm 2]
    exact mul_le_mul_of_nonneg_left (he B ⟨hAB, le_rfl⟩) (abs_nonneg _)
  rw [smooth_residue_error_identity M a f D hA hAB hf hD]
  calc
    _ ≤ |f B*(cumulativeSum (residueIndicator M a) B-B/M)| +
        |f A*(cumulativeSum (residueIndicator M a) A-A/M)| +
        |∫ t in A..B, D t*(cumulativeSum (residueIndicator M a) t-t/M)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by linarith

end Ostmann.Arithmetic.IntegerCell
end

end OAI
