import OAI.Analysis.IrrationalRotation.Sampling.TestedSamplingMoments

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling.TestedSampling

theorem half_le_common_square_bound {m : ℕ} (hm : 200 ≤ m) :
    (1 / 2 : ℝ) ≤ (2 / (m : ℝ)^(-(3 / 5 : ℝ))) *
      Real.log ((m : ℝ)^2 / 2) := by
  obtain ⟨hh, hh1, _, _⟩ := manuscript_parameters hm
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : (1 / 2 : ℝ) ≤ Real.log ((m : ℝ)^2 / 2) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by nlinarith))
  have hfactor : (1 : ℝ) ≤ 2 / (m : ℝ)^(-(3 / 5 : ℝ)) :=
    (le_div_iff₀ hh).2 (by linarith)
  calc
    (1 / 2 : ℝ) = 1 * (1 / 2) := by ring
    _ ≤ (2 / (m : ℝ)^(-(3 / 5 : ℝ))) * Real.log ((m : ℝ)^2 / 2) :=
      mul_le_mul hfactor hlog (by norm_num) (by positivity)

theorem firstTriangular_moment_bounds {m : ℕ} (hm : 200 ≤ m)
    {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MomentBounds m (TestedTriangular.firstKernel E F) := by
  obtain ⟨hi, hmeas, _, hmean, havg, _⟩ :=
    TestedTriangular.firstKernel_moment_bounds hE hF
  refine ⟨hi, hmeas, ?_, ?_, ?_⟩
  · intro s
    exact ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one
      (fun t => (TestedTriangular.firstKernel_bounds E F s t).1),
      (hmean s).trans (by norm_num)⟩
  · refine ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one
      (fun _ => sq_nonneg _), havg.trans ?_⟩
    have hnonneg : 0 ≤ ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by positivity
    linarith
  · exact ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ =>
      intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => sq_nonneg _)),
      (TestedTriangular.testedKernel_reverse_square_moments_le hE hF).1.trans
        (half_le_common_square_bound hm)⟩

theorem secondTriangular_moment_bounds {m : ℕ} (hm : 200 ≤ m)
    {E F : Set ℝ} (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MomentBounds m (TestedTriangular.secondKernel E F) := by
  obtain ⟨hi, hmeas, hnonneg, hmean, havg, _⟩ :=
    TestedTriangular.secondKernel_moment_bounds hE hF
  refine ⟨hi, hmeas, ?_, ?_, ?_⟩
  · intro s
    exact ⟨(hnonneg s).1, (hmean s).trans (by norm_num)⟩
  · refine ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one
      (fun _ => sq_nonneg _), havg.trans ?_⟩
    have hnonneg : 0 ≤ ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by positivity
    linarith
  · exact ⟨intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ =>
      intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => sq_nonneg _)),
      (TestedTriangular.testedKernel_reverse_square_moments_le hE hF).2.trans
        (half_le_common_square_bound hm)⟩

theorem first_choice_moment_bounds {m : ℕ} (hm : 200 ≤ m)
    (selected : Prop) [Decidable selected] {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MomentBounds m (if selected then TestedTriangular.firstKernel E F
      else firstKernel m E F) := by
  by_cases h : selected
  · simpa [h] using firstTriangular_moment_bounds hm hE hF
  · simpa [h] using firstKernel_moment_bounds hm hE hF

theorem second_choice_moment_bounds {m : ℕ} (hm : 200 ≤ m)
    (selected : Prop) [Decidable selected] {E F : Set ℝ}
    (hE : MeasurableSet E) (hF : MeasurableSet F) :
    MomentBounds m (if selected then TestedTriangular.secondKernel E F
      else secondKernel m E F) := by
  by_cases h : selected
  · simpa [h] using secondTriangular_moment_bounds hm hE hF
  · simpa [h] using secondKernel_moment_bounds hm hE hF

end Invariant233.ScalarSampling.TestedSampling

end

end OAI
