import OAI.Analysis.IrrationalRotation.Model.ScalarKernelEstimates
import OAI.Analysis.IrrationalRotation.Analysis.ScalarEndpointKernelBounds
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingJensen
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingEndpointVariation

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem unitInterval_mass_sq_le {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1)
    (hfsq : IntervalIntegrable (fun s => (f s)^2) volume 0 1) :
    (∫ s in (0 : ℝ)..1, f s)^2 ≤ ∫ s in (0 : ℝ)..1, (f s)^2 := by
  let c : ℝ := ∫ s in (0 : ℝ)..1, f s
  have heq : (fun s => (f s - c)^2) =
      (fun s => (f s)^2 - (2 * c) * f s + c^2) := by
    funext s
    ring
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..1, (f s - c)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  rw [heq, intervalIntegral.integral_add (hfsq.sub (hf.const_mul (2 * c)))
    intervalIntegrable_const, intervalIntegral.integral_sub hfsq (hf.const_mul (2 * c)),
    intervalIntegral.integral_const_mul] at hnonneg
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hnonneg
  change c^2 ≤ _
  change 0 ≤ (∫ s in (0 : ℝ)..1, (f s)^2) - 2 * c * c + c^2 at hnonneg
  nlinarith

theorem manuscriptKernel_averaged_bounds {m : ℕ} (hm : 200 ≤ m) (s : ℝ) :
    0 ≤ (∫ v in (0 : ℝ)..1, manuscriptKernel m s v) ∧
      (∫ v in (0 : ℝ)..1, manuscriptKernel m s v) ≤ 2 := by
  obtain ⟨hh, hhone, hα, _⟩ := manuscript_parameters hm
  have hb := averaged_circleKernel_bounds hh hhone hα s
  exact ⟨hb.1, hb.2.trans (by norm_num)⟩

theorem manuscriptKernel_averaged_secondMoment_exact {m : ℕ} (hm : 200 ≤ m) :
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) =
      1 - 2 / (m : ℝ)^2 := by
  obtain ⟨hh, hhone, hα, hαhalf⟩ := manuscript_parameters hm
  simpa only [manuscriptKernel, mul_one_div] using
    integral_sq_averaged_circleKernel hh hhone hα hαhalf

theorem manuscriptKernel_averaged_secondMoment_bounds {m : ℕ} (hm : 200 ≤ m) :
    (1 - 2 / (m : ℝ)^2)^2 ≤
      (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) ∧
    (∫ s in (0 : ℝ)..1, (∫ v in (0 : ℝ)..1, manuscriptKernel m s v)^2) ≤
      1 + ((m : ℝ)^(-(3 / 5 : ℝ)))^2 / (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by
  rw [manuscriptKernel_averaged_secondMoment_exact hm]
  have hα := (manuscript_parameters hm).2.2
  have hq0 : 0 ≤ 2 / (m : ℝ)^2 := by positivity
  have hq1 : 2 / (m : ℝ)^2 ≤ 1 := by
    have := hα.2
    rw [div_eq_mul_inv] at this ⊢
    nlinarith
  constructor
  · nlinarith
  · have : 0 ≤ ((m : ℝ)^(-(3 / 5 : ℝ)))^2 /
        (1 - (m : ℝ)^(-(3 / 5 : ℝ)))^2 := by positivity
    linarith

theorem manuscriptKernel_estimates {m : ℕ} (hm : 200 ≤ m) :
    KernelEstimates m (manuscriptKernel m) where
  boundedVariation s := (manuscriptKernel_BV_bound hm s).1
  variation_sharp s := (manuscriptKernel_BV_bound hm s).2.trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  variation_coarse s := (manuscriptKernel_BV_bound_ten hm s).trans
    (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  average_bounds := manuscriptKernel_averaged_bounds hm
  mass := manuscriptKernel_mass hm
  average_square_lower := (manuscriptKernel_averaged_secondMoment_bounds hm).1
  average_square_upper := (manuscriptKernel_averaged_secondMoment_bounds hm).2
  square_mass := manuscriptKernel_secondMoment hm

theorem manuscriptEndpointKernel_estimates {m : ℕ} (hm : 200 ≤ m) :
    KernelEstimates m (manuscriptEndpointKernel m) where
  boundedVariation s := (manuscriptEndpointKernel_BV_bound hm s).1
  variation_sharp s := (manuscriptEndpointKernel_BV_bound hm s).2
  variation_coarse := manuscriptEndpointKernel_BV_bound_ten hm
  average_bounds := manuscriptEndpointKernel_averaged_bounds hm
  mass := manuscriptEndpointKernel_mass hm
  average_square_lower := manuscriptEndpointKernel_averaged_secondMoment_lower_from_mass hm
  average_square_upper := manuscriptEndpointKernel_averaged_secondMoment hm
  square_mass := manuscriptEndpointKernel_secondMoment hm

theorem both_kernel_estimates {m : ℕ} (hm : 200 ≤ m) {u : ℝ → ℝ → ℝ}
    (hu : u = manuscriptKernel m ∨ u = manuscriptEndpointKernel m) :
    KernelEstimates m u := by
  rcases hu with rfl | rfl
  · exact manuscriptKernel_estimates hm
  · exact manuscriptEndpointKernel_estimates hm

end Invariant233.ScalarSampling

end OAI
