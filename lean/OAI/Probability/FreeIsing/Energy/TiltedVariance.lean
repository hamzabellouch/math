import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω]

lemma sq_integral_mul_le_integral_sq_of_abs_le_one {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g f : Ω → ℝ} (hg : MemLp g 2 μ) (hf : AEStronglyMeasurable f μ)
    (hfBound : ∀ᵐ w ∂μ, |f w| ≤ 1) :
    (∫ w, g w * f w ∂μ) ^ 2 ≤ ∫ w, g w ^ 2 ∂μ := by
  have hgi := hg.integrable one_le_two
  have hfNorm : ∀ᵐ w ∂μ, ‖f w‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hfBound
  have hprod := hgi.mul_bdd hf hfNorm
  have habs : |∫ w, g w * f w ∂μ| ≤ ∫ w, |g w| ∂μ := by
    calc
      |∫ w, g w * f w ∂μ| ≤ ∫ w, |g w * f w| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ w, |g w| ∂μ := by
        apply integral_mono_ae hprod.abs hgi.abs
        filter_upwards [hfBound] with w hw
        rw [abs_mul]
        simpa using mul_le_mul_of_nonneg_left hw (abs_nonneg (g w))
  have hvar := variance_nonneg (fun w => |g w|) μ
  have hgAbs : MemLp (fun w => |g w|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hg.norm
  rw [variance_eq_sub hgAbs] at hvar
  simp only [Pi.pow_apply, sq_abs] at hvar
  have hn : 0 ≤ ∫ w, |g w| ∂μ := integral_nonneg fun w => abs_nonneg _
  have hs := (sq_le_sq₀ (abs_nonneg _) hn).mpr habs
  rw [sq_abs] at hs
  linarith

lemma variance_ge_of_binary_tilt_moments {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g f : Ω → ℝ} {theta : ℝ}
    (hg : MemLp g 2 μ) (hgTilt : MemLp g 2 ν)
    (hf : AEStronglyMeasurable f μ) (hfBound : ∀ᵐ w ∂μ, |f w| ≤ 1)
    (hFirst : (∫ w, g w ∂ν) = theta * ∫ w, g w * f w ∂μ)
    (hSecond : (∫ w, g w ^ 2 ∂ν) = ∫ w, g w ^ 2 ∂μ) :
    (1 - theta ^ 2) * (∫ w, g w ^ 2 ∂μ) ≤ variance g ν := by
  have hcs := sq_integral_mul_le_integral_sq_of_abs_le_one hg hf hfBound
  have hmul := mul_le_mul_of_nonneg_left hcs (sq_nonneg theta)
  rw [variance_eq_sub hgTilt]
  change (1 - theta ^ 2) * (∫ w, g w ^ 2 ∂μ) ≤
    (∫ w, g w ^ 2 ∂ν) - (∫ w, g w ∂ν) ^ 2
  rw [hFirst, hSecond]
  nlinarith

end Problem367

end

end OAI
