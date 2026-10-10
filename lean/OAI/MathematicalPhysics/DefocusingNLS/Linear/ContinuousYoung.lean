import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace OAI

/-! # The continuous-frequency Young estimate used by the homogeneous algebra

Only the nonnegative L¹–L² estimate needed for Fourier magnitudes is proved.
Weighted Cauchy–Schwarz gives the pointwise bound; the existing convolution
Fubini theorem integrates its majorant.
-/

open MeasureTheory
open scoped ENNReal Convolution

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

/-- Weighted Cauchy–Schwarz without introducing a probability normalization. -/
theorem continuousWeightedCauchySchwarz (f g : E → ℝ)
    (hf : Integrable f) (hg : AEStronglyMeasurable g volume)
    (hfp : ∀ x, 0 ≤ f x) (hgp : ∀ x, 0 ≤ g x)
    (hfg : Integrable (fun x => f x * g x ^ 2)) :
    (∫ x, f x * g x) ^ 2 ≤ (∫ x, f x) * ∫ x, f x * g x ^ 2 := by
  let A : E → ℝ := fun x => Real.sqrt (f x)
  let B : E → ℝ := fun x => Real.sqrt (f x) * g x
  have hAm : AEStronglyMeasurable A volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hBm : AEStronglyMeasurable B volume := hAm.mul hg
  have hAs (x : E) : A x ^ 2 = f x := Real.sq_sqrt (hfp x)
  have hBs (x : E) : B x ^ 2 = f x * g x ^ 2 := by
    simp only [B, mul_pow, Real.sq_sqrt (hfp x)]
  have hA : MemLp A 2 volume := (memLp_two_iff_integrable_sq hAm).mpr (by
    simpa only [hAs] using hf)
  have hB : MemLp B 2 volume := (memLp_two_iff_integrable_sq hBm).mpr (by
    simpa only [hBs] using hfg)
  have hAB (x : E) : A x * B x = f x * g x := by
    change Real.sqrt (f x) * (Real.sqrt (f x) * g x) = _
    rw [← mul_assoc, Real.mul_self_sqrt (hfp x)]
  have hholder : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hholder
    (ae_of_all _ (fun x => Real.sqrt_nonneg (f x)))
    (ae_of_all _ (fun x => mul_nonneg (Real.sqrt_nonneg _) (hgp x)))
    (by simpa using hA) (by simpa using hB)
  change (∫ x, A x * B x) ≤ (∫ x, A x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
    (∫ x, B x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) at hh
  simp only [Real.rpow_two, hAB, hAs, hBs, ← Real.sqrt_eq_rpow] at hh
  have hleft : 0 ≤ ∫ x, f x * g x := integral_nonneg (fun x => mul_nonneg (hfp x) (hgp x))
  have h1 : 0 ≤ ∫ x, f x := integral_nonneg hfp
  have h2 : 0 ≤ ∫ x, f x * g x ^ 2 := integral_nonneg (fun x => mul_nonneg (hfp x) (sq_nonneg _))
  have hs := (sq_le_sq₀ hleft (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hh
  simpa only [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2] using hs

noncomputable def positiveFrequencyConvolution (f g : E → ℝ) (ξ : E) : ℝ :=
  ∫ η, f η * g (ξ - η)

theorem positiveFrequencyConvolution_comm (f g : E → ℝ) (ξ : E) :
    positiveFrequencyConvolution f g ξ = positiveFrequencyConvolution g f ξ := by
  unfold positiveFrequencyConvolution
  rw [← integral_sub_left_eq_self (fun η => f η * g (ξ - η)) volume ξ]
  simp only [sub_sub_self, mul_comm]

/-- The exact L¹–L² Young bound, in its squared form. -/
theorem continuousYoung_nonnegative (f g : E → ℝ)
    (hf : Integrable f) (hg : Continuous g)
    (hfp : ∀ x, 0 ≤ f x) (hgp : ∀ x, 0 ≤ g x)
    (hg2 : Integrable (fun x => g x ^ 2))
    (K : ℝ) (_hK : 0 ≤ K) (hgb : ∀ x, g x ≤ K) :
    Integrable (fun ξ => positiveFrequencyConvolution f g ξ ^ 2) ∧
      (∫ ξ, positiveFrequencyConvolution f g ξ ^ 2) ≤
        (∫ ξ, f ξ) ^ 2 * ∫ ξ, g ξ ^ 2 := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hconv : Integrable (fun ξ => ∫ η, f η * g (ξ - η) ^ 2) := by
    exact hf.integrable_convolution L hg2
  have hmajor : Integrable (fun ξ => (∫ x, f x) * ∫ η, f η * g (ξ - η) ^ 2) :=
    hconv.const_mul _
  have hpoint (ξ : E) : positiveFrequencyConvolution f g ξ ^ 2 ≤
      (∫ x, f x) * ∫ η, f η * g (ξ - η) ^ 2 := by
    have hfg : Integrable (fun η => f η * g (ξ - η) ^ 2) := by
      apply (hf.mul_const (K ^ 2)).mono'
        (hf.aestronglyMeasurable.mul ((hg.comp (continuous_const.sub continuous_id)).pow 2).aestronglyMeasurable)
      filter_upwards [] with η
      change ‖f η * g (ξ - η) ^ 2‖ ≤ f η * K ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hfp η) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hgp _) (hgb _) 2) (hfp η)
    exact continuousWeightedCauchySchwarz f (fun η => g (ξ - η)) hf
      (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable hfp
      (fun η => hgp (ξ - η)) hfg
  have hmeas : AEStronglyMeasurable (positiveFrequencyConvolution f g) volume :=
    hf.aestronglyMeasurable.convolution L hg.aestronglyMeasurable
  have hint : Integrable (fun ξ => positiveFrequencyConvolution f g ξ ^ 2) := by
    apply hmajor.mono' (hmeas.pow 2)
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ξ
  refine ⟨hint, (integral_mono hint hmajor hpoint).trans_eq ?_⟩
  rw [integral_const_mul]
  have he := integral_convolution L hf hg2
  change (∫ ξ, ∫ η, f η * g (ξ - η) ^ 2) = (∫ ξ, f ξ) * ∫ ξ, g ξ ^ 2 at he
  rw [he]
  ring

end DefocusingNLS

end OAI
