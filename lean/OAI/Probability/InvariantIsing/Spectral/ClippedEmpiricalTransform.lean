import OAI.Probability.InvariantIsing.Spectral.CompactSpectralClipping
import OAI.Probability.InvariantIsing.Spectral.ResolventLipschitz
import OAI.Probability.InvariantIsing.Spectral.SpectralExcess

namespace OAI

/-! Uniform resolvent error for the actual finite empirical spectral clipping. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace InvariantIsing

theorem empirical_transform_clip_error {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    {R η t : ℝ} (ht : 0 < t)
    (hclip : ∀ i, |spectralClip 0 R (eig i)-eig i| ≤ η) :
    |(∫ x, positiveResolventTest t (spectralClip 0 R x)
      ∂(empiricalSpectralLaw hN eig : Measure ℝ))-
      ∫ x, positiveResolventTest t x ∂(empiricalSpectralLaw hN eig : Measure ℝ)| ≤ η/t^2 := by
  let μ := (empiricalSpectralLaw hN eig : Measure ℝ)
  have hc : Integrable (fun x => positiveResolventTest t (spectralClip 0 R x)) μ := by
    apply Integrable.of_bound
      ((continuous_positiveResolventTest ht).comp (continuous_spectralClip 0 R)).aestronglyMeasurable (1/t)
    exact ae_of_all _ fun x => by
      change ‖positiveResolventTest t (spectralClip 0 R x)‖ ≤ 1/t
      rw [Real.norm_eq_abs,abs_of_nonneg (positiveResolventTest_bound ht _).1]
      exact (positiveResolventTest_bound ht _).2
  have hi : Integrable (positiveResolventTest t) μ := by
    simpa only [pow_one] using positiveResolventPower_integrable ht 1 μ
  rw [← integral_sub hc hi,← Real.norm_eq_abs]
  have ha : ∀ᵐ x ∂μ, |spectralClip 0 R x-x| ≤ η := ae_finiteSpectralMeasure
    (fun _ => (1 : ℝ)/N) eig hclip
  have hb : ∀ᵐ x ∂μ, ‖positiveResolventTest t (spectralClip 0 R x)-positiveResolventTest t x‖ ≤ η/t^2 := by
    filter_upwards [ha] with x hx
    rw [Real.norm_eq_abs]
    exact (positiveResolventTest_sub_le ht _ _).trans
      (div_le_div_of_nonneg_right hx (sq_nonneg t))
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

theorem empirical_transform_clip_excess {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ)
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t) :
    |(∫ x, positiveResolventTest t (spectralClip 0 R x)
      ∂(empiricalSpectralLaw hN eig : Measure ℝ))-
      ∫ x, positiveResolventTest t x ∂(empiricalSpectralLaw hN eig : Measure ℝ)| ≤
        spectralExcess eig 0 R/t^2 := by
  apply empirical_transform_clip_error hN eig ht
  intro i
  exact spectralClip_close hR (spectralExcess_nonneg _ _ _) (spectralExcess_bounds eig 0 R i)

end InvariantIsing

end

end OAI
