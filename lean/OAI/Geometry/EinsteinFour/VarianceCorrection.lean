import OAI.Geometry.EinsteinFour.Variance
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! The variance correction in equation (17). Equal second moments
remove the mean of the difference with the exact deficit weight. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter

noncomputable section

variable {Ω : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem variance_correction_nonneg (v b F : Ω → ℝ)
    (hv : Continuous v) (hb : Continuous b) (hF : Integrable F μ)
    (hsecond : (∫ x, v x ^ 2 ∂μ) = ∫ x, b x ^ 2 ∂μ)
    (hvariance : (∫ x, (v x - b x) ^ 2 ∂μ) - (∫ x, v x - b x ∂μ) ^ 2 ≤
      ∫ x, F x ∂μ) :
    0 ≤ ∫ x, F x - (1 - (2 - v x - b x) ^ 2 / 4) * (v x - b x) ^ 2 ∂μ := by
  let d : Ω → ℝ := fun x => v x - b x
  let w : Ω → ℝ := fun x => (2 - v x - b x) * d x
  have hd : Continuous d := hv.sub hb
  have hw : Continuous w := ((continuous_const.sub hv).sub hb).mul hd
  have intg {f : Ω → ℝ} (h : Continuous f) : Integrable f μ :=
    h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (x : Ω) : w x = 2 * d x - (v x ^ 2 - b x ^ 2) := by
    dsimp [w, d]
    ring
  have hv2i : Integrable (fun x => v x ^ 2) μ := intg (hv.pow 2)
  have hb2i : Integrable (fun x => b x ^ 2) μ := intg (hb.pow 2)
  have hd2i : Integrable (fun x => d x ^ 2) μ := intg (hd.pow 2)
  have hw2i : Integrable (fun x => w x ^ 2) μ := intg (hw.pow 2)
  have hmean : (∫ x, w x ∂μ) = 2 * ∫ x, d x ∂μ := by
    have hs1 := integral_sub ((intg hd).const_mul 2) (hv2i.sub hb2i)
    have hs2 := integral_sub hv2i hb2i
    simp only [Pi.sub_apply] at hs1 hs2
    rw [integral_congr_ae (Eventually.of_forall heq),
      hs1, integral_const_mul, hs2, hsecond]
    ring
  have hcs := integral_pairing_sq_le (integrable_const (1 : ℝ))
    hw2i (intg hw) (Eventually.of_forall (fun _ => zero_le_one))
    (Eventually.of_forall (fun x => sq_nonneg (w x)))
    (Eventually.of_forall (fun x => le_of_eq (one_mul (w x ^ 2)).symm))
  have hcs' : (2 * ∫ x, d x ∂μ) ^ 2 ≤ ∫ x, w x ^ 2 ∂μ := by
    simpa only [hmean, integral_const, probReal_univ, smul_eq_mul, one_mul] using hcs
  have hpoly (x : Ω) :
      (1 - (2 - v x - b x) ^ 2 / 4) * (v x - b x) ^ 2 = d x ^ 2 - w x ^ 2 / 4 := by
    dsimp [d, w]
    ring
  have hp : Integrable (fun x => (1 - (2 - v x - b x) ^ 2 / 4) * (v x - b x) ^ 2) μ := by
    apply intg
    fun_prop
  have hs := integral_sub hd2i (hw2i.div_const 4)
  rw [integral_sub hF hp, integral_congr_ae (Eventually.of_forall hpoly),
    hs, integral_div]
  change 0 ≤ (∫ x, F x ∂μ) - ((∫ x, d x ^ 2 ∂μ) - (∫ x, w x ^ 2 ∂μ) / 4)
  change (∫ x, d x ^ 2 ∂μ) - (∫ x, d x ∂μ) ^ 2 ≤ ∫ x, F x ∂μ at hvariance
  nlinarith only [hcs', hvariance]

end
end PositiveEinsteinFour.Variance

end OAI
