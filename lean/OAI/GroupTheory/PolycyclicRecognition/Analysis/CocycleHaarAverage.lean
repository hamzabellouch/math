import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryCocycle
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! # The defect of a Haar-weighted cocycle average

This is the analytic step of controlled Følner averaging. The weight and
its translates are ordinary scalar functions; their difference, rather than
an assumed cohomology conclusion, bounds the averaged affine displacement.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

variable {G E : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}
  (μ : Measure G) [μ.IsMulLeftInvariant]

theorem IsUnitaryCocycle.haar_weighted_average
    (hb : IsUnitaryCocycle ρ b) (f : G → ℝ)
    (hf : Integrable f μ) (hfb : Integrable (fun x => f x • b x) μ)
    (hmass : ∫ x, f x ∂μ = 1) (q : G)
    (hqfb : Integrable (fun x => f (q⁻¹ * x) • b x) μ) :
    b q + ρ q (∫ x, f x • b x ∂μ) - (∫ x, f x • b x ∂μ) =
      ∫ x, (f (q⁻¹ * x) - f x) • b x ∂μ := by
  have hlinear : Integrable (fun x => ρ q (f x • b x)) μ :=
    (ρ q).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hfb
  have hid : ∫ x, f x • b (q * x) ∂μ =
      b q + ρ q (∫ x, f x • b x ∂μ) := by
    simp_rw [hb q, smul_add, ← map_smul]
    rw [integral_add (hf.smul_const (b q)) hlinear, integral_smul_const, hmass, one_smul]
    exact congrArg (fun v => b q + v)
      ((ρ q).toLinearIsometry.integral_comp_comm (fun x => f x • b x))
  have htranslate : ∫ x, f x • b (q * x) ∂μ =
      ∫ x, f (q⁻¹ * x) • b x ∂μ := by
    simpa only [inv_mul_cancel_left] using
      integral_mul_left_eq_self (μ := μ) (fun x => f (q⁻¹ * x) • b x) q
  rw [← hid, htranslate, ← integral_sub hqfb hfb]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (sub_smul _ _ _).symm))

theorem IsUnitaryCocycle.norm_haar_weighted_average_le
    (hb : IsUnitaryCocycle ρ b) (f : G → ℝ)
    (hf : Integrable f μ) (hfb : Integrable (fun x => f x • b x) μ)
    (hmass : ∫ x, f x ∂μ = 1) (q : G)
    (hqfb : Integrable (fun x => f (q⁻¹ * x) • b x) μ)
    (hdf : Integrable (fun x => |f (q⁻¹ * x) - f x|) μ)
    {M : ℝ} (hM : ∀ x, f (q⁻¹ * x) - f x ≠ 0 → ‖b x‖ ≤ M) :
    ‖b q + ρ q (∫ x, f x • b x ∂μ) - (∫ x, f x • b x ∂μ)‖ ≤
      M * ∫ x, |f (q⁻¹ * x) - f x| ∂μ := by
  rw [hb.haar_weighted_average μ f hf hfb hmass q hqfb, ← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae
    (by simpa only [Pi.sub_apply, ← sub_smul] using (hqfb.sub hfb).norm) (hdf.const_mul M)
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  by_cases hx : f (q⁻¹ * x) - f x = 0
  · simp only [hx, zero_smul, norm_zero, abs_zero, mul_zero, le_refl]
  · rw [norm_smul, Real.norm_eq_abs, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg _)

end PolycyclicRecognition

end

end OAI
