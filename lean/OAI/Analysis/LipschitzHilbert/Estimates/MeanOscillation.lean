import OAI.Analysis.LipschitzHilbert.Estimates.IntervalPoincare

namespace OAI

/-! Local mean oscillation estimates used before John--Nirenberg.
The short part is controlled in mean and the long part by its oscillation.
All constants are independent of the dimension of the range. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def integralAverage (μ : Measure X) (f : X → E) : E :=
  (μ.real univ)⁻¹ • ∫ x, f x ∂μ

theorem norm_average_sub_le (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (hf : Integrable f μ) (hm : 0 < μ.real univ) (c : E) :
    ‖integralAverage μ f - c‖ ≤ (μ.real univ)⁻¹ * ∫ x, ‖f x - c‖ ∂μ := by
  have heq : integralAverage μ f - c = (μ.real univ)⁻¹ • ∫ x, (f x - c) ∂μ := by
    rw [integral_sub hf (integrable_const c), integral_const, smul_sub,
      smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hm.le)

theorem integral_oscillation_le_twice (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (hf : Integrable f μ) (hm : 0 < μ.real univ) (c : E) :
    (∫ x, ‖f x - integralAverage μ f‖ ∂μ) ≤ 2 * ∫ x, ‖f x - c‖ ∂μ := by
  have hpoint (x : X) : ‖f x - integralAverage μ f‖ ≤
      ‖f x - c‖ + ‖integralAverage μ f - c‖ := by
    simpa only [norm_sub_rev] using
      norm_sub_le_norm_sub_add_norm_sub (f x) c (integralAverage μ f)
  calc
    _ ≤ ∫ x, (‖f x - c‖ + ‖integralAverage μ f - c‖) ∂μ :=
      integral_mono (hf.sub (integrable_const _)).norm
        ((hf.sub (integrable_const c)).norm.add (integrable_const _)) hpoint
    _ = (∫ x, ‖f x - c‖ ∂μ) + μ.real univ * ‖integralAverage μ f - c‖ := by
      rw [integral_add (show Integrable (fun x => ‖f x - c‖) μ from
        (hf.sub (integrable_const c)).norm) (integrable_const _),
        integral_const, smul_eq_mul]
    _ ≤ (∫ x, ‖f x - c‖ ∂μ) +
        μ.real univ * ((μ.real univ)⁻¹ * ∫ x, ‖f x - c‖ ∂μ) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (norm_average_sub_le μ f hf hm c) hm.le)
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hm.ne']; ring

omit [CompleteSpace E] in
theorem integralAverage_add (μ : Measure X) (f g : X → E)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    integralAverage μ (fun x => f x + g x) = integralAverage μ f + integralAverage μ g := by
  simp only [integralAverage, integral_add hf hg, smul_add]

theorem short_long_mean_oscillation (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → E) (hf : Integrable f μ) (hg : Integrable g μ)
    (hm : 0 < μ.real univ) {K L : ℝ}
    (hshort : (∫ x, ‖f x‖ ∂μ) ≤ K * μ.real univ)
    (hlong : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖g x - g y‖ ≤ L) :
    (∫ x, ‖f x + g x - integralAverage μ (fun y => f y + g y)‖ ∂μ) ≤
      (2 * K + L) * μ.real univ := by
  have hgpoint : ∀ᵐ x ∂μ, ‖g x - integralAverage μ g‖ ≤ L := by
    filter_upwards [hlong] with x hx
    exact norm_sub_mean_le μ g hg hm (g x) L hx
  have hfmean := integral_oscillation_le_twice μ f hf hm (0 : E)
  simp only [sub_zero] at hfmean
  have hgmean : (∫ x, ‖g x - integralAverage μ g‖ ∂μ) ≤ L * μ.real univ := by
    simpa only [integral_const, smul_eq_mul, mul_comm, Pi.sub_apply] using
      integral_mono_ae (hg.sub (integrable_const _)).norm (integrable_const L) hgpoint
  calc
    _ ≤ ∫ x, (‖f x - integralAverage μ f‖ + ‖g x - integralAverage μ g‖) ∂μ := by
      apply integral_mono
        (show Integrable (fun x => ‖f x + g x - integralAverage μ (fun y => f y + g y)‖) μ from
          ((hf.add hg).sub (integrable_const _)).norm)
        (show Integrable (fun x => ‖f x - integralAverage μ f‖ +
            ‖g x - integralAverage μ g‖) μ from
          (hf.sub (integrable_const _)).norm.add (hg.sub (integrable_const _)).norm)
      intro x
      rw [integralAverage_add μ f g hf hg]
      dsimp only
      rw [add_sub_add_comm]
      exact norm_add_le (f x - integralAverage μ f) (g x - integralAverage μ g)
    _ = (∫ x, ‖f x - integralAverage μ f‖ ∂μ) +
        ∫ x, ‖g x - integralAverage μ g‖ ∂μ := by
      exact integral_add (show Integrable (fun x => ‖f x - integralAverage μ f‖) μ from
        (hf.sub (integrable_const _)).norm)
        (show Integrable (fun x => ‖g x - integralAverage μ g‖) μ from
          (hg.sub (integrable_const _)).norm)
    _ ≤ (2 * K + L) * μ.real univ := by linarith

end LipschitzHilbert

end

end OAI
