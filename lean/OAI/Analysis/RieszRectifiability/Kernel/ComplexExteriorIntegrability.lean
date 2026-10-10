import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ComplexHeightPairing
import OAI.Analysis.RieszRectifiability.Kernel.KernelTestSupport

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter

theorem complexRenormalizedNormalIntegrand_norm {d : ℕ} (m : ℕ)
    (w : Ambient d → ℝ) (g : Ambient d → ℂ) (a : Ambient d) (q : Ambient d × Ambient d) :
    ‖complexRenormalizedNormalIntegrand m w g a q‖ =
      |renormalizedNormalIntegrand m w (fun x => ‖g x‖) a q| := by
  unfold complexRenormalizedNormalIntegrand renormalizedNormalIntegrand
  rw [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal, abs_mul,
    abs_of_nonneg (norm_nonneg (g q.1))]
  ring

theorem complex_renormalized_exterior_integrable {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hgrowth : GlobalUpperGrowth m C μ) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hw : Measurable w) (hgm : Measurable g) (hgn : Integrable (fun x => ‖g x‖) ν)
    (hgnw : Integrable (fun x => ‖g x‖ * w x) ν)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, g x ≠ 0 → dist x a ≤ H)
    (hweighted : IntegrableOn (fun y => |w y| * inverseDistancePow (m + 2) a y)
      (closedExterior a R) μ) :
    Integrable (complexRenormalizedNormalIntegrand m w g a)
      (ν.prod (μ.restrict (closedExterior a R))) := by
  have hnormnear : ∀ᵐ x ∂ν, ‖g x‖ ≠ 0 → dist x a ≤ H := by
    filter_upwards [hnear] with x hx
    exact fun hgx => hx (norm_ne_zero_iff.mp hgx)
  have hi := (renormalized_far_pairing_integrable_and_bound m C μ ν hgrowth w
    (fun x => ‖g x‖) hw hgm.norm hgn hgnw a H R hH hR hHR hnormnear hweighted
    (∫ y in closedExterior a R, |w y| * inverseDistancePow (m + 2) a y ∂μ) le_rfl).1
  have hm : Measurable (complexRenormalizedNormalIntegrand m w g a) := by
    unfold complexRenormalizedNormalIntegrand inverseDistancePow
    simp_rw [Complex.real_smul]
    fun_prop
  apply hi.abs.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun q => (complexRenormalizedNormalIntegrand_norm m w g a q).le

theorem direct_height_exterior_integrable {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hgrowth : GlobalUpperGrowth m C μ) (w : Ambient d → ℝ) (g : Ambient d → ℂ)
    (hw : Measurable w) (hgm : Measurable g)
    (hgnw : Integrable (fun x => ‖g x‖ * w x) ν)
    (a : Ambient d) (H R : ℝ) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hnear : ∀ᵐ x ∂ν, g x ≠ 0 → dist x a ≤ H) :
    Integrable (fun q : Ambient d × Ambient d =>
      w q.1 • (inverseDistancePow (m + 1) q.1 q.2 • g q.1))
      (ν.prod (μ.restrict (closedExterior a R))) := by
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound m C μ hgrowth a R hR).1
  have hdom := (hgnw.abs.mul_prod hk).const_mul ((2 : ℝ) ^ (m + 1))
  have hm : Measurable (fun q : Ambient d × Ambient d =>
      w q.1 • (inverseDistancePow (m + 1) q.1 q.2 • g q.1)) := by
    unfold inverseDistancePow
    simp_rw [Complex.real_smul]
    fun_prop
  apply hdom.mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnear,
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (closedExterior_measurable a R))] with q hx hy
  by_cases hgx : g q.1 = 0
  · rw [hgx]
    simp
  · have hy' : R ≤ dist a q.2 := hy
    have hfar : 2 * dist q.1 a ≤ dist a q.2 := by linarith [hx hgx]
    have hbound := inverseDistancePow_far_le (m + 1) a q.1 q.2 (hR.trans_le hy) hfar
    simp only [RCLike.real_smul_eq_coe_mul, norm_mul, RCLike.norm_ofReal,
      abs_of_nonneg (inverseDistancePow_nonneg _ _ _), abs_mul, abs_norm]
    calc
      _ ≤ |w q.1| * ((2 ^ (m + 1) * inverseDistancePow (m + 1) a q.2) * ‖g q.1‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)) (abs_nonneg _)
      _ = _ := by ring

end

end RieszRectifiability

end OAI
