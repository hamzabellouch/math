import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BoundedDerivatives

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section LogDerivatives
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_log (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hn : ∀ x, f x ≠ 0) (x : E) :
    fderiv ℝ (fderiv ℝ (fun x => Real.log (f x))) x =
      (f x)⁻¹ • fderiv ℝ (fderiv ℝ f) x +
      (-(f x ^ 2)⁻¹ • fderiv ℝ f x).smulRight (fderiv ℝ f x) := by
  have hd := hf.differentiable (by norm_num)
  have he : fderiv ℝ (fun x => Real.log (f x)) = fun x => (f x)⁻¹ • fderiv ℝ f x := by
    funext x
    exact ((hd x).hasFDerivAt.log (hn x)).fderiv
  rw [he]
  exact (((hasDerivAt_inv (hn x)).comp_hasFDerivAt x (hd x).hasFDerivAt).smul
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem log_boundedDerivs_of_relative_bounds (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hp : ∀ x, 0 < f x) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C * f x)
    (hbb : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D * f x) :
    BoundedDerivs (fun x => Real.log (f x)) := by
  have hd := hf.differentiable (by norm_num)
  refine ⟨hf.log (fun x => (hp x).ne'), C, D+C*C, hC, by positivity, ?_, ?_⟩
  · intro x
    rw [((hd x).hasFDerivAt.log (hp x).ne').fderiv, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hp x))]
    calc
      _ ≤ (f x)⁻¹ * (C * f x) := mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr (hp x).le)
      _ = C := by field_simp [(hp x).ne']
  · intro x
    have hfx := (hp x).le
    rw [fderiv_fderiv_log f hf (fun x => (hp x).ne') x]
    calc
      _ ≤ ‖(f x)⁻¹ • fderiv ℝ (fderiv ℝ f) x‖+
        ‖(-(f x ^ 2)⁻¹ • fderiv ℝ f x).smulRight (fderiv ℝ f x)‖ :=
          ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ ‖(f x)⁻¹‖*‖fderiv ℝ (fderiv ℝ f) x‖+
          (‖-(f x ^ 2)⁻¹‖*‖fderiv ℝ f x‖)*‖fderiv ℝ f x‖ := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        gcongr <;> exact ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖(f x)⁻¹‖*(D*f x)+(‖-(f x ^ 2)⁻¹‖*(C*f x))*(C*f x) := by
        gcongr <;> first | positivity | exact hb _ | exact hbb _
      _ = D+C*C := by
        rw [norm_inv, Real.norm_eq_abs, abs_of_pos (hp x), norm_neg, norm_inv, norm_pow,
          Real.norm_eq_abs, abs_of_pos (hp x)]
        field_simp [(hp x).ne']

theorem norm_fderiv_fderiv_exp_le (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C)
    (hbb : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ D) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun x => Real.exp (f x))) x‖ ≤
      (D+C*C)*Real.exp (f x) := by
  rw [fderiv_fderiv_exp f hf x]
  calc
    _ ≤ ‖Real.exp (f x) • fderiv ℝ (fderiv ℝ f) x‖+
        ‖(Real.exp (f x) • fderiv ℝ f x).smulRight (fderiv ℝ f x)‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ ‖Real.exp (f x)‖*‖fderiv ℝ (fderiv ℝ f) x‖+
        (‖Real.exp (f x)‖*‖fderiv ℝ f x‖)*‖fderiv ℝ f x‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      gcongr <;> exact ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖Real.exp (f x)‖*D+(‖Real.exp (f x)‖*C)*C := by gcongr <;> first | exact hb _ | exact hbb _
    _ = _ := by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; ring

end LogDerivatives
end SK.Analytic

end
end
end
end
end
end

end OAI
