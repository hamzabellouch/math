import OAI.Analysis.BernoulliCone.HalfspaceEnergy

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal
namespace Bernoulli.Shape
variable {d : ℕ}

lemma derivative_norm_le {u : Space d → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) (x y : Space d) : ‖fderiv ℝ u x y‖ ≤ L*‖y‖ :=
  (fderiv ℝ u x).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg y))

lemma density_le {u : Space d → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (x : Space d) :
    density u x ≤ (L:ℝ)^2+1 := by
  have hn := LipschitzSobolev.norm_gradient_le hu x
  unfold density
  split_ifs <;> nlinarith [norm_nonneg (gradient u x)]

lemma density_measurable {u : Space d → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) :
    Measurable (density u) := by
  have hp : Measurable (fun x : Space d => if 0 < u x then (1:ℝ) else 0) :=
    measurable_const.ite (isOpen_lt continuous_const hu.continuous).measurableSet measurable_const
  exact (LipschitzSobolev.measurable_gradient.norm.pow_const 2).add hp

lemma stressTerm_measurable {u : Space d → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (φ : Space d → ℝ) (e : Space d) : Measurable (stressTerm u φ e) := by
  have hφ : Measurable (fun x : Space d => fderiv ℝ φ x e) := measurable_fderiv_apply_const ℝ φ e
  have hue : Measurable (fun x : Space d => fderiv ℝ u x e) := measurable_fderiv_apply_const ℝ u e
  have hub : Measurable (fun x : Space d => fderiv ℝ u x (gradient φ x)) := by
    simp_rw [← inner_gradient_left]
    exact LipschitzSobolev.measurable_gradient.inner LipschitzSobolev.measurable_gradient
  exact ((density_measurable hu).mul hφ).sub ((measurable_const.mul hue).mul hub)

lemma stressTerm_norm_le {u φ : Space d → ℝ} {L C : ℝ≥0}
    (hu : LipschitzWith L u) (hφ : LipschitzWith C φ) (e x : Space d) :
    ‖stressTerm u φ e x‖ ≤ ((L:ℝ)^2+1)*C*‖e‖ + 2*(L:ℝ)^2*‖e‖*C := by
  have hud := derivative_norm_le hu x e
  have hφd := derivative_norm_le hφ x e
  have hub : ‖fderiv ℝ u x (gradient φ x)‖ ≤ (L:ℝ)*C :=
    (derivative_norm_le hu x _).trans
      (mul_le_mul_of_nonneg_left (LipschitzSobolev.norm_gradient_le hφ x) L.coe_nonneg)
  have hden : ‖density u x‖ ≤ (L:ℝ)^2+1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (density_nonneg u x)]
    exact density_le hu x
  have h1 := mul_le_mul hden hφd (norm_nonneg _) (by positivity : 0 ≤ (L:ℝ)^2+1)
  have h2 := mul_le_mul (mul_le_mul_of_nonneg_left hud (show (0:ℝ) ≤ 2 by norm_num)) hub
    (norm_nonneg _) (by positivity : 0 ≤ 2*((L:ℝ)*‖e‖))
  unfold stressTerm
  calc
    _ ≤ ‖density u x * fderiv ℝ φ x e‖ + ‖2*fderiv ℝ u x e*fderiv ℝ u x (gradient φ x)‖ := norm_sub_le _ _
    _ ≤ ((L:ℝ)^2+1)*(C*‖e‖)+(2*((L:ℝ)*‖e‖))*((L:ℝ)*C) := by
      simp only [norm_mul,Real.norm_ofNat]
      exact add_le_add h1 h2
    _ = _ := by ring

lemma stressTerm_integrable_ball {u φ : Space d → ℝ} {L C : ℝ≥0}
    (hu : LipschitzWith L u) (hφ : LipschitzWith C φ) (e a : Space d) (R : ℝ) :
    IntegrableOn (stressTerm u φ e) (ball a R) := by
  let : IsFiniteMeasure (volume.restrict (ball a R)) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply (integrable_const (((L:ℝ)^2+1)*C*‖e‖ + 2*(L:ℝ)^2*‖e‖*C)).mono'
    (stressTerm_measurable hu φ e).aestronglyMeasurable
  exact Eventually.of_forall (stressTerm_norm_le hu hφ e)
end Bernoulli.Shape

end
end

end OAI
