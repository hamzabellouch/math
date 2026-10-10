import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.BoundedMassLimit

namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace TamingCompatibility
variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] {μ : Measure Ω}

lemma integral_norm_mul_tendsto_of_schur
    (q : Ω → V) (hq : MemLp q 2 μ)
    (H : ℝ → Ω → ℝ) (hH : ∀ r, 0 < r → Integrable (H r) μ)
    (hH0 : ∀ r x, 0 ≤ H r x) (C D : ℝ) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hbound : ∀ r, 0 < r → ∀ x, r*H r x ≤ C)
    (hmass : ∀ r, 0 < r → (∫ x, H r x ∂μ) ≤ D*r) :
    Tendsto (fun r : ℝ => ∫ x, ‖q x‖*H r x ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  classical
  let F := fun (r : ℝ) (x : Ω) => if 0 < r then r*H r x else 0
  have hFi (r : ℝ) : Integrable (F r) μ := by
    by_cases hr : 0 < r
    · simpa only [F,ite_eq_left hr] using (hH r hr).const_mul r
    · simp only [F,ite_eq_right hr]; exact integrable_zero _ _ _
  have hFp (r : ℝ) (x : Ω) : 0 ≤ F r x ∧ F r x ≤ C := by
    by_cases hr : 0 < r
    · simp only [F,ite_eq_left hr]
      exact ⟨mul_nonneg hr.le (hH0 r x),hbound r hr x⟩
    · simp only [F,ite_eq_right hr]
      exact ⟨le_rfl,hC⟩
  have hFl : Tendsto (fun r => ∫ x, F r x ∂μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun r => integral_nonneg fun x => (hFp r x).1)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r at hr
      simp only [F,ite_eq_left hr,integral_const_mul]
      exact (mul_le_mul_of_nonneg_left (hmass r hr) hr.le).trans_eq (by ring : r*(D*r) = D*r^2)
    · have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
      simpa only [zero_pow (by decide : 2 ≠ 0),mul_zero] using (tendsto_const_nhds (x := D)).mul (hid.pow 2)
  have hq2 : Integrable (fun x => ‖q x‖^2) μ := hq.norm.integrable_sq
  have hweighted := integral_weight_mul_tendsto_zero_of_bounded_mass F hFi C
    (fun r => ae_of_all _ (hFp r)) hFl (fun x => ‖q x‖^2) hq2
  have hlim : Tendsto (fun r => Real.sqrt (∫ x, ‖q x‖^2*F r x ∂μ)*Real.sqrt D)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero,zero_mul,Function.comp_def] using
      (Real.continuous_sqrt.tendsto 0 |>.comp hweighted).mul tendsto_const_nhds
  apply squeeze_zero' (Eventually.of_forall fun r => integral_nonneg fun x => mul_nonneg (norm_nonneg _) (hH0 r x))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    change 0 < r at hr
    have hfi : Integrable (fun x => ‖q x‖^2*(r*H r x)) μ := by
      apply (hq2.mul_const C).mono' (hq2.aestronglyMeasurable.mul ((hH r hr).aestronglyMeasurable.const_mul r))
      apply ae_of_all
      intro x
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hr.le (hH0 r x)))]
      exact mul_le_mul_of_nonneg_left (hbound r hr x) (sq_nonneg _)
    have hgi : Integrable (fun x => H r x/r) μ := (hH r hr).div_const r
    have hfpos (x : Ω) : 0 ≤ ‖q x‖^2*(r*H r x) := mul_nonneg (sq_nonneg _) (mul_nonneg hr.le (hH0 r x))
    have hgpos (x : Ω) : 0 ≤ H r x/r := div_nonneg (hH0 r x) hr.le
    have he (x : Ω) : ‖q x‖*H r x =
        Real.sqrt (‖q x‖^2*(r*H r x))*Real.sqrt (H r x/r) := by
      rw [← Real.sqrt_mul (hfpos x)]
      have ha : ‖q x‖^2*(r*H r x)*(H r x/r) = (‖q x‖*H r x)^2 := by field_simp [hr.ne']
      rw [ha,Real.sqrt_sq (mul_nonneg (norm_nonneg _) (hH0 r x))]
    calc
      _ = ∫ x, Real.sqrt (‖q x‖^2*(r*H r x))*Real.sqrt (H r x/r) ∂μ := integral_congr_ae (ae_of_all _ he)
      _ ≤ Real.sqrt (∫ x, ‖q x‖^2*(r*H r x) ∂μ)*Real.sqrt (∫ x, H r x/r ∂μ) :=
        integral_sqrt_mul_sqrt_le _ _ hfi hgi hfpos hgpos
      _ ≤ Real.sqrt (∫ x, ‖q x‖^2*F r x ∂μ)*Real.sqrt D := by
        simp only [F,ite_eq_left hr]
        apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (Real.sqrt_nonneg _)
        rw [integral_div]
        exact (div_le_iff₀ hr).mpr (hmass r hr)
  · exact hlim
end TamingCompatibility

end
end

end OAI
