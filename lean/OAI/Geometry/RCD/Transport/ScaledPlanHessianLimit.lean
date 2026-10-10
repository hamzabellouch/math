import OAI.Geometry.RCD.Harmonic.UniformLocalL1Pairing

namespace OAI

/-! # Scaled canonical Hessians paired against normalized compressed laws -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MeasurableSpace X]

theorem scaled_plan_hessian_limit (μ : Measure X) (S : ℕ → Set X)
    (r m : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hm : ∀ k, 0 < m k)
    (ν : ℕ → Y → Measure X) {C : ℝ} (hC : 0 ≤ C)
    (hν : ∀ k y, ν k y ≤ ENNReal.ofReal (C/m k) • μ.restrict (S k))
    (J : ∀ k, Y → Lp ℝ 1 (μ.restrict (S k)))
    (hJ : TendstoUniformly (fun k y => (∫ x in S k, |J k y x| ∂μ)/(r k*m k))
      (fun _ => 0) atTop) :
    TendstoUniformly (fun k y => (∫ x, J k y x ∂ν k y)/r k) (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro e he
  have hδ : 0 < e/(C+1) := div_pos he (by positivity)
  filter_upwards [(Metric.tendstoUniformly_iff.mp hJ) (e/(C+1)) hδ] with k hk y
  have hbound := integral_difference_le_of_domination (μ.restrict (S k)) (ν k y)
    ENNReal.ofReal_ne_top (hν k y) (memLp_one_iff_integrable.mp (Lp.memLp (J k y)))
    (integrable_zero X ℝ _)
  simp only [Pi.zero_apply,integral_zero,dist_zero_right,Real.norm_eq_abs,sub_zero,
    ENNReal.toReal_ofReal (div_nonneg hC (hm k).le)] at hbound
  have hsmall : (∫ x in S k, |J k y x| ∂μ)/(r k*m k) < e/(C+1) := by
    have hh := hk y
    simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg
      (div_nonneg (integral_nonneg fun x => abs_nonneg _) (mul_pos (hr k) (hm k)).le)] using hh
  have hb : |(∫ x, J k y x ∂ν k y)/r k| ≤
      C*((∫ x in S k, |J k y x| ∂μ)/(r k*m k)) := by
    rw [abs_div,abs_of_pos (hr k)]
    apply (div_le_div_of_nonneg_right hbound (hr k).le).trans_eq
    field_simp [(hr k).ne',(hm k).ne']
  have hce : C*(e/(C+1)) < e := by
    have heq : e/(C+1)*(C+1)=e := div_mul_cancel₀ e (by positivity)
    nlinarith
  have hfinal := hb.trans_lt ((mul_le_mul_of_nonneg_left hsmall.le hC).trans_lt hce)
  simpa only [dist_zero_left,Real.norm_eq_abs] using hfinal

end RegularPointCoordinates

end

end OAI
