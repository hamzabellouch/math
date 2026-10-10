import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerDerivative
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! Uniform convergence of the exact dimension-twelve weighted primitives. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_weighted_integral_uniform (R : ℝ) (hR : 0 ≤ R)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ n, ContinuousOn (f n) (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R))
    (hT : TendstoUniformlyOn f g atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun n r => ∫ t in (0 : ℝ)..r, f n t*t^11)
      (fun r => ∫ t in (0 : ℝ)..r, g t*t^11) atTop (Icc 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε/(R^12+1)
  have hC : 0 < R^12+1 := by positivity
  have hδ : 0 < δ := div_pos hε hC
  have hδC : δ*(R^12+1)=ε := div_mul_cancel₀ _ hC.ne'
  have hevent := (Metric.tendstoUniformlyOn_iff.mp hT) δ hδ
  filter_upwards [hevent] with n hn r hr
  have hnf : IntervalIntegrable (fun t => f n t*t^11) volume 0 r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1
      (((hf n).mul (continuous_id.pow 11).continuousOn).mono
        (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
  have hgf : IntervalIntegrable (fun t => g t*t^11) volume 0 r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1
      ((hg.mul (continuous_id.pow 11).continuousOn).mono
        (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
  have heq : (∫ t in (0 : ℝ)..r, f n t*t^11)-(∫ t in (0 : ℝ)..r, g t*t^11)=
      ∫ t in (0 : ℝ)..r, (f n t-g t)*t^11 := by
    rw [← intervalIntegral.integral_sub hnf hgf]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hb : ‖∫ t in (0 : ℝ)..r, (f n t-g t)*t^11‖ ≤ δ*R^11*r := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := r)
      (C := δ*R^11) (f := fun t => (f n t-g t)*t^11) (fun t ht => by
      have htI : t ∈ Icc 0 r := ⟨(uIoc_of_le hr.1 ▸ ht).1.le,(uIoc_of_le hr.1 ▸ ht).2⟩
      have htR : t ∈ Icc 0 R := ⟨htI.1,htI.2.trans hr.2⟩
      have hdiff : ‖f n t-g t‖ ≤ δ := by
        have hh := (hn t htR).le
        rwa [dist_comm,dist_eq_norm] at hh
      rw [norm_mul,Real.norm_eq_abs (t^11),abs_of_nonneg (pow_nonneg htI.1 _)]
      exact mul_le_mul hdiff (pow_le_pow_left₀ htI.1 htR.2 11) (pow_nonneg htI.1 _) hδ.le)
    simpa only [sub_zero,abs_of_nonneg hr.1] using hh
  rw [dist_comm,dist_eq_norm,heq]
  have hprod := mul_le_mul_of_nonneg_left hr.2 (show 0 ≤ δ*R^11 by positivity)
  have hpower : δ*R^11*R=δ*R^12 := by ring
  rw [hpower] at hprod
  nlinarith

end DefocusingNLS

end OAI
