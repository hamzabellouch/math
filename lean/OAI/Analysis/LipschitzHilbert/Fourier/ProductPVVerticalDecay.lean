import OAI.Analysis.LipschitzHilbert.Estimates.ProductPVContinuity

namespace OAI

/-! Along every vertical sequence escaping to infinity the actual short
principal value tends to zero. Only boundedness of the direction is used. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem bounded_sample_tendsto_cocompact (u : (ℝ×ℝ) → ℝ)
    (hub : ∀ z, |u z|≤1) (x t : ℝ) (y : ℕ → ℝ)
    (hy : Tendsto (fun n => |y n|) atTop atTop) :
    Tendsto (fun n => productSlopeSample u t (x,y n)) atTop (cocompact (ℝ×ℝ)) := by
  apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0,0)
  have hnorm : ∀ n, |y n|-|t|≤‖productSlopeSample u t (x,y n)‖ := by
    intro n
    have hmul : |t*u (x,y n)|≤|t| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg t) (hub _)
    have hs := abs_sub_abs_le_abs_sub (y n) (t*u (x,y n))
    have hm : |y n-t*u (x,y n)|≤‖productSlopeSample u t (x,y n)‖ := by
      change ‖y n-t*u (x,y n)‖≤max ‖x-t‖ ‖y n-t*u (x,y n)‖
      exact le_max_right _ _
    linarith
  have ht : Tendsto (fun n => ‖productSlopeSample u t (x,y n)‖) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_atTop.mp hy) (b+|t|)] with n hn
    linarith [hnorm n]
  change Tendsto (fun n => ‖productSlopeSample u t (x,y n)-(0:ℝ×ℝ)‖) atTop atTop
  simpa only [sub_zero] using ht

theorem productPV_vertical_decay (u : (ℝ×ℝ) → ℝ) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0≤R) (x : ℝ)
    (y : ℕ → ℝ) (hy : Tendsto (fun n => |y n|) atTop atTop) :
    Tendsto (fun n => productSlopePrincipalValue u R f (x,y n)) atTop (𝓝 0) := by
  simp_rw [productPV_eq_integral u f R hR]
  have h := tendsto_integral_of_dominated_convergence
    (μ:=volume.restrict (Set.Ioc 0 R)) (fun _ => 2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ))
    (F:=fun n t => productPVIntegrand u f (x,y n) t) (f:=fun _ => (0:ℂ))
    (fun n => by
      apply Measurable.aestronglyMeasurable
      unfold productPVIntegrand productSlopeSample
      fun_prop)
    (integrable_const _) (fun n => Eventually.of_forall
      (productPVIntegrand_bound u hub f (x,y n))) (by
      filter_upwards [] with t
      have hp := f.tendsto_cocompact.comp (bounded_sample_tendsto_cocompact u hub x t y hy)
      have hn := f.tendsto_cocompact.comp (bounded_sample_tendsto_cocompact u hub x (-t) y hy)
      simpa only [productPVIntegrand,sub_zero,smul_zero,Function.comp_def] using (hp.sub hn).const_smul t⁻¹)
  simpa only [integral_zero] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
