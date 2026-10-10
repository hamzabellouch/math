import OAI.Analysis.AncientFlat.Kernel.ClassicalBase
import OAI.Analysis.AncientFlat.Kernel.SchwartzIBP

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap ZeroAtInfty
namespace FlatDuality
open BiharmonicKernel ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
def kernelMoment : ℝ := ∫ x : V, ‖x‖*‖heatKernel 1 zero_lt_one x‖
lemma kernelMoment_nonneg : 0≤kernelMoment (V := V) := integral_nonneg (fun point => mul_nonneg (norm_nonneg point) (norm_nonneg _))
lemma kernel_moment_integrable (t : ℝ) (ht : 0<t) : Integrable (fun x : V => ‖x‖*‖kernel t x‖) := by
  rw [←heatKernel_eq_kernel t ht]
  simpa only [pow_one] using (heatKernel (V := V) t ht).integrable_pow_mul volume 1
lemma kernel_moment_scaling (r : ℝ) (hr : 0<r) :
    (∫ x : V, ‖x‖*‖kernel (r^4) x‖)=r*kernelMoment (V := V) := by
  have he (x : V) : kernel (r^4) x=(r^Module.finrank ℝ V)⁻¹ • heatKernel 1 zero_lt_one (r⁻¹ • x) := by
    rw [←heatKernel_eq_kernel _ (by positivity)]
    simpa only [mul_one] using heatKernel_scaling (V := V) 1 zero_lt_one r hr x
  have hf : (fun x : V => ‖x‖*‖kernel (r^4) x‖)=fun x : V =>
      ((r^Module.finrank ℝ V)⁻¹*r)*(‖r⁻¹ • x‖*‖heatKernel 1 zero_lt_one (r⁻¹ • x)‖) := by
    funext x
    rw [he,norm_smul,norm_smul,Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
    field_simp
  rw [hf,integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : V => ‖x‖*‖heatKernel 1 zero_lt_one x‖) hr.le]
  dsimp [kernelMoment]
  field_simp [hr.ne']
lemma norm_kernel_pair_sub_le (r : ℝ) (hr : 0<r) (g : C₀(V,ℂ)) (K : ℝ) (_hK : 0≤K)
    (hg : ∀ x y, ‖g x-g y‖≤K*‖x-y‖) (z : V) :
    ‖(∫ x, kernel (r^4) (x-z)*g x)-g z‖≤K*r*kernelMoment (V := V) := by
  have ht : 0<r^4 := by positivity
  have hk : Integrable (fun x : V => kernel (r^4) (x-z)) := by
    rw [←heatKernel_eq_kernel _ ht]
    exact (heatKernel _ ht).integrable.comp_sub_right z
  have hmass : (∫ x : V, kernel (r^4) (x-z))=1 := by
    rw [integral_sub_right_eq_self,←heatKernel_eq_kernel _ ht,integral_heatKernel]
  have hi : Integrable (fun x => kernel (r^4) (x-z)*g x) :=
    integrable_mul_bounded hk g.continuous ⟨‖g‖,norm_nonneg _,C0Convolution.apply_norm_le g⟩
  have he : (∫ x, kernel (r^4) (x-z)*g x)-g z=∫ x, kernel (r^4) (x-z)*(g x-g z) := by
    calc
      _ = (∫ x, kernel (r^4) (x-z)*g x)-(∫ x, kernel (r^4) (x-z)*g z) := by rw [integral_mul_const,hmass,one_mul]
      _ = _ := by
        rw [←integral_sub hi (hk.mul_const (g z))]
        apply integral_congr_ae
        filter_upwards with x
        ring
  rw [he]
  calc
    _ ≤ ∫ x, K*(‖x-z‖*‖kernel (r^4) (x-z)‖) := by
      apply norm_integral_le_of_norm_le ((kernel_moment_integrable _ ht).comp_sub_right z |>.const_mul K)
      filter_upwards with x
      rw [norm_mul]
      calc
        _ ≤ ‖kernel (r^4) (x-z)‖*(K*‖x-z‖) := mul_le_mul_of_nonneg_left (hg x z) (norm_nonneg _)
        _=_ := by ring
    _ = K*r*kernelMoment (V := V) := by
      rw [integral_const_mul]
      have he' := integral_sub_right_eq_self (μ := volume) (fun x : V => ‖x‖*‖kernel (r^4) x‖) z
      rw [he',kernel_moment_scaling r hr]
      ring
end FlatDuality

end

end OAI
