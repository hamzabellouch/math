import OAI.Analysis.LipschitzHilbert.Fourier.BoundedConvolutionComposition

namespace OAI

/-! Small and large physical scales of convolution on bounded continuous
functions. The large-scale limit uses only decay along escaping sequences. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem scaledLineConvolution_eq (k f : ℝ → ℂ) (W : ℝ) (hW : 0<W) (y : ℝ) :
    lineConvolution (scaledTimeKernel k W) f y=∫ t, k t*f (y-W*t) := by
  let H := fun t : ℝ => k t*f (y-W*t)
  have he (t : ℝ) : scaledTimeKernel k W t*f (y-t)=(W⁻¹:ℂ)*H (t/W) := by
    unfold H scaledTimeKernel
    rw [mul_div_cancel₀ t hW.ne']
    ring
  simp only [lineConvolution,he]
  rw [integral_const_mul,Measure.integral_comp_div H W,abs_of_pos hW,Complex.real_smul,
    ←mul_assoc]
  have hwc : (W:ℂ)≠0 := by exact_mod_cast hW.ne'
  simp only [inv_mul_cancel₀ hwc,one_mul]
  rfl

theorem scaledLineConvolution_small (k f : ℝ → ℂ) (hk : Integrable k)
    (hfm : Measurable f) (hfc : Continuous f) (B : ℝ) (hf : ∀ y, ‖f y‖≤B)
    (W : ℕ → ℝ) (hW : ∀ n, 0<W n) (hWlim : Tendsto W atTop (𝓝 0)) (y : ℝ) :
    Tendsto (fun n => lineConvolution (scaledTimeKernel k (W n)) f y)
      atTop (𝓝 ((∫ t, k t)*f y)) := by
  simp_rw [scaledLineConvolution_eq k f _ (hW _)]
  have h := tendsto_integral_of_dominated_convergence (fun t => ‖k t‖*B)
    (F:=fun n t => k t*f (y-W n*t)) (f:=fun t => k t*f y)
    (fun n => hk.aestronglyMeasurable.mul (hfm.comp (by fun_prop)).aestronglyMeasurable)
    (hk.norm.mul_const B) (fun n => Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)) (by
      filter_upwards [] with t
      have ht : Tendsto (fun n => y-W n*t) atTop (𝓝 y) := by
        simpa only [zero_mul,sub_zero] using tendsto_const_nhds.sub (hWlim.mul_const t)
      exact (hfc.continuousAt.tendsto.comp ht).const_mul (k t))
  simpa only [integral_mul_const] using h

theorem scaledLineConvolution_large (k f : ℝ → ℂ) (hk : Integrable k)
    (hfm : Measurable f) (B : ℝ) (hf : ∀ y, ‖f y‖≤B)
    (hdecay : ∀ y : ℕ → ℝ, Tendsto (fun n => |y n|) atTop atTop →
      Tendsto (fun n => f (y n)) atTop (𝓝 0))
    (W : ℕ → ℝ) (hW : ∀ n, 0<W n) (hWlim : Tendsto W atTop atTop) (y : ℝ) :
    Tendsto (fun n => lineConvolution (scaledTimeKernel k (W n)) f y) atTop (𝓝 0) := by
  simp_rw [scaledLineConvolution_eq k f _ (hW _)]
  have h := tendsto_integral_of_dominated_convergence (fun t => ‖k t‖*B)
    (F:=fun n t => k t*f (y-W n*t)) (f:=fun _ => (0:ℂ))
    (fun n => hk.aestronglyMeasurable.mul (hfm.comp (by fun_prop)).aestronglyMeasurable)
    (hk.norm.mul_const B) (fun n => Eventually.of_forall fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)) (by
      filter_upwards [volume.ae_ne (0:ℝ)] with t ht
      have hg : Tendsto (fun n => |y-W n*t|) atTop atTop := by
        have hm := hWlim.atTop_mul_const (abs_pos.mpr ht)
        apply tendsto_atTop.mpr
        intro b
        filter_upwards [(tendsto_atTop.mp hm) (b+|y|)] with n hn
        have hh := abs_sub_abs_le_abs_sub (W n*t) y
        rw [abs_mul,abs_of_pos (hW n),abs_sub_comm] at hh
        linarith
      simpa only [mul_zero] using (hdecay (fun n => y-W n*t) hg).const_mul (k t))
  simpa only [integral_zero] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
