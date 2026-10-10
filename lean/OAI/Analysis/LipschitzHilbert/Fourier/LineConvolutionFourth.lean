import OAI.Analysis.LipschitzHilbert.Fourier.LineProjectionKernel

namespace OAI

/-! The fourth-power Young bound for an integrable line kernel and a
Schwartz input, with its exact L1 kernel constant. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_fourth_joint_integrable (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) (volume.prod volume) := by
  have hm : Measurable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((lineTranslation_measurePreserving t).integrable_comp_of_integrable
        ((f.memLp 4 volume).integrable_norm_pow (by decide))).const_mul ‖K t‖
  · have heq (t : ℝ) : (∫ z, ‖‖K t‖*‖f (z-t)‖^4‖)=‖K t‖*(∫ z, ‖f z‖^4) := by
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K t)),
        norm_pow,norm_norm]
      rw [integral_const_mul,integral_sub_right_eq_self (fun z => ‖f z‖^4) t]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem lineConvolution_fourth_pointwise (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖lineConvolution K f x‖^4≤(∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := by
  have hi (n : ℕ) : Integrable (fun t => ‖K t‖*‖f (x-t)‖^n) := by
    apply (hK.norm.mul_const ((SchwartzMap.seminorm ℝ 0 0 f)^n)).mono'
      (by fun_prop)
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (by positivity : 0≤‖K t‖*‖f (x-t)‖^n)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (SchwartzMap.norm_le_seminorm ℝ f (x-t)) n)
      (norm_nonneg _)
  have hfirst := lineConvolution_pointwise_energy K hK hKm f f.continuous.measurable x (hi 2)
  have hfourth : Integrable (fun t => ‖K t‖*(‖f (x-t)‖^2)^2) := by
    simpa only [←pow_mul] using hi 4
  have hsecond := (weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖f (x-t)‖^2) hKm.norm (by fun_prop) (fun _ => norm_nonneg _)
    (fun _ => sq_nonneg _) hK.norm hfourth).2
  have hs := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  calc
    ‖lineConvolution K f x‖^4 = (‖lineConvolution K f x‖^2)^2 := by ring
    _ ≤ ((∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (x-t)‖^2))^2 := hs
    _ = (∫ t, ‖K t‖)^2*(∫ t, ‖K t‖*‖f (x-t)‖^2)^2 := mul_pow _ _ _
    _ ≤ (∫ t, ‖K t‖)^2*((∫ t, ‖K t‖)*(∫ t, ‖K t‖*(‖f (x-t)‖^2)^2)) :=
      mul_le_mul_of_nonneg_left hsecond (sq_nonneg _)
    _ = _ := by simp only [←pow_mul]; ring

theorem lineConvolution_fourth_bound (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ‖lineConvolution K f x‖^4) ∧
      (∫ x, ‖lineConvolution K f x‖^4)≤(∫ t, ‖K t‖)^4*(∫ x, ‖f x‖^4) := by
  have hj := lineConvolution_fourth_joint_integrable K hK hKm f
  have hm := lineConvolution_measurable K hKm f f.continuous.measurable
  have hd : Integrable (fun x => (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4)) :=
    hj.integral_prod_right.const_mul _
  have hi : Integrable (fun x => ‖lineConvolution K f x‖^4) := by
    apply hd.mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (by positivity : 0≤‖lineConvolution K f x‖^4)]
    exact lineConvolution_fourth_pointwise K hK hKm f x
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x, (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) :=
      integral_mono hi hd (lineConvolution_fourth_pointwise K hK hKm f)
    _ = _ := by
      rw [integral_const_mul]
      rw [integral_integral_swap (f:=fun (x t : ℝ) => ‖K t‖*‖f (x-t)‖^4) hj.swap]
      simp_rw [integral_const_mul,integral_sub_right_eq_self (fun x => ‖f x‖^4)]
      rw [integral_mul_const]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
