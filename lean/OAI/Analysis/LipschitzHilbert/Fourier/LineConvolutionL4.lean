import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionFourth
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace OAI

/-! The line convolution fourth-power estimate for measurable L4 inputs. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem memLp_fourth_iff (f : ℝ → ℂ) (hfm : AEStronglyMeasurable f volume) :
    MemLp f 4 volume ↔ Integrable (fun x => ‖f x‖^4) := by
  simpa using (integrable_norm_rpow_iff (p:=4) hfm (by norm_num) (by norm_num)).symm

theorem memLp_toL4_norm_pow (f : ℝ → ℂ) (hf : MemLp f 4 volume) :
    ‖hf.toLp f‖^4=∫ x, ‖f x‖^4 := by
  rw [Lp.norm_toLp,toReal_eLpNorm,lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  rw [←Real.rpow_natCast,←Real.rpow_mul (integral_nonneg fun _ => by positivity)]
  norm_num

theorem lineConvolution_fourth_joint (K f : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hfm : Measurable f) (hf : MemLp f 4 volume) :
    Integrable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) (volume.prod volume) := by
  have hm : Measurable (fun p : ℝ×ℝ => ‖K p.1‖*‖f (p.2-p.1)‖^4) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun t =>
      ((lineTranslation_measurePreserving t).integrable_comp_of_integrable
        (hf.integrable_norm_pow (by decide : 4≠0))).const_mul ‖K t‖
  · have heq (t : ℝ) : (∫ z, ‖‖K t‖*‖f (z-t)‖^4‖)=‖K t‖*(∫ z, ‖f z‖^4) := by
      simp only [norm_mul,Real.norm_of_nonneg (norm_nonneg (K t)),norm_pow,norm_norm]
      rw [integral_const_mul,integral_sub_right_eq_self (fun z => ‖f z‖^4) t]
    simp_rw [heq]
    exact hK.norm.mul_const _

theorem lineConvolution_fourth_at (K f : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hfm : Measurable f) (x : ℝ)
    (hi : Integrable (fun t => ‖K t‖*‖f (x-t)‖^4)) :
    ‖lineConvolution K f x‖^4≤(∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := by
  have hfourth : Integrable (fun t => ‖K t‖*(‖f (x-t)‖^2)^2) := by
    simpa only [←pow_mul] using hi
  have hsecond := weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖f (x-t)‖^2) hKm.norm (by fun_prop) (fun _ => norm_nonneg _)
    (fun _ => sq_nonneg _) hK.norm hfourth
  have hfirst := lineConvolution_pointwise_energy K hK hKm f hfm x hsecond.1
  have hs := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  calc
    ‖lineConvolution K f x‖^4 = (‖lineConvolution K f x‖^2)^2 := by ring
    _ ≤ ((∫ t, ‖K t‖)*(∫ t, ‖K t‖*‖f (x-t)‖^2))^2 := hs
    _ = (∫ t, ‖K t‖)^2*(∫ t, ‖K t‖*‖f (x-t)‖^2)^2 := mul_pow _ _ _
    _ ≤ (∫ t, ‖K t‖)^2*((∫ t, ‖K t‖)*(∫ t, ‖K t‖*(‖f (x-t)‖^2)^2)) :=
      mul_le_mul_of_nonneg_left hsecond.2 (sq_nonneg _)
    _ = _ := by simp only [←pow_mul]; ring

theorem lineConvolution_L4_bound (K f : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (hfm : Measurable f) (hf : MemLp f 4 volume) :
    MemLp (lineConvolution K f) 4 volume ∧
      (∫ x, ‖lineConvolution K f x‖^4)≤(∫ t, ‖K t‖)^4*(∫ x, ‖f x‖^4) := by
  have hj := lineConvolution_fourth_joint K f hK hKm hfm hf
  have hm := lineConvolution_measurable K hKm f hfm
  have hd : Integrable (fun x => (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4)) :=
    hj.integral_prod_right.const_mul _
  have hp : ∀ᵐ x ∂volume, ‖lineConvolution K f x‖^4≤
      (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := by
    filter_upwards [hj.prod_left_ae] with x hx
    exact lineConvolution_fourth_at K f hK hKm hfm x hx
  have hi : Integrable (fun x => ‖lineConvolution K f x‖^4) := by
    apply hd.mono' (by fun_prop)
    filter_upwards [hp] with x hx
    rwa [Real.norm_of_nonneg (by positivity : 0≤‖lineConvolution K f x‖^4)]
  refine ⟨(memLp_fourth_iff _ hm.aestronglyMeasurable).2 hi,?_⟩
  calc
    _ ≤ ∫ x, (∫ t, ‖K t‖)^3*(∫ t, ‖K t‖*‖f (x-t)‖^4) := integral_mono_ae hi hd hp
    _ = _ := by
      rw [integral_const_mul]
      rw [integral_integral_swap (f:=fun (x t : ℝ) => ‖K t‖*‖f (x-t)‖^4) hj.swap]
      simp_rw [integral_const_mul,integral_sub_right_eq_self (fun x => ‖f x‖^4)]
      rw [integral_mul_const]
      ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
