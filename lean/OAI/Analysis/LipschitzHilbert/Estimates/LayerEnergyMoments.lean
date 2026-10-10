import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionL4
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

namespace OAI

/-! The two layer integrals needed to interpolate the second and fourth
moments to the third moment. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def highLayerEnergy (f : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, if t≤‖f x‖ then ENNReal.ofReal (‖f x‖^2) else 0

def lowLayerEnergy (f : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, if ‖f x‖<t then ENNReal.ofReal (‖f x‖^4) else 0

theorem highLayerEnergy_integral (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ t in Ioi 0, highLayerEnergy f t)=∫⁻ x, ENNReal.ofReal (‖f x‖^3) := by
  unfold highLayerEnergy
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro x
    have he : (fun t : ℝ => if t≤‖f x‖ then ENNReal.ofReal (‖f x‖^2) else 0)=
        (Iic ‖f x‖).indicator (fun _ => ENNReal.ofReal (‖f x‖^2)) := by
      funext t
      simp only [Set.indicator,mem_Iic]
    rw [he,lintegral_indicator measurableSet_Iic,lintegral_const]
    simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter]
    rw [Measure.restrict_apply measurableSet_Iic]
    have hset : Iic ‖f x‖∩Ioi (0:ℝ)=Ioc 0 ‖f x‖ := by ext t; simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc]; tauto
    rw [hset,Real.volume_Ioc,sub_zero,←ENNReal.ofReal_mul (by positivity)]
    congr 1
  · exact ((hf.comp measurable_snd).norm.pow_const 2).ennreal_ofReal.ite
      (measurableSet_le measurable_fst (hf.comp measurable_snd).norm) measurable_const |>.aemeasurable

theorem lowLayer_scalar_integral (a : ℝ) (ha : 0≤a) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^(-2:ℝ))*
      (if a<t then ENNReal.ofReal (a^4) else 0))=ENNReal.ofReal (a^3) := by
  by_cases hz : a=0
  · subst a
    simp
  have hap : 0<a := lt_of_le_of_ne ha (Ne.symm hz)
  have he : (fun t : ℝ => ENNReal.ofReal (t^(-2:ℝ))*
      (if a<t then ENNReal.ofReal (a^4) else 0))=
      (Ioi a).indicator (fun t => ENNReal.ofReal (t^(-2:ℝ))*ENNReal.ofReal (a^4)) := by
    funext t
    by_cases ht : a<t <;> simp [ht]
  rw [he,lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  rw [inter_eq_left.mpr (Ioi_subset_Ioi ha)]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hint : IntegrableOn (fun t : ℝ => t^(-2:ℝ)) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hap
  have hnonneg : 0≤ᵐ[volume.restrict (Ioi a)] (fun t : ℝ => t^(-2:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hap.trans ht).le _
  rw [←ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hap]
  norm_num
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  exact Real.rpow_neg_one a ▸ inv_mul_cancel₀ hz

theorem lowLayerEnergy_integral (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t^(-2:ℝ))*lowLayerEnergy f t)=
      ∫⁻ x, ENNReal.ofReal (‖f x‖^3) := by
  unfold lowLayerEnergy
  simp_rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap]
  · exact lintegral_congr fun x => lowLayer_scalar_integral ‖f x‖ (norm_nonneg _)
  · have hm : Measurable (fun p : ℝ×ℝ => if ‖f p.2‖<p.1 then ENNReal.ofReal (‖f p.2‖^4) else 0) :=
      ((hf.comp measurable_snd).norm.pow_const 4).ennreal_ofReal.ite
        (measurableSet_lt (hf.comp measurable_snd).norm measurable_fst) measurable_const
    exact ((measurable_fst.pow_const (-2:ℝ)).ennreal_ofReal.mul hm).aemeasurable

end LipschitzHilbert.PacketRepresentation

end

end OAI
