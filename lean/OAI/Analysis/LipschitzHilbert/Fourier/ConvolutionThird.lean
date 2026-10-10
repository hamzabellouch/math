import OAI.Analysis.LipschitzHilbert.Fourier.ConvolutionLayerTail

namespace OAI

/-! Real interpolation at exponent three for bounded measurable inputs.
The proof integrates the two amplitude-dependent Markov bounds. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem highLayerEnergy_measurable (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (highLayerEnergy f) := by
  have hm : Measurable (fun p : ℝ×ℝ => if p.1≤‖f p.2‖ then ENNReal.ofReal (‖f p.2‖^2) else 0) :=
    ((hf.comp measurable_snd).norm.pow_const 2).ennreal_ofReal.ite
      (measurableSet_le measurable_fst (hf.comp measurable_snd).norm) measurable_const
  exact hm.lintegral_prod_right'

theorem lowLayerEnergy_measurable (f : ℝ → ℂ) (hf : Measurable f) :
    Measurable (lowLayerEnergy f) := by
  have hm : Measurable (fun p : ℝ×ℝ => if ‖f p.2‖<p.1 then ENNReal.ofReal (‖f p.2‖^4) else 0) :=
    ((hf.comp measurable_snd).norm.pow_const 4).ennreal_ofReal.ite
      (measurableSet_lt (hf.comp measurable_snd).norm measurable_fst) measurable_const
  exact hm.lintegral_prod_right'

theorem convolution_third_lintegral (K f : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (hf : Measurable f) (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume)
    (M : ℝ) (hM : ∀ x, ‖f x‖≤M) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (h2 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^2)≤A^2*(∫ x, ‖g x‖^2))
    (h4 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4)) :
    (∫⁻ x, ENNReal.ofReal (‖lineConvolution K f x‖^3))≤
      ENNReal.ofReal (3*(4*A^2+16*C^4))*(∫⁻ x, ENNReal.ofReal (‖f x‖^3)) := by
  have hm := lineConvolution_measurable K hKm f hf
  have hlc : (∫⁻ x, ENNReal.ofReal (‖lineConvolution K f x‖^3))=
      ENNReal.ofReal 3*(∫⁻ t in Ioi 0,
        ENNReal.ofReal (t^2)*volume {x | t≤‖lineConvolution K f x‖}) := by
    have hh := lintegral_rpow_eq_lintegral_meas_le_mul volume
        (Filter.Eventually.of_forall fun x => norm_nonneg (lineConvolution K f x))
        hm.norm.aemeasurable (by norm_num : 0<(3:ℝ))
    simp only [show (3:ℝ)-1=2 by norm_num,Real.rpow_ofNat] at hh
    rw [hh]
    congr 1
    apply lintegral_congr
    intro t
    rw [mul_comm]
  have hhigh := highLayerEnergy_measurable f hf
  have hlow := lowLayerEnergy_measurable f hf
  have hdom := lintegral_mono_ae (μ:=volume.restrict (Ioi (0:ℝ))) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact convolution_layer_tail K f hK hKm hf hf2 hf4 M hM A C hA hC h2 h4 t ht)
  rw [hlc]
  calc
    _ ≤ ENNReal.ofReal 3*(∫⁻ t in Ioi 0,
        ENNReal.ofReal (4*A^2)*highLayerEnergy f t+
        ENNReal.ofReal (16*C^4)*(ENNReal.ofReal (t^(-2:ℝ))*lowLayerEnergy f t)) :=
      mul_le_mul_right hdom _
    _ = ENNReal.ofReal 3*(ENNReal.ofReal (4*A^2)*(∫⁻ x, ENNReal.ofReal (‖f x‖^3))+
        ENNReal.ofReal (16*C^4)*(∫⁻ x, ENNReal.ofReal (‖f x‖^3))) := by
      rw [lintegral_add_left (hhigh.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        highLayerEnergy_integral f hf,lowLayerEnergy_integral f hf]
    _ = _ := by
      rw [←add_mul,←mul_assoc,←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_mul (by norm_num)]

theorem memLp_two_four_integrable_cube (f : ℝ → ℂ) (hf : Measurable f)
    (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume) :
    Integrable (fun x => ‖f x‖^3) := by
  apply ((hf2.integrable_norm_pow (by decide : 2≠0)).add
    (hf4.integrable_norm_pow (by decide : 4≠0))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (by positivity : 0≤‖f x‖^3)]
  change ‖f x‖^3≤‖f x‖^2+‖f x‖^4
  nlinarith [sq_nonneg (‖f x‖-1),sq_nonneg (‖f x‖*(‖f x‖-1))]

theorem convolution_third_bound (K f : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (hf : Measurable f) (hf2 : MemLp f 2 volume) (hf4 : MemLp f 4 volume)
    (M : ℝ) (hM : ∀ x, ‖f x‖≤M) (A C : ℝ) (hA : 0≤A) (hC : 0≤C)
    (h2 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^2)≤A^2*(∫ x, ‖g x‖^2))
    (h4 : ∀ g : SchwartzMap ℝ ℂ, (∫ x, ‖lineConvolution K g x‖^4)≤C^4*(∫ x, ‖g x‖^4)) :
    Integrable (fun x => ‖lineConvolution K f x‖^3) ∧
      (∫ x, ‖lineConvolution K f x‖^3)≤(3*(4*A^2+16*C^4))*(∫ x, ‖f x‖^3) := by
  have hlin := convolution_third_lintegral K f hK hKm hf hf2 hf4 M hM A C hA hC h2 h4
  have hfi := memLp_two_four_integrable_cube f hf hf2 hf4
  have hfinite := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => show 0≤‖f x‖^3 by positivity)).mp hfi.2
  have hfinal : (∫⁻ x, ENNReal.ofReal (‖lineConvolution K f x‖^3))<⊤ :=
    hlin.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite)
  have hi : Integrable (fun x => ‖lineConvolution K f x‖^3) := by
    refine ⟨(lineConvolution_measurable K hKm f hf).norm.pow_const 3 |>.aestronglyMeasurable,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by positivity)).mpr hfinal
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity),
    ←ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun x => by positivity),
    ←ENNReal.ofReal_mul (by positivity)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlin

end LipschitzHilbert.PacketRepresentation

end

end OAI
