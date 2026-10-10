import OAI.Analysis.LipschitzHilbert.Fourier.VerticalConvolutionL2
import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram

namespace OAI

/-! Vertical convolution on the L2 quotient, with its actual integral representative. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_congr_ae (K : ℝ → ℂ) (f g : ℝ×ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g) (hfg : f=ᵐ[planeMeasure] g) :
    verticalConvolution K f=ᵐ[planeMeasure] verticalConvolution K g := by
  have he : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ z ∂planeMeasure,
      f (z.1,z.2-t)=g (z.1,z.2-t) := by
    apply Filter.Eventually.of_forall
    intro t
    exact (verticalTranslation_measurePreserving t).quasiMeasurePreserving.ae hfg
  have hm : MeasurableSet {p : ℝ×(ℝ×ℝ) | f (p.2.1,p.2.2-p.1)=g (p.2.1,p.2.2-p.1)} :=
    measurableSet_eq_fun (hf.comp (by fun_prop)) (hg.comp (by fun_prop))
  have hs := (Measure.ae_ae_comm hm).mp he
  filter_upwards [hs] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with t ht
  rw [ht]

theorem verticalConvolution_integrand_ae (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    ∀ᵐ z ∂planeMeasure, Integrable (fun t => K t*f (z.1,z.2-t)) := by
  filter_upwards [(verticalConvolution_energy_joint_integrable K hK hKm f hfm hf).prod_left_ae]
    with z hz
  have hc := (weighted_integral_cauchySchwarz volume (fun t => ‖K t‖)
    (fun t => ‖f (z.1,z.2-t)‖) hKm.norm (hfm.norm.comp (by fun_prop))
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hK.norm hz).1
  exact hc.mono' ((hKm.mul (hfm.comp (by fun_prop))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => le_of_eq (norm_mul _ _))

theorem verticalConvolution_sub_ae (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (f g : ℝ×ℝ → ℂ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 planeMeasure) (hg : MemLp g 2 planeMeasure) :
    verticalConvolution K (f-g)=ᵐ[planeMeasure]
      (verticalConvolution K f-verticalConvolution K g) := by
  filter_upwards [verticalConvolution_integrand_ae K hK hKm f hfm hf,
    verticalConvolution_integrand_ae K hK hKm g hgm hg] with z hfz hgz
  change (∫ t, K t*(f (z.1,z.2-t)-g (z.1,z.2-t)))=_
  simp_rw [mul_sub]
  exact integral_sub hfz hgz

def verticalConvolutionLp (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : Lp ℂ 2 planeMeasure) : Lp ℂ 2 planeMeasure :=
  (verticalConvolution_energy_bound K hK hKm f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1.toLp
    (verticalConvolution K f)

theorem verticalConvolutionLp_coe (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : Lp ℂ 2 planeMeasure) :
    (verticalConvolutionLp K hK hKm f : (ℝ×ℝ) → ℂ)=ᵐ[planeMeasure] verticalConvolution K f :=
  MemLp.coeFn_toLp _

theorem verticalConvolutionLp_toLp (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    verticalConvolutionLp K hK hKm (hf.toLp f)=
      (verticalConvolution_energy_bound K hK hKm f hfm hf).1.toLp (verticalConvolution K f) := by
  apply Lp.ext
  exact (verticalConvolutionLp_coe K hK hKm _).trans
    ((verticalConvolution_congr_ae K _ f (Lp.stronglyMeasurable (hf.toLp f)).measurable hfm hf.coeFn_toLp).trans
      (MemLp.coeFn_toLp _).symm)

theorem verticalConvolutionLp_sub (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f g : Lp ℂ 2 planeMeasure) :
    verticalConvolutionLp K hK hKm (f-g)=
      verticalConvolutionLp K hK hKm f-verticalConvolutionLp K hK hKm g := by
  apply Lp.ext
  have hc := verticalConvolution_congr_ae K (show Lp ℂ 2 planeMeasure from f-g) ((f : (ℝ×ℝ)→ℂ)-(g : (ℝ×ℝ)→ℂ))
    (Lp.stronglyMeasurable (f-g)).measurable ((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable)
    (Lp.coeFn_sub f g)
  have hs := verticalConvolution_sub_ae K hK hKm f g (Lp.stronglyMeasurable f).measurable
    (Lp.stronglyMeasurable g).measurable (Lp.memLp f) (Lp.memLp g)
  filter_upwards [verticalConvolutionLp_coe K hK hKm (f-g),hc,hs,
    verticalConvolutionLp_coe K hK hKm f,verticalConvolutionLp_coe K hK hKm g,
    Lp.coeFn_sub (verticalConvolutionLp K hK hKm f) (verticalConvolutionLp K hK hKm g)]
    with z h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,h6]
  simp only [Pi.sub_apply,h4,h5]

theorem verticalConvolutionLp_norm (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K)
    (f : Lp ℂ 2 planeMeasure) :
    ‖verticalConvolutionLp K hK hKm f‖≤(∫ t, ‖K t‖)*‖f‖ := by
  have h := (verticalConvolution_energy_bound K hK hKm f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).2
  rw [←memLp_toL2_norm_sq planeMeasure _ (Lp.memLp f),Lp.toLp_coeFn,
    ←memLp_toL2_norm_sq planeMeasure _
      (verticalConvolution_energy_bound K hK hKm f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1] at h
  change ‖verticalConvolutionLp K hK hKm f‖^2≤(∫ t, ‖K t‖)^2*‖f‖^2 at h
  have hn : 0≤∫ t, ‖K t‖ := integral_nonneg (fun t => norm_nonneg (K t))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (norm_nonneg f))).mp
  simpa only [mul_pow] using h

theorem verticalConvolutionLp_continuous (K : ℝ → ℂ) (hK : Integrable K) (hKm : Measurable K) :
    Continuous (verticalConvolutionLp K hK hKm) := by
  apply LipschitzWith.continuous (K:=⟨∫ t, ‖K t‖,integral_nonneg fun _ => norm_nonneg _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm,dist_eq_norm,←verticalConvolutionLp_sub]
  exact verticalConvolutionLp_norm K hK hKm (f-g)

end LipschitzHilbert.PacketRepresentation

end

end OAI
