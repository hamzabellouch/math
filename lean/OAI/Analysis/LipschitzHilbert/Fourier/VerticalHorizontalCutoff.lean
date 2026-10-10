import OAI.Analysis.LipschitzHilbert.Fourier.VerticalL2Projection
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinLpReconstruction
import OAI.Analysis.LipschitzHilbert.Estimates.L2Indicator

namespace OAI

/-! Vertical Fourier projections commute with measurable horizontal
cutoffs. The proof uses their actual convolution representatives. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalL2Projection_eq_profile (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : Lp ℂ 2 planeMeasure) :
    verticalL2Projection p w f=verticalProfileLp p w 0 hw f := by
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f ?_ ?_
  · exact isClosed_eq (verticalL2Projection p w).continuous (verticalProfileLp_continuous p w 0 hw)
  · intro g
    rw [verticalL2Projection_onSchwartz _ _ hw,verticalProfileLp_schwartz]

theorem verticalConvolution_horizontal_indicator (K : ℝ → ℂ) (S : Set ℝ) (f : ℝ×ℝ → ℂ) :
    verticalConvolution K ((Prod.fst ⁻¹' S).indicator f)=
      (Prod.fst ⁻¹' S).indicator (verticalConvolution K f) := by
  funext z
  by_cases hz : z.1∈S
  · rw [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hz)]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [Set.indicator_of_mem (show (z.1,z.2-t)∈Prod.fst ⁻¹' S from hz)]
  · rw [Set.indicator_of_notMem (show z∉Prod.fst ⁻¹' S from hz)]
    apply integral_eq_zero_of_ae
    filter_upwards [] with t
    change K t*((Prod.fst ⁻¹' S).indicator f (z.1,z.2-t))=0
    rw [Set.indicator_of_notMem (show (z.1,z.2-t)∉Prod.fst ⁻¹' S from hz),mul_zero]

theorem verticalConvolutionLp_horizontal_indicator (K : ℝ → ℂ) (hK : Integrable K)
    (hKm : Measurable K) (S : Set ℝ) (hS : MeasurableSet S) (f : Lp ℂ 2 planeMeasure) :
    verticalConvolutionLp K hK hKm (l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) f)=
      l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) (verticalConvolutionLp K hK hKm f) := by
  let M := l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst)
  have hc := verticalConvolution_congr_ae K (M f) ((Prod.fst ⁻¹' S).indicator f)
    (Lp.stronglyMeasurable (M f)).measurable
    ((Lp.stronglyMeasurable f).measurable.indicator (hS.preimage measurable_fst))
    (l2Indicator_coe planeMeasure _ _ f)
  apply Lp.ext
  filter_upwards [verticalConvolutionLp_coe K hK hKm (M f),hc,
    l2Indicator_coe planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) (verticalConvolutionLp K hK hKm f),
    verticalConvolutionLp_coe K hK hKm f] with z hz hc hz' hf
  change verticalConvolutionLp K hK hKm (M f) z=_
  rw [hz,hc,verticalConvolution_horizontal_indicator,hz']
  by_cases hmem : z.1∈S
  · simp only [Set.indicator_of_mem (show z∈Prod.fst ⁻¹' S from hmem),hf]
  · simp only [Set.indicator_of_notMem (show z∉Prod.fst ⁻¹' S from hmem)]

theorem verticalL2Projection_horizontal_indicator (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (S : Set ℝ) (hS : MeasurableSet S) (f : Lp ℂ 2 planeMeasure) :
    verticalL2Projection p w (l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) f)=
      l2Indicator planeMeasure (Prod.fst ⁻¹' S) (hS.preimage measurable_fst) (verticalL2Projection p w f) := by
  rw [verticalL2Projection_eq_profile _ _ hw,verticalL2Projection_eq_profile _ _ hw]
  exact verticalConvolutionLp_horizontal_indicator _ _ _ S hS f

end LipschitzHilbert.PacketRepresentation

end

end OAI
