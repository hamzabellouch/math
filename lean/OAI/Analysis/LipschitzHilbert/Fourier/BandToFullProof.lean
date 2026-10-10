import OAI.Analysis.LipschitzHilbert.Fourier.AnnularPVPartialBound
import OAI.Analysis.LipschitzHilbert.Fourier.PublishedBandReductionInput

namespace OAI

/-! A uniform full-frequency principal-value bound from the narrow-band
hypothesis, using finite annular reconstruction and Fatou's lemma. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace LipschitzHilbert.PacketRepresentation

theorem bandToFullInput_proved : BandToFullInput := by
  obtain ⟨D,hD,hannular⟩ := exists_annular_PV_constant
  intro B hB
  let E := B*D
  let C := 1+annularPVBoundConstant E
  have hC0 : 0≤annularPVBoundConstant E := by unfold annularPVBoundConstant; positivity
  refine ⟨C,by dsimp only [C]; linarith,?_⟩
  intro R hR hRs field hf hfb hband f
  let u := fun z => field (planeCoordinates z)
  have hum : Continuous u := (product_slope_lipschitz field hf).continuous
  have hub (z) : |u z|≤1 := (hfb _).trans (by norm_num)
  have hRquarter : R≤1/4 := by linarith
  have hrelative := hannular u R hR hRquarter B hB.le hband
  have hp (N : ℕ) := annularPVPartial_bound N field hf hfb R hR hRquarter E
    (mul_nonneg hB.le hD.le) hrelative f
  have hbound : eLpNorm (productSlopePrincipalValue u R f) 2 planeMeasure≤
      ENNReal.ofReal (annularPVBoundConstant E*‖f.toLp 2 planeMeasure‖) := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u:=(atTop : Filter ℕ))
      (Eventually.of_forall (fun N => (hp N).2))
      (fun N => (hp N).1.aestronglyMeasurable)
      ((productSlopePrincipalValue_measurable u hum.measurable f f.differentiable R hR hRquarter).aestronglyMeasurable)
    exact Eventually.of_forall (annularPVPartial_tendsto u hum hub R hR hRquarter f)
  refine ⟨hbound.trans_lt ENNReal.ofReal_lt_top,hbound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  dsimp only [C]
  nlinarith only [norm_nonneg (f.toLp 2 planeMeasure)]

end LipschitzHilbert.PacketRepresentation

end

end OAI
