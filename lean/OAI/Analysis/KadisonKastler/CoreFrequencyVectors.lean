import OAI.Analysis.KadisonKastler.CoreFrequencyCuts
import OAI.Analysis.KadisonKastler.RegularCoreHilbertSum

namespace OAI

/-! # Vectors supported in the bounded-frequency core corners -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def regularFrequencyPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) : RegularCoreHilbert H :=
  (Lp.fourierTransformₗᵢ ℝ H).symm (regularTensorVector φ ξ)

theorem norm_regularFrequencyPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    ‖regularFrequencyPacket φ ξ‖ = ‖φ‖ * ‖ξ‖ := by
  rw [regularFrequencyPacket, LinearIsometryEquiv.norm_map, norm_regularTensorVector]

omit [CompleteSpace H] in
theorem regularIndicatorProjection_tensor (s : Set ℝ) (hs : MeasurableSet s)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    regularIndicatorProjection s hs (regularTensorVector φ ξ) =
      regularTensorVector (regularIndicatorProjection s hs φ) ξ := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae s hs (regularTensorVector φ ξ),
    regularTensorVector_apply_ae φ ξ,
    regularTensorVector_apply_ae (regularIndicatorProjection s hs φ) ξ,
    regularIndicatorProjection_apply_ae s hs φ] with t hp hφ ht hps
  rw [hp, ht]
  by_cases h : t ∈ s
  · simp only [Set.indicator_of_mem h] at hps ⊢
    rw [hφ, hps]
  · simp only [Set.indicator_of_notMem h] at hps ⊢
    rw [hps, zero_smul]

theorem regularFrequencyWindow_packet (a b : ℝ)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    regularFrequencyWindow a b (regularFrequencyPacket φ ξ) =
      regularFrequencyPacket (regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc φ) ξ := by
  unfold regularFrequencyWindow regularFrequencyPacket
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    regularIndicatorProjection_tensor]

end

end KadisonKastler

end OAI
