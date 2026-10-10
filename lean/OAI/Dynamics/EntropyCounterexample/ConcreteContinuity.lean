import OAI.Dynamics.EntropyCounterexample.MapData
import OAI.Dynamics.EntropyCounterexample.MapContinuity
import OAI.Dynamics.EntropyCounterexample.MapQuotientContinuity

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem continuous_concrete_baseInput (L : ℝ) (hL : 2 < L) (i : Fin 3) :
    Continuous (fun x : ℝ × Sphere => baseInput (concreteData L hL) i x.1 x.2) := by
  apply continuous_baseInput_of_standard_cutoffs _ rfl rfl
  change 1 < L
  linarith

theorem continuous_concrete_input (L : ℝ) (hL : 2 < L) (i : Fin 3) :
    Continuous (fun x : AddCircle (100 : ℝ) × Sphere =>
      input (concreteData L hL) i x.1 x.2) :=
  continuous_input_of_baseInput _ i (continuous_concrete_baseInput L hL i)

theorem concrete_gain_seam (L : ℝ) (hL : 2 < L) :
    (concreteData L hL).gain 0 = (concreteData L hL).gain 100 := by
  change gainProfile L 0 = gainProfile L 100
  rw [gainProfile_zero_outside (by norm_num), gainProfile_zero_outside (by norm_num)]

theorem continuous_concrete_periodicGain (L : ℝ) (hL : 2 < L) :
    Continuous (periodicGain (concreteData L hL)) := by
  let : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩
  apply AddCircle.liftIco_zero_continuous
  · exact concrete_gain_seam L hL
  · exact (gainProfile_contDiff L).continuous.continuousOn

theorem continuous_concreteMap (L : ℝ) (hL : 2 < L) :
    Continuous (concreteMap L hL) := by
  apply continuous_rawMap_of_coefficients (concreteData L hL)
  · exact SphereCutoffs.continuous_onePointClockGate
  · exact continuous_concrete_input L hL
  · exact sphereSaturation_continuous (3 * L) _
  · exact continuous_concrete_periodicGain L hL

end Problem340.Construction

end

end OAI
