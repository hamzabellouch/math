import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatWeighted
import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarSlabEndpoint
import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarFourJet

namespace OAI

/-! The weighted continuation equation specialized to the actual finite
Ising tail. Its inverse coordinate is the proved minimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticLogCoshMeanFourJet_derivative (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    HasDerivAt (fieldScalarValue L (fun y => Real.log (Real.cosh y)))
      ((magneticLogCoshMeanFourJet L hL).value z) z := by
  have he := congrArg MagneticContinuationJet.value (magneticLogCoshMeanFourJet_eq L hL)
  rw [he]
  exact hasDerivAt_fieldScalarLogCosh L hL z

def magneticScalarSlabFourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v : ℝ) : MagneticContinuationFourJet :=
  let P := magneticLogCoshMeanFourJet L hL
  let hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  P.transition P.toMagneticContinuationJet ζ (Real.toNNReal v)
    (fieldScalarValue L (fun y => Real.log (Real.cosh y))) hF.1 hF.2
    (magneticLogCoshMeanFourJet_derivative L hL)

def magneticScalarSlabContinuationFourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v : ℝ) :
    MagneticContinuationFourJet :=
  let P := magneticLogCoshMeanFourJet L hL
  let hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  A.transition P.toMagneticContinuationJet ζ (Real.toNNReal v)
    (fieldScalarValue L (fun y => Real.log (Real.cosh y))) hF.1 hF.2
    (magneticLogCoshMeanFourJet_derivative L hL)

lemma magneticScalarSlabFourJet_toJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v : ℝ) :
    (magneticScalarSlabFourJet L hL ζ v).toMagneticContinuationJet =
      magneticScalarSlabJet L hL ζ v := by
  simp only [magneticScalarSlabFourJet, MagneticContinuationFourJet.transition,
    magneticLogCoshMeanFourJet_eq, magneticScalarSlabJet]

lemma magneticScalarSlabContinuationFourJet_toJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v : ℝ) :
    (magneticScalarSlabContinuationFourJet L hL A ζ v).toMagneticContinuationJet =
      magneticScalarSlabContinuationJet L hL A.toMagneticContinuationJet ζ v := by
  simp only [magneticScalarSlabContinuationFourJet, MagneticContinuationFourJet.transition,
    magneticLogCoshMeanFourJet_eq, magneticScalarSlabContinuationJet]

lemma magneticScalarSlabWeighted_eq_heat (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v s : ℝ) :
    magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v s =
      magneticHeatWeighted (magneticLogCoshMeanFourJet L hL) A
        (fieldScalarValue L (fun y => Real.log (Real.cosh y))) ζ
          (v, magneticScalarSlabBias L ζ v s) := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  rw [magneticHeatWeighted_eq _ _ _ hF.1 hF.2 (magneticLogCoshMeanFourJet_derivative L hL)]
  simp only [magneticWeightedJetValue, MagneticContinuationFourJet.transition,
    magneticLogCoshMeanFourJet_eq, magneticScalarSlabWeighted,
    magneticScalarSlabJet, magneticScalarSlabContinuationJet]
  ring

lemma magneticScalarSlabWeighted_eq_jet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v s : ℝ) :
    magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v s =
      magneticWeightedJetValue (magneticScalarSlabFourJet L hL ζ v)
        (magneticScalarSlabContinuationFourJet L hL A ζ v) (magneticScalarSlabBias L ζ v s) := by
  unfold magneticWeightedJetValue magneticScalarSlabWeighted
  rw [← magneticScalarSlabFourJet_toJet L hL ζ v,
    ← magneticScalarSlabContinuationFourJet_toJet L hL A ζ v]
  ring

theorem magneticScalarSlabWeighted_hasDerivAt_time (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ v s : ℝ} (hζ : 0 ≤ ζ) (hv : 0 < v) (hs : |s| < 1) :
    let J := magneticScalarSlabFourJet L hL ζ v
    let K := magneticScalarSlabContinuationFourJet L hL A ζ v
    let b := magneticScalarSlabBias L ζ v s
    HasDerivAt (fun t => magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ t s)
      ((J.first b) ^ 2 / 2 * magneticWeightedInverseSecond J K b +
        (J.third b / J.first b - (J.second b) ^ 2 / (J.first b) ^ 2 + 2 * ζ * J.first b) *
          magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v s) v := by
  let P := magneticLogCoshMeanFourJet L hL
  let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hq : (P.toMagneticContinuationJet.transition P.toMagneticContinuationJet ζ
      (Real.toNNReal v) F hF.1 hF.2 (magneticLogCoshMeanFourJet_derivative L hL)).first
        (magneticScalarSlabBias L ζ v s) ≠ 0 := by
    have hp := (magneticScalarSlabJet_curvature_pos L hL hζ v
      (magneticScalarSlabBias L ζ v s)).ne'
    simpa only [P, magneticLogCoshMeanFourJet_eq, magneticScalarSlabJet, F] using hp
  have he : ∀ᶠ t in 𝓝 v, magneticHeatMean P.toMagneticContinuationJet F ζ
      (t, magneticScalarSlabBias L ζ t s) = s := by
    filter_upwards [] with t
    simp only [P, F, magneticLogCoshMeanFourJet_eq]
    rw [← magneticScalarSlabMean_eq L hL]
    exact magneticScalarSlabMean_bias L hL hζ hs t
  have hd := magneticHeatWeighted_inverse_hasDerivAt P A F hF.1 hF.2
    (magneticLogCoshMeanFourJet_derivative L hL) ζ hv
    (magneticScalarSlabBias_continuousAt_variance L hL hζ hs hv) he hq
  simpa only [← magneticScalarSlabWeighted_eq_heat, magneticScalarSlabFourJet,
    magneticScalarSlabContinuationFourJet, P, F,
    magneticScalarSlabWeighted_eq_jet] using hd

end InvariantIsing

end

end OAI
