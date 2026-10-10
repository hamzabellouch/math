import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabPDE
import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatContinuity

namespace OAI

/-! Actual bounded observables continued in the inverse mean coordinate.
Both spatial derivatives and the drift cancellation follow from the finite
Gaussian field, with no inverse-regularity assumptions left over. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarSlabContinuation (L : List (ℝ × ℝ≥0))
    (A : MagneticContinuationJet) (ζ v s : ℝ) : ℝ :=
  magneticHeatMean A (fieldScalarValue L (fun z => Real.log (Real.cosh z))) ζ
    (v, magneticScalarSlabBias L ζ v s)

def magneticScalarSlabContinuationJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ v : ℝ) : MagneticContinuationJet :=
  let P := magneticLogCoshMeanJet L hL
  let hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  A.transition P ζ (Real.toNNReal v)
    (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hF.1 hF.2
    (hasDerivAt_fieldScalarLogCosh L hL)

lemma magneticScalarSlabContinuation_eq_jet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ v s : ℝ) :
    magneticScalarSlabContinuation L A ζ v s =
      (magneticScalarSlabContinuationJet L hL A ζ v).value (magneticScalarSlabBias L ζ v s) := by
  exact magneticHeatMean_eq A _
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1 ζ _

def magneticScalarSlabContinuationSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabJet L hL ζ v
  let K := magneticScalarSlabContinuationJet L hL A ζ v
  let b := magneticScalarSlabBias L ζ v s
  K.first b / J.first b

def magneticScalarSlabContinuationSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ v s : ℝ) : ℝ :=
  let J := magneticScalarSlabJet L hL ζ v
  let K := magneticScalarSlabContinuationJet L hL A ζ v
  let b := magneticScalarSlabBias L ζ v s
  K.second b / (J.first b) ^ 2 - K.first b * J.second b / (J.first b) ^ 3

lemma magneticScalarSlabContinuation_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarSlabContinuation L A ζ v)
      (magneticScalarSlabContinuationSlope L hL A ζ v s) s := by
  have he : magneticScalarSlabContinuation L A ζ v = fun u =>
      (magneticScalarSlabContinuationJet L hL A ζ v).value
        (magneticScalarSlabBias L ζ v u) :=
    funext (magneticScalarSlabContinuation_eq_jet L hL A ζ v)
  rw [he]
  exact inverse_mean_pullback_derivative (magneticScalarSlabBias_hasDerivAt_jet L hL hζ hs v)
    ((magneticScalarSlabContinuationJet L hL A ζ v).dValue _)

lemma magneticScalarSlabContinuationSlope_hasDerivAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarSlabContinuationSlope L hL A ζ v)
      (magneticScalarSlabContinuationSecond L hL A ζ v s) s := by
  let J := magneticScalarSlabJet L hL ζ v
  let K := magneticScalarSlabContinuationJet L hL A ζ v
  let b := magneticScalarSlabBias L ζ v s
  have hd := inverse_mean_pullback_quotient
    (magneticScalarSlabJet_curvature_pos L hL hζ v b).ne'
    (magneticScalarSlabBias_hasDerivAt_jet L hL hζ hs v) rfl rfl
    (K.dFirst b) (J.dFirst b)
  exact hd

lemma magneticScalarSlabContinuation_second_deriv (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    deriv (deriv (magneticScalarSlabContinuation L A ζ v)) s =
      magneticScalarSlabContinuationSecond L hL A ζ v s := by
  apply HasDerivAt.deriv
  apply (magneticScalarSlabContinuationSlope_hasDerivAt L hL A hζ hs v).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2] with t ht
  exact (magneticScalarSlabContinuation_hasDerivAt_spin L hL A hζ (abs_lt.mpr ht) v).deriv

theorem magneticScalarSlabContinuation_PDE (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s v : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (hv : 0 < v) :
    HasDerivAt (fun t => magneticScalarSlabContinuation L A ζ t s)
      ((magneticScalarInverseCurvature L hL ζ v s) ^ 2 / 2 *
        deriv (deriv (magneticScalarSlabContinuation L A ζ v)) s) v := by
  rw [magneticScalarSlabContinuation_second_deriv L hL A hζ hs v,
    magneticScalarInverseCurvature_eq_jet]
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  apply magneticHeatInverse_continuation_hasDerivAt (s := s)
    (magneticLogCoshMeanJet L hL) A _ hF.1 hF.2
    (hasDerivAt_fieldScalarLogCosh L hL) ζ hv
    (magneticScalarSlabBias_continuousAt_variance L hL hζ hs hv)
  · exact Eventually.of_forall fun t => by
      rw [← magneticScalarSlabMean_eq L hL]
      exact magneticScalarSlabMean_bias L hL hζ hs t
  · exact (magneticScalarSlabJet_curvature_pos L hL hζ v _).ne'

end InvariantIsing

end

end OAI
