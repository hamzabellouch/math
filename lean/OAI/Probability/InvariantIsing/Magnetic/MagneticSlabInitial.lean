import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabBoundary

namespace OAI

/-! Exact zero-variance data for the inverse-coordinate slab equations.
The continued square starts at s², and the final tanh curvature at 1-s². -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticScalarSlabMean_zero (L : List (ℝ × ℝ≥0)) (ζ z : ℝ) :
    magneticScalarSlabMean L ζ 0 z =
      fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh z := by
  simp only [magneticScalarSlabMean, Real.toNNReal_zero, fieldSpinTransition_zero_variance]

lemma magneticScalarSlabBias_zero (L : List (ℝ × ℝ≥0)) (ζ η s : ℝ) :
    magneticScalarSlabBias L ζ 0 s = magneticScalarSlabBias L η 0 s := by
  unfold magneticScalarSlabBias
  apply congrArg (fun f : ℝ → ℝ => Function.invFun f s)
  funext z
  rw [magneticScalarSlabMean_zero, magneticScalarSlabMean_zero]

lemma magneticScalarSlab_square_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) :
    magneticHeatMean (magneticLogCoshMeanJet L hL).square
      (fieldScalarValue L (fun x => Real.log (Real.cosh x))) ζ
      (0, magneticScalarSlabBias L ζ 0 s) = s ^ 2 := by
  rw [magneticHeatMean_eq _ _
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1]
  simp only [Real.toNNReal_zero, fieldSpinTransition_zero_variance, MagneticContinuationJet.square]
  have hh := magneticScalarSlabMean_bias L hL hζ hs 0
  rw [magneticScalarSlabMean_zero] at hh
  change (fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh
    (magneticScalarSlabBias L ζ 0 s)) ^ 2 = s ^ 2
  rw [hh]

lemma magneticScalarInverseCurvature_nil_initial
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) :
    magneticScalarInverseCurvature [] (by simp) ζ 0 s = 1 - s ^ 2 := by
  rw [magneticScalarInverseCurvature_eq]
  simp only [Real.toNNReal_zero, fieldCurvatureTransform, fieldSpinTransition_zero_variance,
    sub_self, mul_zero, add_zero]
  have hh := magneticScalarSlabMean_bias [] (by simp) hζ hs 0
  rw [magneticScalarSlabMean_zero] at hh
  change Real.tanh (magneticScalarSlabBias [] ζ 0 s) = s at hh
  change 1 / (Real.cosh (magneticScalarSlabBias [] ζ 0 s)) ^ 2 = 1 - s ^ 2
  have hv := field_logCosh_spin_variance (magneticScalarSlabBias [] ζ 0 s)
  rw [hh] at hv
  linarith

end InvariantIsing

end

end OAI
