import OAI.Probability.InvariantIsing.Magnetic.MagneticWeightedSpatial

namespace OAI

/-! Initial data of the weighted square-continuation equation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticScalarSlabJet_zero (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) :
    magneticScalarSlabJet L hL ζ 0 = magneticLogCoshMeanJet L hL := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  simp only [magneticScalarSlabJet, MagneticContinuationJet.transition,
    Real.toNNReal_zero, fieldSpinTransition_zero_variance]

lemma magneticScalarSlabContinuationJet_zero (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ : ℝ) :
    magneticScalarSlabContinuationJet L hL A ζ 0 = A := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  simp only [magneticScalarSlabContinuationJet, MagneticContinuationJet.transition,
    Real.toNNReal_zero, fieldSpinTransition_zero_variance]

lemma magneticScalarSlabWeighted_zero (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ s : ℝ) :
    let P := magneticLogCoshMeanJet L hL
    let z := magneticScalarSlabBias L ζ 0 s
    magneticScalarSlabWeighted L hL A ζ 0 s =
      A.second z - A.first z * (P.second z / P.first z) := by
  simp only [magneticScalarSlabWeighted, magneticScalarSlabJet_zero,
    magneticScalarSlabContinuationJet_zero]

lemma magneticScalarSlabWeighted_square_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ s : ℝ) :
    magneticScalarSlabWeighted L hL (magneticLogCoshMeanJet L hL).square ζ 0 s =
      2 * ((magneticLogCoshMeanJet L hL).first (magneticScalarSlabBias L ζ 0 s)) ^ 2 := by
  rw [magneticScalarSlabWeighted_zero]
  have hq := (fieldScalarLogCoshSecond_pos L hL (magneticScalarSlabBias L ζ 0 s)).ne'
  change (magneticLogCoshMeanJet L hL).first (magneticScalarSlabBias L ζ 0 s) ≠ 0 at hq
  simp only [MagneticContinuationJet.square]
  field_simp [hq]
  ring

lemma magneticScalarSlabWeighted_square_initial_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ s : ℝ) :
    0 ≤ magneticScalarSlabWeighted L hL (magneticLogCoshMeanJet L hL).square ζ 0 s := by
  rw [magneticScalarSlabWeighted_square_initial]
  positivity

end InvariantIsing

end

end OAI
