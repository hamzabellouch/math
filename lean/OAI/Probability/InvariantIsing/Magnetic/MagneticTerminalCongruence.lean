import OAI.Probability.InvariantIsing.Fields.FieldTerminalOne
import OAI.Probability.InvariantIsing.Magnetic.MagneticTailCongruence
import OAI.Probability.InvariantIsing.Magnetic.MagneticSquareInitial

namespace OAI

/-! Constant terminal shifts leave the optimizing bias, inverse
curvature, and all preceding conditional square means unchanged. -/

noncomputable section
open Filter Set IsingPerceptron
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticLogCoshMeanJet_eq_of_value_const_add (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1) (c : ℝ)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fun z => c + fieldScalarValue M (fun z => Real.log (Real.cosh z)) z) :
    magneticLogCoshMeanJet L hL = magneticLogCoshMeanJet M hM := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  have hl := hasDerivAt_fieldScalarLogCosh L hL z
  rw [he] at hl
  exact hl.unique ((hasDerivAt_fieldScalarLogCosh M hM z).const_add c)

lemma magneticScalarSlabMean_eq_of_value_const_add (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1) (c : ℝ)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fun z => c + fieldScalarValue M (fun z => Real.log (Real.cosh z)) z)
    (ζ v : ℝ) : magneticScalarSlabMean L ζ v = magneticScalarSlabMean M ζ v := by
  have hj := magneticLogCoshMeanJet_eq_of_value_const_add L M hL hM c he
  have hm := congrArg MagneticContinuationJet.value hj
  change fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh =
    fieldScalarMean M (fun z => Real.log (Real.cosh z)) Real.tanh at hm
  unfold magneticScalarSlabMean
  rw [he, hm]
  funext z
  exact fieldSpinTransition_const_add ζ (Real.toNNReal v) _ _ c z

lemma magneticScalarSlabBias_eq_of_value_const_add (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1) (c : ℝ)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fun z => c + fieldScalarValue M (fun z => Real.log (Real.cosh z)) z)
    (ζ v : ℝ) : magneticScalarSlabBias L ζ v = magneticScalarSlabBias M ζ v := by
  unfold magneticScalarSlabBias
  rw [magneticScalarSlabMean_eq_of_value_const_add L M hL hM c he]

lemma closedMagneticScalarCurvature_eq_of_value_const_add (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1) (c : ℝ)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fun z => c + fieldScalarValue M (fun z => Real.log (Real.cosh z)) z)
    (ζ : ℝ) (p : ℝ × ℝ) :
    closedMagneticScalarCurvature L hL ζ p = closedMagneticScalarCurvature M hM ζ p := by
  have hj := magneticLogCoshMeanJet_eq_of_value_const_add L M hL hM c he
  have hb := magneticScalarSlabBias_eq_of_value_const_add L M hL hM c he ζ p.1
  unfold closedMagneticScalarCurvature
  split_ifs
  · rw [magneticScalarInverseCurvature_eq, magneticScalarInverseCurvature_eq, hj, he, hb]
    unfold fieldCurvatureTransform
    simp only [fieldSpinTransition_const_add]
  · rfl

lemma closedMagneticScalarCurvature_terminal_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0)
    (hT : ∀ av ∈ L ++ [(1, v)], 0 < av.1) (ζ : ℝ) (p : ℝ × ℝ) :
    closedMagneticScalarCurvature (L ++ [(1, v)]) hT ζ p =
      closedMagneticScalarCurvature L hL ζ p :=
  closedMagneticScalarCurvature_eq_of_value_const_add _ _ hT hL (v / 2)
    (fieldScalarValue_terminal_one L hL v) ζ p

lemma closedMagneticSquare_terminal_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0)
    (hT : ∀ av ∈ L ++ [(1, v)], 0 < av.1)
    (i : ℕ) (hi : i ≤ L.length) (ζ : ℝ) (p : ℝ × ℝ) :
    closedMagneticContinuation (L ++ [(1, v)])
      (magneticScalarSquareFourJet _ hT
        ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩).toMagneticContinuationJet ζ p =
    closedMagneticContinuation L
      (magneticScalarSquareFourJet L hL ⟨i, by omega⟩).toMagneticContinuationJet ζ p := by
  have hb := magneticScalarSlabBias_eq_of_value_const_add _ _ hT hL (v / 2)
    (fieldScalarValue_terminal_one L hL v) ζ p.1
  unfold closedMagneticContinuation
  split_ifs
  · rw [magneticScalarSlabContinuation_eq_jet _ hT,
      magneticScalarSlabContinuation_eq_jet _ hL]
    simp only [magneticScalarSlabContinuationJet, MagneticContinuationJet.transition,
      magneticScalarSquareFourJet_value]
    rw [fieldScalarSquares_terminal_one L hL v i hi, fieldScalarValue_terminal_one L hL v,
      fieldSpinTransition_const_add, hb]
  · rfl

end InvariantIsing

end

end OAI
