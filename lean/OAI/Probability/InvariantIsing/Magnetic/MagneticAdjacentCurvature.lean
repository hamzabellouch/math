import OAI.Probability.InvariantIsing.Magnetic.MagneticTailCongruence

namespace OAI

/-! Moving a nonnegative variance increment from a larger exponent to the
preceding smaller exponent decreases the actual inverse curvature. -/

noncomputable section
open Filter Set IsingPerceptron
open scoped NNReal Topology

namespace InvariantIsing

private lemma positive_cons {a : ℝ} (ha : 0 < a) (v : ℝ≥0)
    {L : List (ℝ × ℝ≥0)} (hL : ∀ av ∈ L, 0 < av.1) :
    ∀ av ∈ (a, v) :: L, 0 < av.1 := by
  intro av hav
  rcases List.mem_cons.mp hav with rfl | hav
  · exact ha
  · exact hL av hav

private lemma upper_cons {a : ℝ} (ha : a ≤ 1) (v : ℝ≥0)
    {L : List (ℝ × ℝ≥0)} (hL : ∀ av ∈ L, av.1 ≤ 1) :
    ∀ av ∈ (a, v) :: L, av.1 ≤ 1 := by
  intro av hav
  rcases List.mem_cons.mp hav with rfl | hav
  · exact ha
  · exact hL av hav

theorem magneticClosedCurvature_adjacent_transfer
    (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (x δ y : ℝ≥0) {η v s : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature ((a, x + δ) :: (b, y) :: L)
      (positive_cons ha _ (positive_cons (ha.trans_le hab) _ hL)) η (v, s) ≤
    closedMagneticScalarCurvature ((a, x) :: (b, δ + y) :: L)
      (positive_cons ha _ (positive_cons (ha.trans_le hab) _ hL)) η (v, s) := by
  have hb : 0 < b := ha.trans_le hab
  have ha1 : a ≤ 1 := hab.trans hb1
  let T := (b, y) :: L
  have hT : ∀ av ∈ T, 0 < av.1 := positive_cons hb y hL
  have hT1 : ∀ av ∈ T, av.1 ≤ 1 := upper_cons hb1 y hL1
  let A := (a, δ) :: T
  let B := (b, δ) :: T
  have hA : ∀ av ∈ A, 0 < av.1 := positive_cons ha δ hT
  have hB : ∀ av ∈ B, 0 < av.1 := positive_cons hb δ hT
  have hA1 : ∀ av ∈ A, av.1 ≤ 1 := upper_cons ha1 δ hT1
  have hB1 : ∀ av ∈ B, av.1 ≤ 1 := upper_cons hb1 δ hT1
  have hmid (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      closedMagneticScalarCurvature A hA a (0, u) ≤
        closedMagneticScalarCurvature B hB a (0, u) := by
    rw [closedMagneticScalarCurvature_cons_initial,
      closedMagneticScalarCurvature_cons_initial]
    exact magneticClosedCurvature_exponent_mono T hT hT1 ha.le hab hb1 δ.property hu
  have houter (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      closedMagneticScalarCurvature A hA a (x, u) ≤
        closedMagneticScalarCurvature B hB a (x, u) :=
    magneticClosedCurvature_compare_initial A B hA hB hA1 hB1 ha.le le_rfl ha1
      hmid x.property hu
  let N := (a, x + δ) :: T
  let O := (a, x) :: (b, δ + y) :: L
  have hN : ∀ av ∈ N, 0 < av.1 := positive_cons ha _ hT
  have hO : ∀ av ∈ O, 0 < av.1 := positive_cons ha _ (positive_cons hb _ hL)
  have hN1 : ∀ av ∈ N, av.1 ≤ 1 := upper_cons ha1 _ hT1
  have hO1 : ∀ av ∈ O, av.1 ≤ 1 := upper_cons ha1 _ (upper_cons hb1 _ hL1)
  have hsplit : fieldScalarValue ((a, x) :: B) (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue O (fun z => Real.log (Real.cosh z)) := by
    change gaussianOperator a x (fieldScalarValue ((b, δ) :: (b, y) :: L)
        (fun z => Real.log (Real.cosh z))) =
      gaussianOperator a x (fieldScalarValue ((b, δ + y) :: L)
        (fun z => Real.log (Real.cosh z)))
    rw [fieldScalarValue_same_exponent L hL b δ y]
  have hinit (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      closedMagneticScalarCurvature N hN η (0, u) ≤
        closedMagneticScalarCurvature O hO η (0, u) := by
    have hn := closedMagneticScalarCurvature_same_exponent T hT ha x δ η (0, u)
    have ho := closedMagneticScalarCurvature_eq_of_value_eq ((a, x) :: B) O
      (positive_cons ha x hB) hO hsplit η (0, u)
    rw [← hn, ← ho]
    rw [closedMagneticScalarCurvature_cons_initial,
      closedMagneticScalarCurvature_cons_initial]
    exact houter u hu
  exact magneticClosedCurvature_compare_initial N O hN hO hN1 hO1 hη le_rfl hη1
    hinit hv hs

end InvariantIsing

end

end OAI
