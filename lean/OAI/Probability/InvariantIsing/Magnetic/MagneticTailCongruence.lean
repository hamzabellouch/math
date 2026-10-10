import OAI.Probability.InvariantIsing.Fields.FieldGaussianSemigroup
import OAI.Probability.InvariantIsing.Magnetic.MagneticTailComparison

namespace OAI

/-! Equality of backward field values gives equality of their actual
inverse curvatures. In particular, an equal-exponent Gaussian step may be
split without changing the inverse-coordinate model. -/

noncomputable section
open Filter Set IsingPerceptron
open scoped NNReal Topology

namespace InvariantIsing

lemma closedMagneticScalarCurvature_cons_initial (av : ℝ × ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ bv ∈ av :: L, 0 < bv.1) (ζ s : ℝ) :
    closedMagneticScalarCurvature (av :: L) hL ζ (0, s) =
      closedMagneticScalarCurvature L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        av.1 ((av.2 : ℝ), s) := by
  by_cases hs : |s| < 1
  · simp only [closedMagneticScalarCurvature, hs, ite_true]
    exact magneticScalarInverseCurvature_cons_initial av L hL ζ s
  · simp only [closedMagneticScalarCurvature, hs, ite_false]

lemma magneticClosedCurvature_exponent_mono (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ η : ℝ} (hζ : 0 ≤ ζ) (hζη : ζ ≤ η) (hη1 : η ≤ 1)
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature L hL ζ (v, s) ≤
      closedMagneticScalarCurvature L hL η (v, s) := by
  apply magneticClosedCurvature_compare_initial L L hL hL hL1 hL1 hζ hζη hη1 ?_ hv hs
  intro u _
  exact (closedMagneticScalarCurvature_initial L hL ζ η u).le

lemma magneticLogCoshMeanJet_eq_of_value_eq (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue M (fun z => Real.log (Real.cosh z))) :
    magneticLogCoshMeanJet L hL = magneticLogCoshMeanJet M hM := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  have hl := hasDerivAt_fieldScalarLogCosh L hL z
  rw [he] at hl
  exact hl.unique (hasDerivAt_fieldScalarLogCosh M hM z)

lemma magneticScalarSlabBias_eq_of_value_eq (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue M (fun z => Real.log (Real.cosh z))) (ζ v : ℝ) :
    magneticScalarSlabBias L ζ v = magneticScalarSlabBias M ζ v := by
  have hJ := magneticLogCoshMeanJet_eq_of_value_eq L M hL hM he
  have hm : magneticScalarSlabMean L ζ v = magneticScalarSlabMean M ζ v := by
    funext z
    rw [magneticScalarSlabMean_eq L hL, magneticScalarSlabMean_eq M hM, hJ, he]
  unfold magneticScalarSlabBias
  rw [hm]

lemma closedMagneticScalarCurvature_eq_of_value_eq (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue M (fun z => Real.log (Real.cosh z))) (ζ : ℝ) (p : ℝ × ℝ) :
    closedMagneticScalarCurvature L hL ζ p = closedMagneticScalarCurvature M hM ζ p := by
  have hJ := magneticLogCoshMeanJet_eq_of_value_eq L M hL hM he
  have hb := magneticScalarSlabBias_eq_of_value_eq L M hL hM he ζ p.1
  unfold closedMagneticScalarCurvature
  split_ifs
  · unfold magneticScalarInverseCurvature
    rw [hJ, he, hb]
  · rfl

lemma fieldScalarValue_same_exponent (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (v w : ℝ≥0) :
    fieldScalarValue ((ζ, v) :: (ζ, w) :: L) (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue ((ζ, v + w) :: L) (fun z => Real.log (Real.cosh z)) := by
  funext z
  exact gaussianOperator_same_exponent ζ v w
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).2 z

lemma closedMagneticScalarCurvature_same_exponent (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 < ζ)
    (v w : ℝ≥0) (η : ℝ) (p : ℝ × ℝ) :
    closedMagneticScalarCurvature ((ζ, v) :: (ζ, w) :: L)
      (by intro av hav; simp only [List.mem_cons] at hav; rcases hav with rfl | rfl | hav
          · exact hζ
          · exact hζ
          · exact hL av hav) η p =
    closedMagneticScalarCurvature ((ζ, v + w) :: L)
      (by intro av hav; rcases List.mem_cons.mp hav with rfl | hav
          · exact hζ
          · exact hL av hav) η p :=
  closedMagneticScalarCurvature_eq_of_value_eq _ _ _ _
    (fieldScalarValue_same_exponent L hL ζ v w) η p

end InvariantIsing

end

end OAI
