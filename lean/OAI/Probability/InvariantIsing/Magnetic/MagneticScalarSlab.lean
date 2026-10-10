import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatMean
import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarContinuation
import OAI.Probability.InvariantIsing.Magnetic.MagneticCoerciveRoot

namespace OAI

/-! Actual finite-tail Gaussian slabs have a unique bias at every
interior prescribed magnetization. These are the inverse coordinates used
in the finite-step parabolic comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScalarSlabMean (L : List (ℝ × ℝ≥0)) (ζ v : ℝ) (z : ℝ) : ℝ :=
  fieldSpinTransition ζ (Real.toNNReal v)
    (fieldScalarValue L (fun x => Real.log (Real.cosh x)))
    (fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh) z

def magneticScalarSlabBias (L : List (ℝ × ℝ≥0)) (ζ v s : ℝ) : ℝ :=
  Function.invFun (magneticScalarSlabMean L ζ v) s

lemma magneticScalarSlabMean_eq (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v z : ℝ) :
    magneticScalarSlabMean L ζ v z =
      magneticHeatMean (magneticLogCoshMeanJet L hL)
        (fieldScalarValue L (fun x => Real.log (Real.cosh x))) ζ (v, z) := by
  exact (magneticHeatMean_eq (magneticLogCoshMeanJet L hL) _
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1 ζ (v, z)).symm

lemma magneticScalarSlab_lower (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    |z| - Real.log 2 ≤ gaussianOperator ζ (Real.toNNReal v)
      (fieldScalarValue L (fun x => Real.log (Real.cosh x))) z := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hp : ∀ x, 1 * x + -Real.log 2 ≤
      fieldScalarValue L (fun y => Real.log (Real.cosh y)) x := by
    apply affine_le_fieldScalarValue L hL measurable_logCosh logCosh_linearGrowth
    intro x
    simpa only [one_mul, sub_eq_add_neg] using signed_bias_le_logcosh x
  have hm : ∀ x, (-1) * x + -Real.log 2 ≤
      fieldScalarValue L (fun y => Real.log (Real.cosh y)) x := by
    apply affine_le_fieldScalarValue L hL measurable_logCosh logCosh_linearGrowth
    intro x
    simpa only [Real.cosh_neg, neg_mul, one_mul, sub_eq_add_neg]
      using signed_bias_le_logcosh (-x)
  have hplus := affine_le_gaussianOperator hF.1 hF.2 hζ (Real.toNNReal v)
    1 (-Real.log 2) hp z
  have hminus := affine_le_gaussianOperator hF.1 hF.2 hζ (Real.toNNReal v)
    (-1) (-Real.log 2) hm z
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    simpa only [one_mul, sub_eq_add_neg] using hplus
  · rw [abs_of_nonpos hz]
    simpa only [neg_mul, one_mul, sub_eq_add_neg] using hminus

lemma magneticScalarSlab_value_hasDerivAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v z : ℝ) :
    HasDerivAt
      (gaussianOperator ζ (Real.toNNReal v)
        (fieldScalarValue L (fun x => Real.log (Real.cosh x))))
      (magneticScalarSlabMean L ζ v z) z := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet L hL
  obtain ⟨K, hK, bK⟩ := P.bValue
  exact hasDerivAt_gaussianOperator ζ (Real.toNNReal v) hF.1 hF.2 P.mValue hK bK
    (hasDerivAt_fieldScalarLogCosh L hL) z

lemma magneticScalarSlab_curvature_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    0 < fieldCurvatureTransform ζ (Real.toNNReal v)
      (fieldScalarValue L (fun x => Real.log (Real.cosh x)))
      (magneticLogCoshMeanJet L hL).value (magneticLogCoshMeanJet L hL).first z := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet L hL
  obtain ⟨K, _, bK⟩ := P.bFirst
  have hpos : ∀ x, 0 < P.first x := fieldScalarLogCoshSecond_pos L hL
  have hp := fieldSpinTransition_pos ζ (Real.toNNReal v) hF.1 hF.2 P.mFirst bK hpos z
  obtain ⟨D, _, bD⟩ := P.bValue
  have hs := fieldSpinTransition_square_le ζ (Real.toNNReal v) hF.1 hF.2 P.mValue bD z
  exact add_pos_of_pos_of_nonneg hp (mul_nonneg hζ (sub_nonneg.mpr hs))

lemma magneticScalarSlabMean_hasDerivAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v z : ℝ) :
    HasDerivAt (magneticScalarSlabMean L ζ v)
      (fieldCurvatureTransform ζ (Real.toNNReal v)
        (fieldScalarValue L (fun x => Real.log (Real.cosh x)))
        (magneticLogCoshMeanJet L hL).value (magneticLogCoshMeanJet L hL).first z) z := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet L hL
  obtain ⟨K, hK, bK⟩ := P.bValue
  obtain ⟨C, _, bC⟩ := P.bFirst
  have hd := hasDerivAt_fieldSpinTransition ζ (Real.toNNReal v)
    hF.1 hF.2 P.mValue P.mValue P.mFirst hK hK bK bK bC
    (hasDerivAt_fieldScalarLogCosh L hL) P.dValue z
  change HasDerivAt (fieldSpinTransition ζ (Real.toNNReal v) _ P.value)
    (fieldCurvatureTransform ζ (Real.toNNReal v) _ P.value P.first z) z
  simpa only [fieldCurvatureTransform, pow_two] using hd

lemma magneticScalarSlabMean_strictMono (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v : ℝ) :
    StrictMono (magneticScalarSlabMean L ζ v) := by
  apply strictMono_of_deriv_pos
  intro z
  rw [(magneticScalarSlabMean_hasDerivAt L hL ζ v z).deriv]
  exact magneticScalarSlab_curvature_pos L hL hζ v z

lemma magneticScalarSlabMean_bias (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    magneticScalarSlabMean L ζ v (magneticScalarSlabBias L ζ v s) = s := by
  apply Function.invFun_eq
  exact exists_mean_root_of_linear_lower (magneticScalarSlab_value_hasDerivAt L hL ζ v)
    (magneticScalarSlab_lower L hL hζ v) hs

lemma magneticScalarSlabBias_continuousAt_variance (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s v : ℝ}
    (hζ : 0 ≤ ζ) (hs : |s| < 1) (hv : 0 < v) :
    ContinuousAt (fun t => magneticScalarSlabBias L ζ t s) v := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet L hL
  have heq : (fun q : ℝ × ℝ => magneticScalarSlabMean L ζ q.1 q.2) =
      magneticHeatMean P (fieldScalarValue L (fun x => Real.log (Real.cosh x))) ζ := by
    funext q
    exact magneticScalarSlabMean_eq L hL ζ q.1 q.2
  apply parametric_bias_continuousAt (A := fun q => magneticScalarSlabMean L ζ q.1 q.2)
  · intro z
    have hc := (magneticHeatMean_hasFDerivAt P _ hF.1 hF.2
      (hasDerivAt_fieldScalarLogCosh L hL) ζ hv z).continuousAt
    rw [← heq] at hc
    have hp : ContinuousAt (fun t : ℝ => (t, z)) v :=
      continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp' (f := fun t : ℝ => (t, z)) (x := v) hc hp
  · exact Eventually.of_forall fun t => magneticScalarSlabMean_strictMono L hL hζ t
  · exact Eventually.of_forall fun t => magneticScalarSlabMean_bias L hL hζ hs t

end InvariantIsing

end

end OAI
