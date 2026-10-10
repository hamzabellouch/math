import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarSlab
import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatInverse

namespace OAI

/-! Spatial and variance derivatives of the genuine finite-tail inverse
curvature. The minimizing bias is constructed by coercivity, and no
inverse-regularity assumption remains in these statements. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabBias_continuousAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    ContinuousAt (magneticScalarSlabBias L ζ v) s := by
  have hmono := magneticScalarSlabMean_strictMono L hL hζ v
  apply tendsto_order.2
  constructor
  · intro l hl
    have hlt : magneticScalarSlabMean L ζ v l < s := by
      rw [← magneticScalarSlabMean_bias L hL hζ hs v]
      exact hmono hl
    filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2,
      Ioi_mem_nhds hlt] with t ht hlt'
    apply hmono.lt_iff_lt.mp
    rw [magneticScalarSlabMean_bias L hL hζ (abs_lt.mpr ht) v]
    exact hlt'
  · intro u hu
    have htu : s < magneticScalarSlabMean L ζ v u := by
      rw [← magneticScalarSlabMean_bias L hL hζ hs v]
      exact hmono hu
    filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2,
      Iio_mem_nhds htu] with t ht htu'
    apply hmono.lt_iff_lt.mp
    rw [magneticScalarSlabMean_bias L hL hζ (abs_lt.mpr ht) v]
    exact htu'

lemma magneticScalarSlabBias_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    let z := magneticScalarSlabBias L ζ v s
    let P := magneticLogCoshMeanJet L hL
    let F := fieldScalarValue L (fun x => Real.log (Real.cosh x))
    HasDerivAt (magneticScalarSlabBias L ζ v)
      (fieldCurvatureTransform ζ (Real.toNNReal v) F P.value P.first z)⁻¹ s := by
  apply HasDerivAt.of_local_left_inverse
    (magneticScalarSlabBias_continuousAt_spin L hL hζ hs v)
    (magneticScalarSlabMean_hasDerivAt L hL ζ v _)
    (magneticScalarSlab_curvature_pos L hL hζ v _).ne'
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2] with t ht
  exact magneticScalarSlabMean_bias L hL hζ (abs_lt.mpr ht) v

def magneticScalarInverseCurvature (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) : ℝ :=
  magneticHeatCurvature (magneticLogCoshMeanJet L hL)
    (fieldScalarValue L (fun x => Real.log (Real.cosh x))) ζ
    (v, magneticScalarSlabBias L ζ v s)

lemma magneticScalarInverseCurvature_eq (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) :
    magneticScalarInverseCurvature L hL ζ v s =
      fieldCurvatureTransform ζ (Real.toNNReal v)
        (fieldScalarValue L (fun x => Real.log (Real.cosh x)))
        (magneticLogCoshMeanJet L hL).value (magneticLogCoshMeanJet L hL).first
        (magneticScalarSlabBias L ζ v s) := by
  exact magneticHeatCurvature_eq _ _
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1 ζ _

lemma magneticScalarInverseCurvature_variance_hasDerivAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s v : ℝ}
    (hζ : 0 ≤ ζ) (hs : |s| < 1) (hv : 0 < v) :
    let P := magneticLogCoshMeanJet L hL
    let F := fieldScalarValue L (fun x => Real.log (Real.cosh x))
    let hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
    let J := P.transition P ζ (Real.toNNReal v) F hF.1 hF.2
      (hasDerivAt_fieldScalarLogCosh L hL)
    let z := magneticScalarSlabBias L ζ v s
    HasDerivAt (fun t => magneticScalarInverseCurvature L hL ζ t s)
      ((J.first z) ^ 2 / 2 * (J.third z / (J.first z) ^ 2 -
        (J.second z) ^ 2 / (J.first z) ^ 3) + ζ * (J.first z) ^ 2) v := by
  let P := magneticLogCoshMeanJet L hL
  let F := fieldScalarValue L (fun x => Real.log (Real.cosh x))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hd : ∀ z, HasDerivAt F (P.value z) z := hasDerivAt_fieldScalarLogCosh L hL
  have hq : (P.transition P ζ (Real.toNNReal v) F hF.1 hF.2 hd).first
      (magneticScalarSlabBias L ζ v s) ≠ 0 := by
    have hp := (magneticScalarSlab_curvature_pos L hL hζ v
      (magneticScalarSlabBias L ζ v s)).ne'
    simpa only [P, MagneticContinuationJet.transition, fieldTiltSpatial,
      fieldCurvatureTransform, pow_two] using hp
  apply magneticHeatInverse_curvature_hasDerivAt P F hF.1 hF.2 hd ζ (s := s) hv
    (magneticScalarSlabBias_continuousAt_variance L hL hζ hs hv) ?_ hq
  exact Eventually.of_forall fun t => by
    rw [← magneticScalarSlabMean_eq L hL ζ t]
    exact magneticScalarSlabMean_bias L hL hζ hs t

end InvariantIsing

end

end OAI
