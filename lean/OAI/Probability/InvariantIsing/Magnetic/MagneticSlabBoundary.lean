import OAI.Probability.InvariantIsing.Magnetic.MagneticHeatContinuity
import OAI.Probability.InvariantIsing.Magnetic.MagneticCurvatureBound

namespace OAI

/-! The actual slab inverse curvature extends continuously to both spin
endpoints. The uniform bound by 1-s² gives joint boundary continuity in
the variance parameter without an asymptotic expansion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarInverseCurvature_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v s : ℝ) :
    0 < magneticScalarInverseCurvature L hL ζ v s := by
  rw [magneticScalarInverseCurvature_eq]
  exact magneticScalarSlab_curvature_pos L hL hζ v _

lemma magneticScalarInverseCurvature_le_spin_variance (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hs : |s| < 1) (v : ℝ) :
    magneticScalarInverseCurvature L hL ζ v s ≤ 1 - s ^ 2 := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet L hL
  obtain ⟨K, _, bK⟩ := P.bValue
  obtain ⟨C, _, bC⟩ := P.bFirst
  have hbound (y : ℝ) : P.first y + (P.value y) ^ 2 ≤ 1 := by
    have hh := fieldScalarLogCoshSecond_le_spin_variance L hL hL1 y
    change P.first y ≤ 1 - (P.value y) ^ 2 at hh
    linarith
  have hh := fieldCurvatureTransform_le_spin_variance hζ1 (Real.toNNReal v)
    hF.1 hF.2 P.mValue P.mFirst bK bC hbound (magneticScalarSlabBias L ζ v s)
  change _ ≤ 1 - (magneticScalarSlabMean L ζ v (magneticScalarSlabBias L ζ v s)) ^ 2 at hh
  rw [magneticScalarSlabMean_bias L hL hζ hs v] at hh
  rwa [magneticScalarInverseCurvature_eq]

lemma magneticScalarInverseCurvature_continuousAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s v : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) :
    ContinuousAt (fun q : ℝ × ℝ => magneticScalarInverseCurvature L hL ζ q.1 q.2) (v, s) := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hc : Continuous (fieldScalarValue L (fun z => Real.log (Real.cosh z))) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hasDerivAt_fieldScalarLogCosh L hL z).continuousAt
  have hh := continuous_magneticHeatCurvature (magneticLogCoshMeanJet L hL) _ hc hF.2 ζ
  have hb := magneticScalarSlabBias_continuousAt_joint L hL hζ (v := v) hs
  exact hh.continuousAt.comp' (continuousAt_fst.prodMk hb)

def closedMagneticScalarCurvature (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  if |q.2| < 1 then magneticScalarInverseCurvature L hL ζ q.1 q.2 else 0

lemma closedMagneticScalarCurvature_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (q : ℝ × ℝ) :
    0 ≤ closedMagneticScalarCurvature L hL ζ q := by
  unfold closedMagneticScalarCurvature
  split_ifs
  · exact (magneticScalarInverseCurvature_pos L hL hζ q.1 q.2).le
  · exact le_rfl

lemma closedMagneticScalarCurvature_le_spin_variance (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (q : ℝ × ℝ) (hq : q.2 ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature L hL ζ q ≤ 1 - q.2 ^ 2 := by
  unfold closedMagneticScalarCurvature
  split_ifs with hs
  · exact magneticScalarInverseCurvature_le_spin_variance L hL hL1 hζ hζ1 hs q.1
  · have hh := mul_nonneg (by linarith [hq.1] : 0 ≤ q.2 + 1)
      (by linarith [hq.2] : 0 ≤ 1 - q.2)
    nlinarith

lemma continuousOn_closedMagneticScalarCurvature (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ContinuousOn (closedMagneticScalarCurvature L hL ζ)
      (univ ×ˢ Icc (-1 : ℝ) 1) := by
  intro p hp
  by_cases hs : |p.2| < 1
  · have he : closedMagneticScalarCurvature L hL ζ =ᶠ[𝓝 p]
        (fun q => magneticScalarInverseCurvature L hL ζ q.1 q.2) := by
      filter_upwards [(isOpen_lt continuous_snd.abs continuous_const).mem_nhds hs] with q hq
      exact ite_eq_left hq
    exact ((magneticScalarInverseCurvature_continuousAt L hL hζ hs).congr_of_eventuallyEq he).continuousWithinAt
  · have hps : |p.2| = 1 := le_antisymm (abs_le.mpr hp.2) (le_of_not_gt hs)
    have hps2 : p.2 ^ 2 = 1 := by nlinarith [sq_abs p.2]
    have he : closedMagneticScalarCurvature L hL ζ p = 0 := ite_eq_right hs
    change Tendsto (closedMagneticScalarCurvature L hL ζ)
      (𝓝[univ ×ˢ Icc (-1 : ℝ) 1] p) (𝓝 _)
    rw [he]
    have hg : Tendsto (fun q : ℝ × ℝ => 1 - q.2 ^ 2)
        (𝓝[univ ×ˢ Icc (-1 : ℝ) 1] p) (𝓝 0) := by
      have hc : ContinuousWithinAt (fun q : ℝ × ℝ => 1 - q.2 ^ 2)
          (univ ×ˢ Icc (-1 : ℝ) 1) p := by fun_prop
      change Tendsto _ _ (𝓝 (1 - p.2 ^ 2)) at hc
      simpa only [hps2, sub_self] using hc
    apply squeeze_zero' (Eventually.of_forall (closedMagneticScalarCurvature_nonneg L hL hζ)) ?_ hg
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact closedMagneticScalarCurvature_le_spin_variance L hL hL1 hζ hζ1 q hq.2

end InvariantIsing

end

end OAI
