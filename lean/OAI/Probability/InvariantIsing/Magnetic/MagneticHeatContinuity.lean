import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarInverse
import OAI.Probability.InvariantIsing.Fields.FieldGaussianContinuity

namespace OAI

/-! Joint continuity of the finite Gaussian slab and its physical inverse
coordinates, including zero Gaussian variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma continuous_magneticHeatMean (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Continuous F) (hG : HasLinearGrowth F) (ζ : ℝ) :
    Continuous (magneticHeatMean P F ζ) := by
  obtain ⟨C, L, hC, hL, hB⟩ := hG
  obtain ⟨M, hM, bM⟩ := P.bValue
  have hP : Continuous P.value := continuous_iff_continuousAt.mpr
    fun z => (P.dValue z).continuousAt
  exact continuous_field_gaussian_tilt_average
    (hF.comp continuous_snd) (hP.comp continuous_snd) continuous_fst continuous_snd
    hC hL hM (fun _ z => by simpa only [Real.norm_eq_abs] using hB z)
    (fun _ z => bM z) ζ

lemma continuous_magneticHeatCurvature (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Continuous F) (hG : HasLinearGrowth F) (ζ : ℝ) :
    Continuous (magneticHeatCurvature P F ζ) := by
  obtain ⟨C, L, hC, hL, hB⟩ := hG
  obtain ⟨M, hM, bM⟩ := P.bFirst
  have hP : Continuous P.first := continuous_iff_continuousAt.mpr
    fun z => (P.dFirst z).continuousAt
  have hfirst : Continuous (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F P.first q.2) :=
    continuous_field_gaussian_tilt_average
      (hF.comp continuous_snd) (hP.comp continuous_snd) continuous_fst continuous_snd
      hC hL hM (fun _ z => by simpa only [Real.norm_eq_abs] using hB z)
      (fun _ z => bM z) ζ
  exact hfirst.add (((continuous_magneticHeatMean P.square F hF
    ⟨C, L, hC, hL, hB⟩ ζ).sub
      ((continuous_magneticHeatMean P F hF ⟨C, L, hC, hL, hB⟩ ζ).pow 2)).const_mul ζ)

lemma continuous_magneticScalarSlabMean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) :
    Continuous (fun q : ℝ × ℝ => magneticScalarSlabMean L ζ q.1 q.2) := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hc : Continuous (fieldScalarValue L (fun z => Real.log (Real.cosh z))) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hasDerivAt_fieldScalarLogCosh L hL z).continuousAt
  have he : (fun q : ℝ × ℝ => magneticScalarSlabMean L ζ q.1 q.2) =
      magneticHeatMean (magneticLogCoshMeanJet L hL)
        (fieldScalarValue L (fun z => Real.log (Real.cosh z))) ζ := by
    funext q
    exact magneticScalarSlabMean_eq L hL ζ q.1 q.2
  rw [he]
  exact continuous_magneticHeatMean _ _ hc hF.2 ζ

lemma continuousAt_parametric_strict_inverse (M b : ℝ → ℝ → ℝ)
    (hc : Continuous (fun q : ℝ × ℝ => M q.1 q.2))
    (hm : ∀ v, StrictMono (M v))
    (hroot : ∀ v s, |s| < 1 → M v (b v s) = s)
    {s v : ℝ} (hs : |s| < 1) :
    ContinuousAt (fun q : ℝ × ℝ => b q.1 q.2) (v, s) := by
  have hn : ∀ᶠ q : ℝ × ℝ in 𝓝 (v, s), |q.2| < 1 :=
    (isOpen_lt continuous_snd.abs continuous_const).mem_nhds hs
  apply tendsto_order.2
  constructor
  · intro l hl
    have hlt : M v l < s := by
      rw [← hroot v s hs]
      exact hm v hl
    have hlc : Continuous (fun q : ℝ × ℝ => M q.1 l) :=
      hc.comp (continuous_fst.prodMk continuous_const)
    have hN : ∀ᶠ q : ℝ × ℝ in 𝓝 (v, s), M q.1 l < q.2 :=
      (isOpen_lt hlc continuous_snd).mem_nhds hlt
    filter_upwards [hn, hN] with q hq hq'
    apply (hm q.1).lt_iff_lt.mp
    rw [hroot q.1 q.2 hq]
    exact hq'
  · intro u hu
    have htu : s < M v u := by
      rw [← hroot v s hs]
      exact hm v hu
    have huc : Continuous (fun q : ℝ × ℝ => M q.1 u) :=
      hc.comp (continuous_fst.prodMk continuous_const)
    have hN : ∀ᶠ q : ℝ × ℝ in 𝓝 (v, s), q.2 < M q.1 u :=
      (isOpen_lt continuous_snd huc).mem_nhds htu
    filter_upwards [hn, hN] with q hq hq'
    apply (hm q.1).lt_iff_lt.mp
    rw [hroot q.1 q.2 hq]
    exact hq'


lemma magneticScalarSlabBias_continuousAt_joint (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s v : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) :
    ContinuousAt (fun q : ℝ × ℝ => magneticScalarSlabBias L ζ q.1 q.2) (v, s) := by
  exact continuousAt_parametric_strict_inverse _ _
    (continuous_magneticScalarSlabMean L hL ζ)
    (magneticScalarSlabMean_strictMono L hL hζ)
    (fun v s hs => magneticScalarSlabMean_bias L hL hζ hs v) hs

end InvariantIsing

end

end OAI
