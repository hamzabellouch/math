import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricCoords
import OAI.Geometry.TamingCompatibility.Charts.FiniteCharts
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricDensity

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
namespace TamingCompatibility.ManifoldVolume
open MeasureTheory Set Bundle
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

def chartMetric (J : AlmostComplexStructure X) (α : TwoForm X) (p : X) (z : Space) :
    Space →L[ℝ] Space →L[ℝ] ℝ :=
  metricCoords J (invariantPart J α) p ((extChartAt Model p).symm z)

lemma chartMetric_apply (J : AlmostComplexStructure X) (α : TwoForm X) (p : X)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    chartMetric J α p z u v = associatedBilinear J (invariantPart J α)
      ((extChartAt Model p).symm z)
      ((trivializationAt Space (TangentSpace Model) p).symmL ℝ
        ((extChartAt Model p).symm z) u)
      ((trivializationAt Space (TangentSpace Model) p).symmL ℝ
        ((extChartAt Model p).symm z) v) := by
  let e := extChartAt Model p
  let te := trivializationAt Space (TangentSpace Model) p
  have hs : e.symm z ∈ (chartAt Space p).source := by
    simpa only [e, extChartAt_source] using e.map_target hz
  have ht : e.symm z ∈ te.baseSet := by
    simpa only [te, TangentBundle.trivializationAt_baseSet] using hs
  unfold chartMetric metricCoords
  rw [inCoordinates_apply_eq₂ ht ht (Set.mem_univ _)]
  change (Bundle.Trivial.trivialization X ℝ).linearMapAt ℝ (e.symm z) _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply,
    te.symmL_apply ht, te.symmL_apply ht]

lemma chartMetric_symm (J : AlmostComplexStructure X) (α : TwoForm X) (p : X)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    chartMetric J α p z u v = chartMetric J α p z v u := by
  rw [chartMetric_apply J α p hz, chartMetric_apply J α p hz]
  exact (invariantPart_isInvariant J α).associatedBilinear_symm _ _ _

lemma chartMetric_pos (J : AlmostComplexStructure X) (α : TwoForm X)
    (htame : Tames α J) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (u : Space) (hu : u ≠ 0) : 0 < chartMetric J α p z u u := by
  rw [chartMetric_apply J α p hz]
  apply (tames_invariantPart htame).associatedBilinear_pos
  let te := trivializationAt Space (TangentSpace Model) p
  have ht : (extChartAt Model p).symm z ∈ te.baseSet := by
    simpa only [te, TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt Model p).map_target hz
  intro h
  have hc := congrArg (te.continuousLinearMapAt ℝ ((extChartAt Model p).symm z)) h
  rw [te.continuousLinearMapAt_symmL ht, map_zero] at hc
  exact hu hc

def chartDensity (J : AlmostComplexStructure X) (α : TwoForm X) (p : X) (z : Space) : ℝ :=
  MetricDensity.density (MetricDensity.gram (stdOrthonormalBasis ℝ Space).toBasis
    (chartMetric J α p z))

lemma chartDensity_pos (J : AlmostComplexStructure X) (α : TwoForm X)
    (htame : Tames α J) (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target) :
    0 < chartDensity J α p z :=
  MetricDensity.density_pos _ (MetricDensity.gram_posDef _ _
    (chartMetric_symm J α p hz) (chartMetric_pos J α htame p hz))

lemma chartDensity_smooth (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : X) :
    ContDiffOn ℝ ∞ (chartDensity J α p) (extChartAt Model p).target := by
  apply MetricDensity.contDiffOn_gram_density
  · exact (hs.invariantPart J).metricCoords J p
  · intro z hz
    exact chartMetric_symm J α p hz
  · intro z hz
    exact chartMetric_pos J α htame p hz

lemma inverseChart_derivative (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    mfderiv Model Model (extChartAt Model p).symm z =
      (trivializationAt Space (TangentSpace Model) p).symmL ℝ
        ((extChartAt Model p).symm z) := by
  have hs : (extChartAt Model p).symm z ∈ (chartAt Space p).source := by
    simpa only [extChartAt_source] using (extChartAt Model p).map_target hz
  rw [TangentBundle.symmL_trivializationAt hs, (extChartAt Model p).right_inv hz]
  simp only [Model, modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ]

lemma chartMetric_derivative (J : AlmostComplexStructure X) (α : TwoForm X) (p : X)
    {z : Space} (hz : z ∈ (extChartAt Model p).target) (u v : Space) :
    chartMetric J α p z u v = associatedBilinear J (invariantPart J α)
      ((extChartAt Model p).symm z)
      (mfderiv Model Model (extChartAt Model p).symm z u)
      (mfderiv Model Model (extChartAt Model p).symm z v) := by
  rw [chartMetric_apply J α p hz, inverseChart_derivative p hz]
  rfl

lemma inverseChart_comp_transition (p q : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target)
    (hq : (extChartAt Model p).symm z ∈ (extChartAt Model q).source) :
    mfderiv Model Model (extChartAt Model q).symm
        ((extChartAt Model q) ((extChartAt Model p).symm z)) ∘L
      fderiv ℝ ((extChartAt Model q) ∘ (extChartAt Model p).symm) z =
        mfderiv Model Model (extChartAt Model p).symm z := by
  have hp' : MDifferentiableAt Model Model (extChartAt Model p).symm z :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz)).mdifferentiableAt (by simp)
  have hq' : MDifferentiableAt Model Model (extChartAt Model q)
      ((extChartAt Model p).symm z) := by
    apply (contMDiffOn_extChartAt (I := Model) (x := q) (n := ∞)).contMDiffAt _
      |>.mdifferentiableAt (by simp)
    simpa only [extChartAt_source] using (isOpen_extChartAt_source q).mem_nhds hq
  erw [← mfderiv_eq_fderiv, mfderiv_comp z hq' hp', ← ContinuousLinearMap.comp_assoc]
  have hinv := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := Model) hq
  simp only [Model, modelWithCornersSelf_coe, Set.range_id, mfderivWithin_univ] at hinv
  erw [hinv]
  rfl

lemma chartMetric_transition (J : AlmostComplexStructure X) (α : TwoForm X) (p q : X)
    {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (hq : (extChartAt Model p).symm z ∈ (extChartAt Model q).source) :
    chartMetric J α p z = MetricDensity.pullMetric
      (chartMetric J α q ((extChartAt Model q) ((extChartAt Model p).symm z)))
      (fderiv ℝ ((extChartAt Model q) ∘ (extChartAt Model p).symm) z) := by
  ext u v
  rw [MetricDensity.pullMetric_apply, chartMetric_derivative J α p hz,
    chartMetric_derivative J α q ((extChartAt Model q).map_source hq)]
  have hd := inverseChart_comp_transition p q hz hq
  have hu := congrArg (fun L : Space →L[ℝ] Space => L u) hd
  have hv := congrArg (fun L : Space →L[ℝ] Space => L v) hd
  change (mfderiv Model Model (extChartAt Model q).symm
    ((extChartAt Model q) ((extChartAt Model p).symm z)))
    ((fderiv ℝ ((extChartAt Model q) ∘ (extChartAt Model p).symm) z) u) = _ at hu
  change (mfderiv Model Model (extChartAt Model q).symm
    ((extChartAt Model q) ((extChartAt Model p).symm z)))
    ((fderiv ℝ ((extChartAt Model q) ∘ (extChartAt Model p).symm) z) v) = _ at hv
  erw [hu, hv, (extChartAt Model q).left_inv hq]
  rfl

lemma chartDensity_transition (J : AlmostComplexStructure X) (α : TwoForm X) (p q : X)
    {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (hq : (extChartAt Model p).symm z ∈ (extChartAt Model q).source) :
    chartDensity J α p z =
      |LinearMap.det (fderiv ℝ ((extChartAt Model q) ∘
        (extChartAt Model p).symm) z).toLinearMap| *
      chartDensity J α q ((extChartAt Model q) ((extChartAt Model p).symm z)) := by
  unfold chartDensity
  rw [chartMetric_transition J α p q hz hq, MetricDensity.density_pullMetric]

def chartOverlap (p q : X) : Set Space :=
  (extChartAt Model p).target ∩ (extChartAt Model p).symm ⁻¹' (extChartAt Model q).source

def transition (p q : X) : Space → Space :=
  (extChartAt Model q) ∘ (extChartAt Model p).symm

omit [IsManifold Model ∞ X] in
lemma chartOverlap_open (p q : X) : IsOpen (chartOverlap p q) :=
  (continuousOn_extChartAt_symm p).isOpen_inter_preimage
    (isOpen_extChartAt_target p) (isOpen_extChartAt_source q)

omit [IsManifold Model ∞ X] in
lemma transition_injOn (p q : X) : Set.InjOn (transition p q) (chartOverlap p q) := by
  intro z hz w hw he
  apply (extChartAt Model p).symm.injOn hz.1 hw.1
  exact (extChartAt Model q).injOn hz.2 hw.2 he

omit [IsManifold Model ∞ X] in
lemma transition_image_overlap (p q : X) :
    transition p q '' chartOverlap p q = chartOverlap q p := by
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨(extChartAt Model q).map_source hz.2, ?_⟩
    change (extChartAt Model q).symm ((extChartAt Model q)
      ((extChartAt Model p).symm z)) ∈ (extChartAt Model p).source
    rw [(extChartAt Model q).left_inv hz.2]
    exact (extChartAt Model p).map_target hz.1
  · intro hw
    refine ⟨transition q p w, ⟨(extChartAt Model p).map_source hw.2, ?_⟩, ?_⟩
    · change (extChartAt Model p).symm ((extChartAt Model p)
        ((extChartAt Model q).symm w)) ∈ (extChartAt Model q).source
      rw [(extChartAt Model p).left_inv hw.2]
      exact (extChartAt Model q).map_target hw.1
    · dsimp only [transition, Function.comp_apply]
      rw [(extChartAt Model p).left_inv hw.2, (extChartAt Model q).right_inv hw.1]

lemma transition_differentiableAt (p q : X) {z : Space} (hz : z ∈ chartOverlap p q) :
    DifferentiableAt ℝ (transition p q) z := by
  have hp' : MDifferentiableAt Model Model (extChartAt Model p).symm z :=
    ((contMDiffOn_extChartAt_symm (n := ∞) p).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hz.1)).mdifferentiableAt (by simp)
  have hq' : MDifferentiableAt Model Model (extChartAt Model q)
      ((extChartAt Model p).symm z) := by
    apply (contMDiffOn_extChartAt (I := Model) (x := q) (n := ∞)).contMDiffAt _
      |>.mdifferentiableAt (by simp)
    simpa only [extChartAt_source] using (isOpen_extChartAt_source q).mem_nhds hz.2
  exact mdifferentiableAt_iff_differentiableAt.mp (hq'.comp z hp')

lemma integral_overlap (J : AlmostComplexStructure X) (α : TwoForm X)
    (p q : X) (f : X → ℝ) :
    (∫ z in chartOverlap p q, chartDensity J α p z * f ((extChartAt Model p).symm z)) =
      ∫ w in chartOverlap q p, chartDensity J α q w * f ((extChartAt Model q).symm w) := by
  rw [← transition_image_overlap p q,
    integral_image_eq_integral_abs_det_fderiv_smul volume (chartOverlap_open p q).measurableSet
      (fun z hz => (transition_differentiableAt p q hz).hasFDerivAt.hasFDerivWithinAt)
      (transition_injOn p q)]
  apply setIntegral_congr_fun (chartOverlap_open p q).measurableSet
  intro z hz
  dsimp only
  rw [smul_eq_mul, chartDensity_transition J α p q hz.1 hz.2]
  dsimp only [transition, Function.comp_apply]
  rw [(extChartAt Model q).left_inv hz.2]
  ring

variable [T2Space X] [CompactSpace X]
variable (A : ManifoldLocalization.FiniteCharts X)

def chartWeight (J : AlmostComplexStructure X) (α : TwoForm X) (p : A.centers) : Space → ℝ :=
  (extChartAt Model p.val).target.indicator (fun z =>
    A.partition p ((extChartAt Model p.val).symm z) * chartDensity J α p.val z)

omit [T2Space X] in
lemma chartWeight_smooth_compact (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : A.centers) :
    ContDiff ℝ ∞ (chartWeight A J α p) ∧ HasCompactSupport (chartWeight A J α p) := by
  apply ManifoldLocalization.smooth_indicator_of_compact (isOpen_extChartAt_target p.val)
    (ManifoldLocalization.coordinateSupport_compact A p)
    (ManifoldLocalization.coordinateSupport_subset A p)
  · have hρ : ContDiffOn ℝ ∞
        (fun z => A.partition p ((extChartAt Model p.val).symm z))
        (extChartAt Model p.val).target := by
      exact (A.partition p).contMDiff.comp_contMDiffOn
        (contMDiffOn_extChartAt_symm p.val) |>.contDiffOn
    exact hρ.mul (chartDensity_smooth J α hs htame p.val)
  · intro z hz hK
    have hn : (extChartAt Model p.val).symm z ∉ tsupport (A.partition p) := by
      intro h
      exact hK ⟨(extChartAt Model p.val).symm z,h,(extChartAt Model p.val).right_inv hz⟩
    rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]

omit [T2Space X] [CompactSpace X] in
lemma chartWeight_nonneg (J : AlmostComplexStructure X) (α : TwoForm X)
    (p : A.centers) (z : Space) : 0 ≤ chartWeight A J α p z := by
  apply Set.indicator_nonneg
  intro y _
  exact mul_nonneg (A.partition.nonneg _ _) (Real.sqrt_nonneg _)

variable [MeasurableSpace X] [BorelSpace X]

def chartInverse (p : X) (z : Space) : X := by
  classical
  exact if z ∈ (extChartAt Model p).target then (extChartAt Model p).symm z else p

omit [T2Space X] [CompactSpace X] [IsManifold Model ∞ X] in
lemma chartInverse_measurable (p : X) : Measurable (chartInverse p) := by
  classical
  exact (continuousOn_extChartAt_symm p).measurable_piecewise
    continuousOn_const (isOpen_extChartAt_target p).measurableSet

def chartMeasure (J : AlmostComplexStructure X) (α : TwoForm X) (p : A.centers) :
    Measure X := Measure.map (chartInverse p.val)
      (volume.withDensity (fun z => ENNReal.ofReal (chartWeight A J α p z)))

omit [T2Space X] [BorelSpace X] in
lemma chartMeasure_finite (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : A.centers) :
    IsFiniteMeasure (chartMeasure A J α p) := by
  have hw := chartWeight_smooth_compact A J α hs htame p
  have hi : Integrable (chartWeight A J α p) volume :=
    hw.1.continuous.integrable_of_hasCompactSupport hw.2
  have hf := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (chartWeight_nonneg A J α p))).mp hi.hasFiniteIntegral
  have := isFiniteMeasure_withDensity hf.ne
  exact inferInstanceAs (IsFiniteMeasure (Measure.map (chartInverse p.val)
    (volume.withDensity (fun z => ENNReal.ofReal (chartWeight A J α p z)))))

def geometricVolume (J : AlmostComplexStructure X) (α : TwoForm X) : Measure X :=
  ∑ p : A.centers, chartMeasure A J α p

omit [T2Space X] [BorelSpace X] in
lemma geometricVolume_finite (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) :
    IsFiniteMeasure (geometricVolume A J α) := by
  have (p : A.centers) := chartMeasure_finite A J α hs htame p
  unfold geometricVolume
  infer_instance

omit [T2Space X] in
lemma integral_chartMeasure (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : A.centers)
    (f : X → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂chartMeasure A J α p) =
      ∫ z, chartWeight A J α p z * f ((extChartAt Model p.val).symm z) := by
  rw [chartMeasure, integral_map (chartInverse_measurable p.val).aemeasurable
    hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun z => ENNReal.ofReal (chartWeight A J α p z)) from
      ENNReal.measurable_ofReal.comp
        (chartWeight_smooth_compact A J α hs htame p).1.continuous.measurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only
  rw [ENNReal.toReal_ofReal (chartWeight_nonneg A J α p z), smul_eq_mul]
  by_cases hz : z ∈ (extChartAt Model p.val).target
  · simp only [chartInverse, ite_eq_left hz]
  · simp only [chartWeight, Set.indicator_of_notMem hz, zero_mul]

end TamingCompatibility.ManifoldVolume

end

end OAI
