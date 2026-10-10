import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartMetric

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
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]

def coordinateIntegrand (J : AlmostComplexStructure X) (α : TwoForm X)
    (p : X) (f : X → ℝ) : Space → ℝ :=
  (extChartAt Model p).target.indicator
    (fun z => chartDensity J α p z * f ((extChartAt Model p).symm z))

lemma continuous_indicator_compact {E F : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace F] [Zero F] {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {f : E → F}
    (hf : ContinuousOn f U) (hz : ∀ x ∈ U, x ∉ K → f x = 0) :
    Continuous (U.indicator f) ∧ HasCompactSupport (U.indicator f) := by
  have hs : Function.support (U.indicator f) ⊆ K := by
    intro x hx
    by_contra h
    by_cases hu : x ∈ U
    · exact hx (by rw [indicator_of_mem hu]; exact hz x hu h)
    · exact hx (indicator_of_notMem hu f)
  refine ⟨?_, HasCompactSupport.of_support_subset_isCompact hK hs⟩
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hu : x ∈ U
  · apply ((hf x hu).continuousAt (hU.mem_nhds hu)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hu] with y hy
    exact indicator_of_mem hy f
  · have hx : x ∉ K := fun h => hu (hKU h)
    apply (show ContinuousAt (fun _ : E => (0 : F)) x from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact Function.notMem_support.mp (fun h => hy (hs h))

omit [T2Space X] in
lemma coordinateIntegrand_continuous_compact (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : X) (f : X → ℝ)
    (hf : Continuous f) (hfp : tsupport f ⊆ (extChartAt Model p).source) :
    Continuous (coordinateIntegrand J α p f) ∧
      HasCompactSupport (coordinateIntegrand J α p f) := by
  have hK : IsCompact ((extChartAt Model p) '' tsupport f) :=
    (isClosed_tsupport f).isCompact.image_of_continuousOn
      ((continuousOn_extChartAt p).mono hfp)
  apply continuous_indicator_compact (isOpen_extChartAt_target p) hK
  · rintro z ⟨x,hx,rfl⟩
    exact (extChartAt Model p).map_source (hfp hx)
  · exact (chartDensity_smooth J α hs htame p).continuousOn.mul
      (hf.comp_continuousOn (continuousOn_extChartAt_symm p))
  · intro z hz hn
    have hn' : (extChartAt Model p).symm z ∉ tsupport f := by
      intro h
      exact hn ⟨(extChartAt Model p).symm z,h,(extChartAt Model p).right_inv hz⟩
    rw [image_eq_zero_of_notMem_tsupport hn', mul_zero]

omit [T2Space X] in
lemma coordinateIntegrand_integrable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : X) (f : X → ℝ)
    (hf : Continuous f) (hfp : tsupport f ⊆ (extChartAt Model p).source) :
    Integrable (coordinateIntegrand J α p f) := by
  have h := coordinateIntegrand_continuous_compact J α hs htame p f hf hfp
  exact h.1.integrable_of_hasCompactSupport h.2

omit [T2Space X] [CompactSpace X] in

lemma integral_coordinateIntegrand_eq (J : AlmostComplexStructure X) (α : TwoForm X)
    (p q : X) (f : X → ℝ)
    (hfp : tsupport f ⊆ (extChartAt Model p).source)
    (hfq : tsupport f ⊆ (extChartAt Model q).source) :
    (∫ z, coordinateIntegrand J α p f z) = ∫ z, coordinateIntegrand J α q f z := by
  have h (a b : X) (hb : tsupport f ⊆ (extChartAt Model b).source) :
      coordinateIntegrand J α a f = (chartOverlap a b).indicator
        (fun z => chartDensity J α a z * f ((extChartAt Model a).symm z)) := by
    funext z
    by_cases ha : z ∈ (extChartAt Model a).target
    · by_cases hba : (extChartAt Model a).symm z ∈ (extChartAt Model b).source
      · have hab : z ∈ chartOverlap a b := ⟨ha,hba⟩
        simp only [coordinateIntegrand, indicator_of_mem ha, indicator_of_mem hab]
      · have hn : (extChartAt Model a).symm z ∉ tsupport f := fun h => hba (hb h)
        have hab : z ∉ chartOverlap a b := fun h => hba h.2
        simp only [coordinateIntegrand, indicator_of_mem ha, indicator_of_notMem hab,
          image_eq_zero_of_notMem_tsupport hn, mul_zero]
    · have hab : z ∉ chartOverlap a b := fun h => ha h.1
      simp only [coordinateIntegrand, indicator_of_notMem ha, indicator_of_notMem hab]
  rw [h p q hfq, h q p hfp, integral_indicator (chartOverlap_open p q).measurableSet,
    integral_indicator (chartOverlap_open q p).measurableSet]
  exact integral_overlap J α p q f

variable (A : ManifoldLocalization.FiniteCharts X)
variable [MeasurableSpace X] [BorelSpace X]

omit [T2Space X] in
lemma integral_chartMeasure_coordinate (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (q : A.centers)
    (f : X → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂chartMeasure A J α q) =
      ∫ z, coordinateIntegrand J α q.val (fun x => A.partition q x * f x) z := by
  rw [integral_chartMeasure A J α hs htame q f hf]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ (extChartAt Model q.val).target
  · simp only [chartWeight, coordinateIntegrand, indicator_of_mem hz]
    ring
  · simp only [chartWeight, coordinateIntegrand, indicator_of_notMem hz, zero_mul]

omit [T2Space X] in

theorem integral_geometricVolume_coordinate (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (htame : Tames α J) (p : X)
    (f : X → ℝ) (hf : Continuous f) (hfp : tsupport f ⊆ (extChartAt Model p).source) :
    (∫ x, f x ∂geometricVolume A J α) =
      ∫ z in (extChartAt Model p).target,
        chartDensity J α p z * f ((extChartAt Model p).symm z) := by
  have hc (q : A.centers) : Continuous (fun x => A.partition q x * f x) :=
    (A.partition q).contMDiff.continuous.mul hf
  have hp (q : A.centers) : tsupport (fun x => A.partition q x * f x) ⊆
      (extChartAt Model p).source := (tsupport_mul_subset_right).trans hfp
  have hq (q : A.centers) : tsupport (fun x => A.partition q x * f x) ⊆
      (extChartAt Model q.val).source := (tsupport_mul_subset_left).trans (A.subordinate q)
  have hmi (q : A.centers) : Integrable f (chartMeasure A J α q) := by
    let := chartMeasure_finite A J α hs htame q
    exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  rw [geometricVolume, integral_finsetSum_measure (fun q _ => hmi q)]
  simp_rw [integral_chartMeasure_coordinate A J α hs htame _ f hf]
  have he (q : A.centers) := integral_coordinateIntegrand_eq J α q.val p
    (fun x => A.partition q x * f x) (hq q) (hp q)
  simp_rw [he]
  rw [← integral_finsetSum _ (fun q _ =>
    coordinateIntegrand_integrable J α hs htame p _ (hc q) (hp q))]
  rw [← integral_indicator (isOpen_extChartAt_target p).measurableSet]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ (extChartAt Model p).target
  · simp only [coordinateIntegrand, indicator_of_mem hz]
    rw [← Finset.mul_sum, ← Finset.sum_mul, ManifoldLocalization.partition_sum, one_mul]
  · simp only [coordinateIntegrand, indicator_of_notMem hz, Finset.sum_const_zero]

end TamingCompatibility.ManifoldVolume

end

end OAI
