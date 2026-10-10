import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeAtlasPatches
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationCutoff
import OAI.Geometry.TamingCompatibility.DifferentialForms.PlaneConvolution
import OAI.Geometry.TamingCompatibility.Functional.NormalInverseCompact

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory PlaneVariation Concentration Hermitian NormalMetricCalculus CoordinateOperator
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}

namespace ParametrixData

def concentrationCompact (D : ParametrixData J α ht p) : Set Space :=
  Prod.fst '' D.physicalCompact ∪ Prod.snd '' D.physicalCompact

omit [T2Space X] [CompactSpace X] in
lemma concentrationCompact_compact (D : ParametrixData J α ht p) : IsCompact D.concentrationCompact :=
  (D.physicalCompact_compact.image continuous_fst).union (D.physicalCompact_compact.image continuous_snd)

omit [T2Space X] [CompactSpace X] in
lemma concentrationCompact_target (D : ParametrixData J α ht p) :
    D.concentrationCompact ⊆ (extChartAt Model p).target := by
  rintro y (⟨xy,hxy,rfl⟩ | ⟨xy,hxy,rfl⟩)
  · exact D.chart.domain_subset (D.physicalCompact_domain hxy).1
  · exact D.chart.domain_subset (D.physicalCompact_domain hxy).2

omit [T2Space X] [CompactSpace X] in
lemma concentrationCompact_center (D : ParametrixData J α ht p) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) : q ∈ D.concentrationCompact := by
  have hx : (q,0) ∈ D.normalCompact := ⟨hq,Metric.mem_closedBall_self D.radius_pos.le⟩
  have he : D.normalChart (q,0) = (q,q) := by
    change (q,normalMap D.metricExtension D.frameExtension q 0) = (q,q)
    rw [normalMap_zero]
  exact Or.inl ⟨(q,q),⟨(q,0),hx,he⟩,rfl⟩

structure ConcentrationCutoff (D : ParametrixData J α ht p) where
  radius : ℝ
  positive : 0 < radius
  near : ∀ q ∈ Metric.closedBall (extChartAt Model p p) D.radius, ∀ y : Space,
    ‖y-q‖ ≤ radius → (q,y) ∈ D.physicalCompact

omit [T2Space X] [CompactSpace X] in
lemma concentrationCutoff_nonempty (D : ParametrixData J α ht p) : Nonempty D.ConcentrationCutoff := by
  obtain ⟨_,_,ε,hε,hnear⟩ := D.normal_inverse_near
  exact ⟨⟨ε,hε,fun q hq y hy => (hnear q hq y hy).1⟩⟩

def concentrationCutoff (D : ParametrixData J α ht p) : D.ConcentrationCutoff :=
  Classical.choice D.concentrationCutoff_nonempty

namespace ConcentrationCutoff
variable {D : ParametrixData J α ht p} (c : D.ConcentrationCutoff)

def bump : ContDiffBump (0 : Space) := ⟨c.radius/2,c.radius,by linarith [c.positive],by linarith [c.positive]⟩

omit [T2Space X] [CompactSpace X] in
lemma reflected_support {q : Space} (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius)
    (r : ℝ) : tsupport (fun y => cutKernel c.bump r (q-y)) ⊆ D.concentrationCompact := by
  have hs : tsupport (fun y => cutKernel c.bump r (q-y)) ⊆
      (fun y => q-y) ⁻¹' tsupport (cutKernel c.bump r) :=
    tsupport_comp_subset_preimage (f := fun y : Space => q-y)
      (cutKernel (c.bump : Space → ℝ) r) (continuous_const.sub continuous_id)
  intro y hy
  have hk : q-y ∈ tsupport (c.bump : Space → ℝ) := tsupport_mul_subset_left (hs hy)
  have hn : ‖y-q‖ ≤ c.radius := by
    rw [c.bump.tsupport_eq] at hk
    change dist (q-y) 0 ≤ c.radius at hk
    rwa [dist_zero_right,norm_sub_rev] at hk
  exact Or.inr ⟨(q,y),c.near q hq y hn,rfl⟩
end ConcentrationCutoff
end ParametrixData

variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def localConcentration (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) (r : ℝ) : Space → ℝ :=
  planeConvolution J α hs ht p.val (E p).concentrationCompact μ
    (cutKernel (E p).concentrationCutoff.bump r)

lemma localConcentration_smooth (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (p : A.centers) {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (localConcentration A J α hs ht E μ p r) :=
  planeConvolution_smooth J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ _ (cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff)
      (cutKernel_compact _ (E p).concentrationCutoff.bump.hasCompactSupport r)

def concentrationPatch (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) (r : ℝ) : X → ℝ :=
  scalarChartLift p.val (fun b => coordinatePartition A p b*localConcentration A J α hs ht E μ p r b)

lemma concentrationPatch_smooth (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (p : A.centers) {r : ℝ} (hr : 0 < r) : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (concentrationPatch A J α hs ht E μ p r) :=
  scalarChartLift_smooth p.val
    ((coordinatePartition_smooth_compact A p).1.mul (localConcentration_smooth A J α hs ht E μ p hr))
    (coordinatePartition_smooth_compact A p).2.mul_right
    (tsupport_mul_subset_left.trans ((coordinatePartition_tsupport A p).trans (coordinateSupport_subset A p)))

omit [T2Space X] [CompactSpace X] in
lemma concentrationPatch_apply (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) (r : ℝ) (x : X) : concentrationPatch A J α hs ht E μ p r x =
      A.partition p x*localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) := by
  by_cases hx : x ∈ (extChartAt Model p.val).source
  · simp only [concentrationPatch,scalarChartLift,ite_eq_left hx,coordinatePartition_apply A p hx]
  · have he : A.partition p x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.subordinate p h))
    simp only [concentrationPatch,scalarChartLift,ite_eq_right hx,he,zero_mul]

def globalConcentration (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (r : ℝ) : X → ℝ :=
  ∑ p : A.centers, concentrationPatch A J α hs ht E μ p r

lemma globalConcentration_smooth (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (globalConcentration A J α hs ht E μ r) := by
  classical
  exact contMDiff_finsetSum' (fun p _ => concentrationPatch_smooth A J α hs ht E μ p hr)

omit [T2Space X] [CompactSpace X] in
lemma localConcentration_nonneg (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) (r : ℝ) (b : Space) : 0 ≤ localConcentration A J α hs ht E μ p r b := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (E p).concentrationCutoff.bump.nonneg (rationalKernel_nonneg _ _)

omit [T2Space X] [CompactSpace X] in
lemma globalConcentration_nonneg (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (r : ℝ) (x : X) : 0 ≤ globalConcentration A J α hs ht E μ r x := by
  classical
  simp only [globalConcentration,Finset.sum_apply]
  apply Finset.sum_nonneg
  intro p _
  rw [concentrationPatch_apply]
  exact mul_nonneg (A.partition.nonneg _ _) (localConcentration_nonneg A J α hs ht E μ p r _)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory PlaneVariation Concentration Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def concentrationDensity (p : A.centers) (r : ℝ) (b : Space) :
    MetricUnit (hermitianMetric J α hs ht) → ℝ :=
  (unitChartDomain J α hs ht p.val (E p).concentrationCompact).indicator
    (fun u => unitChartArea J α hs ht p.val u *
      cutKernel (E p).concentrationCutoff.bump r (b-unitChartBase J α hs ht p.val u))

lemma concentrationDensity_integrable (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    [IsFiniteMeasure μ] (p : A.centers) {r : ℝ} (hr : 0 < r) (b : Space) :
    Integrable (concentrationDensity A J α hs ht E p r b) μ := by
  exact planeWeighted_integrable J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ _
    ((cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff).continuous.comp_continuousOn
      (continuousOn_const.sub (unitChartBase_continuousOn J α hs ht p.val (E p).concentrationCompact_target)))

omit [T2Space X] [CompactSpace X] in
lemma concentrationDensity_nonneg (p : A.centers) (r : ℝ) (b : Space)
    (u : MetricUnit (hermitianMetric J α hs ht)) :
    0 ≤ concentrationDensity A J α hs ht E p r b u := by
  apply indicator_nonneg _ u
  intro v _
  apply mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact cutKernel_nonneg _ (fun z => (E p).concentrationCutoff.bump.nonneg (x := z)) _ _

omit [CompactSpace X] in
lemma localConcentration_integral (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    (p : A.centers) {r : ℝ} (hr : 0 < r) (b : Space) :
    localConcentration A J α hs ht E μ p r b = ∫ u, concentrationDensity A J α hs ht E p r b u ∂μ := by
  exact planeMeasure_integral J α hs ht p.val (E p).concentrationCompact_compact
    (E p).concentrationCompact_target μ _
    ((cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff).continuous.comp
      (continuous_const.sub continuous_id))

omit [T2Space X] [CompactSpace X] in
lemma partition_center_ball
    (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
    (p : A.centers) {x : X} (hx : x ∈ tsupport (A.partition p)) :
    extChartAt Model p.val x ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius := by
  exact Metric.closedBall_subset_closedBall (by linarith [(E p).radius_pos])
    ((E p).source_image_subset ⟨x,hE p hx,rfl⟩)

omit [T2Space X] [CompactSpace X] in
lemma concentrationDensity_near (p : A.centers) {x : X}
    (hx : extChartAt Model p.val x ∈ Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hne : ‖extChartAt Model p.val u.val.proj-extChartAt Model p.val x‖ ≤
      (E p).concentrationCutoff.radius/2) (r : ℝ) :
    concentrationDensity A J α hs ht E p r (extChartAt Model p.val x) u =
      unitChartArea J α hs ht p.val u * rationalKernel r
        (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) := by
  have hnear : (extChartAt Model p.val x,extChartAt Model p.val u.val.proj) ∈ (E p).physicalCompact :=
    (E p).concentrationCutoff.near _ hx _ (hne.trans (by linarith [(E p).concentrationCutoff.positive]))
  have hbase : extChartAt Model p.val u.val.proj ∈ (E p).concentrationCompact :=
    Or.inr ⟨_,hnear,rfl⟩
  have hmem : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact :=
    ⟨extChartAt Model p.val u.val.proj,hbase,(extChartAt Model p.val).left_inv hu⟩
  have hone : (E p).concentrationCutoff.bump (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    change dist (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) 0 ≤ (E p).concentrationCutoff.radius/2
    rwa [dist_zero_right,norm_sub_rev]
  simp only [concentrationDensity,indicator_of_mem hmem,cutKernel,unitChartBase,hone,one_mul]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
