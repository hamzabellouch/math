import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.PhysicalProfile
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationChart

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory PlaneVariation Concentration Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma compact_chart_profile_bound (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : X, x ∈ (extChartAt Model p).source →
      extChartAt Model p x ∈ K → ∀ u : MetricUnit (hermitianMetric J α hs ht),
      u ∈ unitChartDomain J α hs ht p K → ∀ r : ℝ, 0 < r →
      ((1+‖extChartAt Model p x-unitChartBase J α hs ht p u‖/r)⁻¹)^6 ≤
        physicalProfile J α hs ht (L*r) x u.val.proj := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨L₀,hL₀⟩ := chartInverse_compact_lipschitz J α hs ht p K hK hKT
  let L : ℝ := (L₀:ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L,hL,fun x hx hxK u hu r hr => ?_⟩
  have humem := unitChart_mem J α hs ht p hKT hu
  have hphys := hL₀.dist_le_mul _ hxK _ humem.2
  change dist ((extChartAt Model p).symm (extChartAt Model p x))
    ((extChartAt Model p).symm (unitChartBase J α hs ht p u)) ≤ _ at hphys
  simp only [unitChartBase] at hphys
  rw [(extChartAt Model p).left_inv hx,(extChartAt Model p).left_inv humem.1,dist_eq_norm] at hphys
  have htransport : dist x u.val.proj ≤ L*‖extChartAt Model p x-unitChartBase J α hs ht p u‖ :=
    hphys.trans (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (norm_nonneg _))
  have hdiv : dist x u.val.proj/(L*r) ≤ ‖extChartAt Model p x-unitChartBase J α hs ht p u‖/r := by
    apply (div_le_iff₀ (mul_pos hL hr)).mpr
    calc
      _ ≤ L*‖extChartAt Model p x-unitChartBase J α hs ht p u‖ := htransport
      _ = _ := by field_simp
  change _ ≤ ((1+dist x u.val.proj/(L*r))⁻¹)^6
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) (by linarith)) 6

include hE in
omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma concentrationDensity_physical_bound (p : A.centers) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 < L ∧ ∀ x : X, x ∈ tsupport (A.partition p) →
      ∀ r : ℝ, 0 < r → ∀ u : MetricUnit (hermitianMetric J α hs ht),
      concentrationDensity A J α hs ht E p r (extChartAt Model p.val x) u ≤
        (C/r^2)*physicalProfile J α hs ht (L*r) x u.val.proj := by
  obtain ⟨L,hL,hprofile⟩ := compact_chart_profile_bound J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  obtain ⟨_,P,_,hP,harea⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  refine ⟨8*P,L,by positivity,hL,fun x hx r hr u => ?_⟩
  by_cases hu : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  · have hxK := (E p).concentrationCompact_center (partition_center_ball A J α ht E hE p hx)
    have hp := hprofile x (A.subordinate p hx) hxK u hu r hr
    rw [concentrationDensity,indicator_of_mem hu]
    calc
      _ ≤ P*rationalKernel r (extChartAt Model p.val x-unitChartBase J α hs ht p.val u) :=
        mul_le_mul (harea u hu).2
          (cutKernel_le _ (fun z => (E p).concentrationCutoff.bump.le_one (x := z)) _ _)
          (cutKernel_nonneg _ (fun z => (E p).concentrationCutoff.bump.nonneg (x := z)) _ _) hP.le
      _ ≤ P*((8/r^2)*((1+‖extChartAt Model p.val x-unitChartBase J α hs ht p.val u‖/r)⁻¹)^6) :=
        mul_le_mul_of_nonneg_left (rationalKernel_profile hr _) hP.le
      _ ≤ P*((8/r^2)*physicalProfile J α hs ht (L*r) x u.val.proj) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity)) hP.le
      _ = _ := by ring
  · rw [concentrationDensity,indicator_of_notMem hu]
    exact mul_nonneg (by positivity) (physicalProfile_nonneg J α hs ht _ _ _)

include hE in
omit [MeasurableSpace X] [BorelSpace X] in
lemma localConcentration_physical_bound
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] (p : A.centers) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 < L ∧ ∀ x : X, x ∈ tsupport (A.partition p) →
      ∀ r : ℝ, 0 < r → localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) ≤
        (C/r^2)*physicalProfileMass J α hs ht μ (L*r) x := by
  obtain ⟨C,L,hC,hL,hbound⟩ := concentrationDensity_physical_bound A J α hs ht E hE p
  refine ⟨C,L,hC,hL,fun x hx r hr => ?_⟩
  rw [localConcentration_integral A J α hs ht E μ p hr,physicalProfileMass,←integral_const_mul]
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hmap : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => (x,u.val.proj)) := continuous_const.prodMk hp
  have hh := (physicalProfile_continuous J α hs ht (mul_pos hL hr)).comp hmap
  exact integral_mono (concentrationDensity_integrable A J α hs ht E μ p hr _)
    ((hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _)
    (hbound x hx r hr)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
