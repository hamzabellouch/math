import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianShell
import OAI.Geometry.TamingCompatibility.Functional.QuadraticShellLimit
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGeometricDistance
import OAI.Geometry.TamingCompatibility.DifferentialForms.GeometricVolumeBall
import OAI.Geometry.TamingCompatibility.DifferentialForms.FourthMomentKernel

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def physicalProfile (r : ℝ) (x y : X) : ℝ :=
  ((1+(hermitianEDist J α hs ht x y).toReal/r)⁻¹)^6

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma physicalProfile_continuous {r : ℝ} (hr : 0 < r) :
    Continuous (fun xy : X×X => physicalProfile J α hs ht r xy.1 xy.2) := by
  let := geometricMetricSpace J α hs ht
  change Continuous (fun xy : X×X => ((1+dist xy.1 xy.2/r)⁻¹)^6)
  exact ((continuous_const.add ((continuous_fst.dist continuous_snd).div_const r)).inv₀
    (fun xy => (show 0 < 1+dist xy.1 xy.2/r by positivity).ne')).pow 6

omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
lemma physicalProfile_nonneg (r : ℝ) (x y : X) : 0 ≤ physicalProfile J α hs ht r x y := by
  unfold physicalProfile
  positivity

omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
lemma physicalProfile_le_one {r : ℝ} (hr : 0 < r) (x y : X) : physicalProfile J α hs ht r x y ≤ 1 := by
  apply pow_le_one₀ (by positivity)
  apply inv_le_one_of_one_le₀
  have : 0 ≤ (hermitianEDist J α hs ht x y).toReal/r := by positivity
  linarith

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma physicalProfile_symm (r : ℝ) (x y : X) : physicalProfile J α hs ht r x y = physicalProfile J α hs ht r y x := by
  let := geometricMetricSpace J α hs ht
  change ((1+dist x y/r)⁻¹)^6 = ((1+dist y x/r)⁻¹)^6
  rw [dist_comm]

omit [SecondCountableTopology X] in
lemma physicalProfile_volume_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : X, ∀ r : ℝ, 0 < r →
      (∫ x, physicalProfile J α hs ht r x y ∂geometricVolume A J α) ≤ C*r^4 := by
  let := geometricVolume_finite A J α hs ht
  obtain ⟨C,hC,hgrowth⟩ := geometricVolume_hermitian_ball_growth J α hs ht A
  refine ⟨32*C,by positivity,fun y r hr => ?_⟩
  have hδ : Measurable (fun x => hermitianEDist J α hs ht y x) :=
    ((hermitianEDist_continuous J α hs ht).comp (continuous_const.prodMk continuous_id)).measurable
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (FourthShell.lintegral_profile_le (geometricVolume A J α) _ hδ C hC (hgrowth y) hr)
  rw [ENNReal.toReal_ofReal (by positivity),← QuadraticShell.integral_profile_toReal _ _ hδ] at hh
  simp_rw [hermitian_profile_toReal J α hs ht _ _ hr] at hh
  change (∫ x, physicalProfile J α hs ht r y x ∂geometricVolume A J α) ≤ _ at hh
  simpa only [physicalProfile_symm J α hs ht r y] using hh

lemma physicalProfile_unit_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : Integrable
      (fun xu : X × MetricUnit (hermitianMetric J α hs ht) => physicalProfile J α hs ht r xu.1 xu.2.val.proj)
      ((geometricVolume A J α).prod μ) := by
  let := geometricVolume_finite A J α hs ht
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hmap : Continuous (fun xu : X × MetricUnit (hermitianMetric J α hs ht) => (xu.1,xu.2.val.proj)) :=
    continuous_fst.prodMk (hp.comp continuous_snd)
  have hh := (physicalProfile_continuous J α hs ht hr).comp hmap
  exact hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def physicalProfileMass (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (r : ℝ) (x : X) : ℝ :=
  ∫ u, physicalProfile J α hs ht r x u.val.proj ∂μ

lemma physicalProfileMass_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : Integrable (physicalProfileMass J α hs ht μ r) (geometricVolume A J α) := by
  let := geometricVolume_finite A J α hs ht
  exact (physicalProfile_unit_integrable A J α hs ht μ hr).integral_prod_left

omit [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [T2Space X] in
lemma physicalProfileMass_nonneg
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (r : ℝ) (x : X) :
    0 ≤ physicalProfileMass J α hs ht μ r x :=
  integral_nonneg (fun u => physicalProfile_nonneg J α hs ht r x u.val.proj)

lemma physicalProfileMass_volume_growth
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      (∫ x, physicalProfileMass J α hs ht μ r x ∂geometricVolume A J α) ≤ C*r^4 := by
  let := geometricVolume_finite A J α hs ht
  obtain ⟨C,hC,hgrowth⟩ := physicalProfile_volume_growth A J α hs ht
  refine ⟨C,hC,fun r hr => ?_⟩
  unfold physicalProfileMass
  rw [integral_integral_swap (physicalProfile_unit_integrable A J α hs ht μ hr)]
  have hi := (physicalProfile_unit_integrable A J α hs ht μ hr).integral_prod_right
  have hh := integral_mono hi (integrable_const (C*r^4)) (fun u => hgrowth u.val.proj r hr)
  simpa only [integral_const,probReal_univ,one_smul] using hh
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms Set Filter GeometricHilbert.GeometricNormalCharts
open scoped Manifold ContDiff Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]

lemma compact_physical_chart_near (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (p : X) {K : Set X} (hK : IsCompact K)
    (hKs : K ⊆ (extChartAt Model p).source) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y : X,
      (hermitianEDist J α hs ht x y).toReal ≤ δ →
      y ∈ (extChartAt Model p).source ∧
      ‖extChartAt Model p y-extChartAt Model p x‖ ≤ ε := by
  let := geometricMetricSpace J α hs ht
  let U : Set (X×X) := (extChartAt Model p).source ×ˢ (extChartAt Model p).source
  have hU : IsOpen U := (isOpen_extChartAt_source p).prod (isOpen_extChartAt_source p)
  let f : X×X → ℝ := fun xy => ‖extChartAt Model p xy.2-extChartAt Model p xy.1‖
  have hf : ContinuousOn f U :=
    ((continuousOn_extChartAt p).comp continuous_snd.continuousOn (fun _ h => h.2) |>.sub
      ((continuousOn_extChartAt p).comp continuous_fst.continuousOn (fun _ h => h.1))).norm
  let W := U ∩ f ⁻¹' Iio ε
  have hW : IsOpen W := hf.isOpen_inter_preimage hU isOpen_Iio
  have hD : IsCompact ((fun x : X => (x,x)) '' K) := hK.image (continuous_id.prodMk continuous_id)
  have hsW : (fun x : X => (x,x)) '' K ⊆ W := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨⟨hKs hx,hKs hx⟩,?_⟩
    simpa only [mem_preimage,mem_Iio,f,sub_self,norm_zero] using hε
  obtain ⟨δ,hδ,hsub⟩ := hD.exists_cthickening_subset_open hW hsW
  refine ⟨δ,hδ,fun x hx y hxy => ?_⟩
  have hm : (x,y) ∈ Metric.cthickening δ ((fun x : X => (x,x)) '' K) := by
    apply Metric.mem_cthickening_of_dist_le (x,y) (x,x) δ ((fun x : X => (x,x)) '' K) ⟨x,hx,rfl⟩
    change dist x y ≤ δ at hxy
    simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg,dist_comm y x] using hxy
  exact ⟨(hsub hm).1.2,le_of_lt (hsub hm).2⟩
end TamingCompatibility

end
end

end OAI
