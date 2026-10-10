import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.PhysicalProfile
import OAI.Geometry.TamingCompatibility.Charts.HermitianChartControl
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationChart

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter MeasureTheory PlaneVariation Concentration Hermitian
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

include hE in
lemma physicalProfile_concentrationDensity (p : A.centers) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x : X, x ∈ tsupport (A.partition p) →
      ∀ r : ℝ, 0 < r → ∀ u : MetricUnit (hermitianMetric J α hs ht),
      (1/r^2)*physicalProfile J α hs ht r x u.val.proj ≤
        C*concentrationDensity A J α hs ht E p r (extChartAt Model p.val x) u+B*r^4 := by
  obtain ⟨δ,hδ,hnear⟩ := compact_physical_chart_near J α hs ht p.val
    (isClosed_tsupport (A.partition p)).isCompact
    (fun x hx => (E p).source_subset (hE p hx))
    (div_pos (E p).concentrationCutoff.positive (by norm_num : (0:ℝ) < 2))
  obtain ⟨L,hL,hcoord⟩ := compact_hermitian_chart_control J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  obtain ⟨m,P,hm,hP,harea⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  refine ⟨L^6/m,1/δ^6,by positivity,by positivity,fun x hx r hr u => ?_⟩
  by_cases hd : (hermitianEDist J α hs ht x u.val.proj).toReal ≤ δ
  · have hne := hnear x hx u.val.proj hd
    have hcenter := partition_center_ball A J α ht E hE p hx
    have hphys := (E p).concentrationCutoff.near _ hcenter _
      (hne.2.trans (by linarith [(E p).concentrationCutoff.positive]))
    have huK : u ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact :=
      ⟨extChartAt Model p.val u.val.proj,Or.inr ⟨_,hphys,rfl⟩,(extChartAt Model p.val).left_inv hne.1⟩
    have hdist := hcoord x u.val.proj ((E p).source_subset (hE p hx)) hne.1
      ((E p).concentrationCompact_center hcenter) (Or.inr ⟨_,hphys,rfl⟩)
    have hprof := profile_le_rationalKernel hr hL ENNReal.toReal_nonneg _ hdist
    have hpa : L^6 ≤ (L^6/m)*unitChartArea J α hs ht p.val u := by
      have hh := mul_le_mul_of_nonneg_left (harea u huK).1 (by positivity : 0 ≤ L^6/m)
      rwa [div_mul_cancel₀ _ hm.ne'] at hh
    calc
      _ ≤ L^6*rationalKernel r (extChartAt Model p.val x-extChartAt Model p.val u.val.proj) := hprof
      _ ≤ (L^6/m)*(unitChartArea J α hs ht p.val u *
          rationalKernel r (extChartAt Model p.val x-extChartAt Model p.val u.val.proj)) := by
        nlinarith [mul_le_mul_of_nonneg_right hpa
          (rationalKernel_nonneg r (extChartAt Model p.val x-extChartAt Model p.val u.val.proj))]
      _ ≤ _ := by
        rw [←concentrationDensity_near A J α hs ht E p hcenter u hne.1 hne.2 r]
        exact le_add_of_nonneg_right (by positivity)
  · have hp := profile_away hr hδ (le_of_lt (lt_of_not_ge hd))
    change (1/r^2)*physicalProfile J α hs ht r x u.val.proj ≤ r^4/δ^6 at hp
    calc
      _ ≤ r^4/δ^6 := hp
      _ = (1/δ^6)*r^4 := by ring
      _ ≤ _ := le_add_of_nonneg_left
        (mul_nonneg (by positivity) (concentrationDensity_nonneg A J α hs ht E p r _ u))
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
  [T2Space X] [CompactSpace X] [ConnectedSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2

lemma physicalProfile_unit_section_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) (x : X) :
    Integrable (fun u : MetricUnit (hermitianMetric J α hs ht) => physicalProfile J α hs ht r x u.val.proj) μ := by
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  exact ((physicalProfile_continuous J α hs ht hr).comp (continuous_const.prodMk hp)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

include hE in
lemma physicalProfile_localConcentration
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (p : A.centers) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x : X, x ∈ tsupport (A.partition p) →
      ∀ r : ℝ, 0 < r →
      (1/r^2)*physicalProfileMass J α hs ht μ r x ≤
        C*localConcentration A J α hs ht E μ p r (extChartAt Model p.val x)+B*r^4 := by
  obtain ⟨C,B,hC,hB,hb⟩ := physicalProfile_concentrationDensity A J α hs ht E hE p
  refine ⟨C,B,hC,hB,fun x hx r hr => ?_⟩
  rw [physicalProfileMass,localConcentration_integral A J α hs ht E μ p hr]
  have hi := physicalProfile_unit_section_integrable J α hs ht μ hr x
  have hq := concentrationDensity_integrable A J α hs ht E μ p hr (extChartAt Model p.val x)
  have hh := integral_mono (hi.const_mul (1/r^2)) ((hq.const_mul C).add (integrable_const (B*r^4))) (hb x hx r hr)
  simpa only [Pi.add_apply,integral_add (hq.const_mul C) (integrable_const (B*r^4)),integral_const_mul,
    integral_const,probReal_univ,one_smul] using hh

include hE in
lemma physicalProfile_globalConcentration
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ] :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ x : X, ∀ r : ℝ, 0 < r →
      (1/r^2)*physicalProfileMass J α hs ht μ r x ≤
        C*globalConcentration A J α hs ht E μ r x+B*r^4 := by
  classical
  choose c b hc hb hh using fun p => physicalProfile_localConcentration A J α hs ht E hE μ p
  let C := ∑ p : A.centers, c p
  let B := ∑ p : A.centers, b p
  have hC : 0 ≤ C := Finset.sum_nonneg (fun p _ => hc p)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun p _ => hb p)
  have hcC (p : A.centers) : c p ≤ C := Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ p)
  have hbB (p : A.centers) : b p ≤ B := Finset.single_le_sum (fun i _ => hb i) (Finset.mem_univ p)
  refine ⟨C,B,hC,hB,fun x r hr => ?_⟩
  have hq (p : A.centers) :
      A.partition p x*((1/r^2)*physicalProfileMass J α hs ht μ r x) ≤
        C*(A.partition p x*localConcentration A J α hs ht E μ p r (extChartAt Model p.val x))+
          A.partition p x*(B*r^4) := by
    by_cases hz : A.partition p x = 0
    · simp only [hz,zero_mul,mul_zero,add_zero,le_refl]
    · have hpx : x ∈ tsupport (A.partition p) := subset_tsupport _ (Function.mem_support.mpr hz)
      have hl := (hh p x hpx r hr).trans (add_le_add
        (mul_le_mul_of_nonneg_right (hcC p) (localConcentration_nonneg A J α hs ht E μ p r _))
        (mul_le_mul_of_nonneg_right (hbB p) (by positivity)))
      have hm := mul_le_mul_of_nonneg_left hl (A.partition.nonneg p x)
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hq p)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,partition_sum,one_mul] at hsum
  have he : globalConcentration A J α hs ht E μ r x =
      ∑ p : A.centers, A.partition p x*localConcentration A J α hs ht E μ p r (extChartAt Model p.val x) := by
    simp only [globalConcentration,Finset.sum_apply,concentrationPatch_apply]
  rwa [←he] at hsum
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
