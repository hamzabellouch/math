import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePatchContinuity
import OAI.Geometry.TamingCompatibility.DifferentialForms.UnitTransverseLimit

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def transversePairKernel (p : A.centers) (K : Set Space) (r : ℝ) : UnitPair J α hs ht → ℝ :=
  ((unitChartDomain J α hs ht p.val K) ×ˢ (unitChartDomain J α hs ht p.val K)).indicator
    (fun uv => A.partition p uv.1.val.proj *
      radialCoefficient r ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖ *
      ‖unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2‖^2)

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma transversePairKernel_measurable (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target) {r : ℝ} (hr : 0 < r) :
    Measurable (transversePairKernel A J α hs ht p K r) := by
  classical
  let S := unitChartDomain J α hs ht p.val K
  let f := fun uv : UnitPair J α hs ht => unitChartFirst J α hs ht p.val uv.2
  let g := fun uv : UnitPair J α hs ht => unitChartSecond J α hs ht p.val uv.2
  let z := fun uv : UnitPair J α hs ht => unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1
  have hf : ContinuousOn f (S ×ˢ S) := (unitChartFirst_continuousOn J α hs ht p.val hKT).comp continuous_snd.continuousOn (fun _ h => h.2)
  have hg : ContinuousOn g (S ×ˢ S) := (unitChartSecond_continuousOn J α hs ht p.val hKT).comp continuous_snd.continuousOn (fun _ h => h.2)
  have hb := unitChartBase_continuousOn J α hs ht p.val hKT
  have hz : ContinuousOn z (S ×ˢ S) := (hb.comp continuous_snd.continuousOn (fun _ h => h.2)).sub
    (hb.comp continuous_fst.continuousOn (fun _ h => h.1))
  have hi : ContinuousOn (fun uv => inner ℝ (f uv) (z uv)) (S ×ˢ S) := hf.inner hz
  have hj : ContinuousOn (fun uv => inner ℝ (g uv) (z uv)) (S ×ˢ S) := hg.inner hz
  have hiv : ContinuousOn (fun uv => (inner ℝ (f uv) (z uv)) • f uv) (S ×ˢ S) := hi.smul hf
  have hjv : ContinuousOn (fun uv => (inner ℝ (g uv) (z uv)) • g uv) (S ×ˢ S) := hj.smul hg
  have hv : ContinuousOn (fun uv => unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2) (S ×ˢ S) := (hz.sub hiv).sub hjv
  have ha : ContinuousOn (fun uv : UnitPair J α hs ht => A.partition p uv.1.val.proj) (S ×ˢ S) :=
    ((A.partition p).property.continuous.comp (angularBase_continuous J α hs ht).snd).continuousOn
  have hk : ContinuousOn (fun uv => radialCoefficient r ‖z uv‖) (S ×ˢ S) :=
    continuousOn_const.div ((continuousOn_const.add (hz.norm.pow 2)).pow 4) (fun uv _ => by positivity)
  have hm := ((ha.mul hk).mul (hv.norm.pow 2)).measurable_piecewise
      (continuousOn_const : ContinuousOn (fun _ : UnitPair J α hs ht => (0 : ℝ)) (S ×ˢ S)ᶜ)
      ((unitChartDomain_closed J α hs ht p.val hK hKT).prod
        (unitChartDomain_closed J α hs ht p.val hK hKT)).measurableSet
  convert hm using 1
  funext uv
  by_cases hu : uv ∈ S ×ˢ S <;>
    simp [transversePairKernel, Set.indicator, Set.piecewise, S, z] at hu ⊢

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X] [CompactSpace X] in
lemma transversePairKernel_apply (p : A.centers) (K : Set Space) (r : ℝ)
    (u v : MetricUnit (hermitianMetric J α hs ht)) :
    transversePairKernel A J α hs ht p K r (u,v) =
      (unitChartDomain J α hs ht p.val K).indicator
        (fun w => A.partition p w.val.proj* (radialCoefficient r
          (unitDistanceCut J α hs ht p.val (unitChartBase J α hs ht p.val w) K v)*
          ‖unitTransverseCut J α hs ht p.val (unitChartBase J α hs ht p.val w) K v‖^2)) u := by
  by_cases hu : u ∈ unitChartDomain J α hs ht p.val K
  · rw [indicator_of_mem hu]
    by_cases hv : v ∈ unitChartDomain J α hs ht p.val K
    · simp only [transversePairKernel,indicator_of_mem (show (u,v) ∈ _ ×ˢ _ from ⟨hu,hv⟩),
        unitDistanceCut,unitTransverseCut,indicator_of_mem hv]
      ring
    · simp [transversePairKernel,Set.indicator,hu,hv,unitDistanceCut,unitTransverseCut]
  · simp [transversePairKernel,Set.indicator,hu]
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

lemma separating_probability_transverse_pair_limit
    (D : ∀ p : A.centers, Data J α ht p.val)
    (hA : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target) :
    Tendsto (fun r : ℝ => ∫ u, ∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let S := unitChartDomain J α hs ht p.val K
  let H := fun (r : ℝ) (u : MetricUnit (hermitianMetric J α hs ht)) =>
    ∫ v, radialCoefficient r (unitDistanceCut J α hs ht p.val (unitChartBase J α hs ht p.val u) K v)*
      ‖unitTransverseCut J α hs ht p.val (unitChartBase J α hs ht p.val u) K v‖^2 ∂μ
  have he (r : ℝ) (u : MetricUnit (hermitianMetric J α hs ht)) :
      (∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ) =
        S.indicator (fun w => A.partition p w.val.proj*H r w) u := by
    simp_rw [transversePairKernel_apply]
    by_cases hu : u ∈ S
    · dsimp only [S] at hu
      simp only [S,indicator_of_mem hu]
      exact integral_const_mul _ _
    · dsimp only [S] at hu
      simp only [S,indicator_of_notMem hu,integral_zero]
  obtain ⟨C,hC,huniform⟩ := separating_probability_transverse_uniform J α hs ht p.val hK hKT μ hann
  have hnonneg (r : ℝ) (u : MetricUnit (hermitianMetric J α hs ht)) :
      0 ≤ S.indicator (fun w => A.partition p w.val.proj*H r w) u := by
    apply Set.indicator_nonneg _ u
    intro w _
    apply mul_nonneg (A.partition.nonneg _ _)
    exact integral_nonneg (fun v => mul_nonneg (radialCoefficient_nonneg _ _) (sq_nonneg _))
  have hbound (r : ℝ) (hr : 0 < r) (u : MetricUnit (hermitianMetric J α hs ht)) :
      ‖∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ‖ ≤ C := by
    rw [he,Real.norm_eq_abs,abs_of_nonneg (hnonneg r u)]
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu]
      have humem := unitChart_mem J α hs ht p.val hKT hu
      have hh := (huniform u.val.proj humem.1 humem.2 r hr).2
      calc
        _ ≤ A.partition p u.val.proj*C := mul_le_mul_of_nonneg_left hh (A.partition.nonneg _ _)
        _ ≤ C := mul_le_of_le_one_left hC (A.partition.le_one _ _)
    · rw [indicator_of_notMem hu]
      exact hC
  have hlim (u : MetricUnit (hermitianMetric J α hs ht)) :
      Tendsto (fun r : ℝ => ∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ)
        (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simp_rw [he]
    by_cases hu : u ∈ S
    · simp only [indicator_of_mem hu]
      by_cases hc : A.partition p u.val.proj = 0
      · simp only [hc,zero_mul]
        exact tendsto_const_nhds
      · have hi := separating_probability_atlas_transverse_limit J α hs ht A D hA μ hann
          p u.val.proj hc hK hKT
        simpa only [H,unitChartBase,mul_zero] using tendsto_const_nhds.mul hi
    · simp only [indicator_of_notMem hu]
      exact tendsto_const_nhds
  have hm : ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ), AEStronglyMeasurable
      (fun u => ∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ) μ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (transversePairKernel_measurable A J α hs ht p hK hKT hr).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hb : ∀ᶠ r : ℝ in 𝓝[>] (0:ℝ), ∀ᵐ u ∂μ,
      ‖∫ v, transversePairKernel A J α hs ht p K r (u,v) ∂μ‖ ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ae_of_all _ (hbound r hr)
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (fun _ => C) hm hb (integrable_const C) (ae_of_all _ hlim)
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
