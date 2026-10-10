import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartComponent
import OAI.Geometry.TamingCompatibility.Elliptic.AntiChartH1
import OAI.Geometry.TamingCompatibility.Charts.ChartMetricComparison
import OAI.Geometry.TamingCompatibility.DifferentialForms.AntiEnergyWeak

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart
open MeasureTheory
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def smoothToChart : PreL2 A J α hs ht true →ₗ[ℝ] globalL2 A 2 :=
  ClosureLinear.toClosure (localizeL2 A 2)

omit [MeasurableSpace X] [BorelSpace X] in
lemma smoothToChart_dense : DenseRange (smoothToChart A J α hs ht) :=
  ClosureLinear.toClosure_dense (localizeL2 A 2)

include hD in
lemma smoothToChart_metric_bound : ∃ C : ℝ, ∀ a : PreL2 A J α hs ht true,
    ‖smoothL2 A J α hs ht true a‖ ≤ C * ‖smoothToChart A J α hs ht a‖ := by
  obtain ⟨C,hC,hb⟩ := metric_norm_le_chart A J α hs ht D hD
  refine ⟨Real.sqrt C,fun a => ?_⟩
  rw [(smoothL2 A J α hs ht true).norm_map]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC.le]
  exact hb a

def chartToMetric : globalL2 A 2 →L[ℝ] L2 A J α hs ht true :=
  (smoothL2 A J α hs ht true).toLinearMap.extendOfNorm (smoothToChart A J α hs ht)

include hD in
lemma chartToMetric_smooth (a : PreL2 A J α hs ht true) :
    chartToMetric A J α hs ht (smoothToChart A J α hs ht a) = smoothL2 A J α hs ht true a :=
  LinearMap.extendOfNorm_eq (smoothToChart_dense A J α hs ht)
    (smoothToChart_metric_bound A J α hs ht D hD) a

def energyInclusion : antiEnergy A J α hs ht →L[ℝ] L2 A J α hs ht true :=
  (WithLp.fstL 2 ℝ _ _) ∘L (antiEnergy A J α hs ht).subtypeL

def weakDelta : antiEnergy A J α hs ht →L[ℝ] L2 A J α hs ht false :=
  (WithLp.sndL 2 ℝ _ _) ∘L (antiEnergy A J α hs ht).subtypeL

lemma energyInclusion_injective : Function.Injective (energyInclusion A J α hs ht) :=
  antiEnergy_fst_injective A J α hs ht

include hD in
lemma energyInclusion_factor : energyInclusion A J α hs ht =
    chartToMetric A J α hs ht ∘L h1ToL2 A 2 ∘L energyToH1 A J α hs ht := by
  apply DFunLike.coe_injective
  apply (antiToEnergy_dense A J α hs ht).equalizer
    (energyInclusion A J α hs ht).continuous
    (chartToMetric A J α hs ht ∘L h1ToL2 A 2 ∘L energyToH1 A J α hs ht).continuous
  funext a
  change smoothL2 A J α hs ht true a.val =
    chartToMetric A J α hs ht (h1ToL2 A 2 (energyToH1 A J α hs ht (antiToEnergy A J α hs ht a)))
  rw [energyToH1_smooth A J α hs ht D hD]
  exact (chartToMetric_smooth A J α hs ht D hD a.val).symm

include hD in

theorem energyInclusion_compact : IsCompactOperator (energyInclusion A J α hs ht) := by
  rw [energyInclusion_factor A J α hs ht D hD]
  exact ((h1ToL2_compact A 2).comp_clm (energyToH1 A J α hs ht)).clm_comp
    (chartToMetric A J α hs ht)

end TamingCompatibility.GeometricHilbert

end

end OAI
