import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.RadialEnergyDual
import OAI.Geometry.TamingCompatibility.Functional.CompactUniformBound
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianCombinedForms

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem nonharmonicCorrection_off_source_compact
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ f : antiPre A J α hs ht,
      (∀ z ∈ U, rawPair J α ht p.val (D p) f.val.val z = 0) →
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y f‖ ≤
        C*‖antiEnergyDualLM A J α hs ht f‖ := by
  apply _root_.OAI.IsCompact.exists_uniform_monotone_bound hK
  · intro y a b hab ha f hf
    exact (ha f hf).trans (mul_le_mul_of_nonneg_right hab (ContinuousLinearMap.opNorm_nonneg _))
  · intro q hq
    obtain ⟨δ,hδ,C,hC,hest⟩ := nonharmonicCorrection_off_source_uniform
      A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ q (hKU hq)
    refine ⟨C,hC,?_⟩
    filter_upwards [Metric.ball_mem_nhds q hδ] with y hy
    intro f hf
    exact hest y hy f ‖antiEnergyDualLM A J α hs ht f‖ (ContinuousLinearMap.opNorm_nonneg _)
      (fun v => (antiEnergyDualLM A J α hs ht f).le_opNorm v) hf
end TamingCompatibility.GeometricHilbert

end

end OAI
