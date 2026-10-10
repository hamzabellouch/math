import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianUnitMetric
import OAI.Geometry.TamingCompatibility.Functional.GeometricOffCompact
import OAI.Geometry.TamingCompatibility.DifferentialForms.CorrectedDdcOff

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

theorem correctedDdc_off_source_compact
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ v : Space,
      chartMetric J α p.val y v v = 1 →
      ∀ (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f),
      (∀ z ∈ U, (extChartAt Model p.val).symm z ∉ tsupport f) →
      ‖ManifoldForms.pullback (correctedDdc A J α hs ht H Gs hf).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v]‖ ≤
        C*‖antiEnergyDualLM A J α hs ht
          (smoothAntiProjection A J α hs ht (smoothDdc J hf))‖ := by
  obtain ⟨C,hC,hest⟩ := nonharmonicCorrection_off_source_compact
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU
  have hKT : K ⊆ (extChartAt Model p.val).target := hKU.trans (hUD.trans (D p).domain_subset)
  obtain ⟨M,hM,hunit⟩ := form_unit_line_bound J α hs ht p.val hK hKT
  refine ⟨C*M,by positivity,?_⟩
  intro y hy v hv f hf hoff
  rw [correctedDdc_norm_off_source A J α hs ht H Gs hf p.val (hKT hy) (hoff y (hKU hy)) v]
  have he := hest y hy (smoothAntiProjection A J α hs ht (smoothDdc J hf)) (by
    intro z hz
    apply rawPair_zero_of_zero
    exact anti_ddc_zero_off J f (hoff z hz))
  exact (hunit y hy v hv _).trans (by
    nlinarith [mul_le_mul_of_nonneg_right he hM.le])
end TamingCompatibility.GeometricHilbert

end

end OAI
