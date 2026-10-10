import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.HermitianCutoffEstimates
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianGeometricAssembly

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
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

variable (W : Space → Space →L[ℝ] Space) (hW : ContDiff ℝ ∞ W)

include hD hH hweak hB hdual hW in

theorem nonharmonic_geometric_cutoffLog_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (q : Space) (hq : q ∈ U) (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (smoothAntiProjection A J α hs ht (smoothDdc J
          (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffLog_smooth W R hsr.1 b)
            (HermitianRadial.translatedCutoffLog_compact W hR s b)
            (((HermitianRadial.translatedCutoffLog_support W hR s b).trans (hcenters b hb)).trans
              (hKU.trans (hUD.trans (D p).domain_subset))))))‖ ≤ C/(s+dist b y) := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨δ₀,hδ₀,C₀,hC₀,hzero⟩ := scalarCorrection_cutoffLog_estimate
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU q hq
      0 W (V 0) hW ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hone⟩ := scalarCorrection_cutoffLog_estimate
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU q hq
      1 W (V 1) hW ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro y hy s hsr b hb
  have hy₀ : y ∈ Metric.ball q δ₀ :=
    (show dist y q < min δ₀ δ₁ from hy).trans_le (min_le_left _ _)
  have hy₁ : y ∈ Metric.ball q δ₁ :=
    (show dist y q < min δ₀ δ₁ from hy).trans_le (min_le_right _ _)
  rw [smoothAnti_ddc_cutoffLog A J α hs ht D W p hφ hc hφD K hK (hKU.trans hUD)
    hφone hR hsr.1 b (hcenters b hb),map_add]
  apply (norm_add_le _ _).trans
  have h₀ := hzero y hy₀ s hsr b hb
  have h₁ := hone y hy₁ s hsr b hb
  exact (add_le_add h₀ h₁).trans_eq (by rw [add_div])

include hD hH hweak hB hdual hW in

theorem nonharmonic_geometric_cutoffSqrt_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (q : Space) (hq : q ∈ U) (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) (hR1 : 2*R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (smoothAntiProjection A J α hs ht (smoothDdc J
          (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffSqrt_smooth W R hsr.1 b)
            (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
            (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans (hcenters b hb)).trans
              (hKU.trans (hUD.trans (D p).domain_subset))))))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨δ₀,hδ₀,C₀,hC₀,hzero⟩ := scalarCorrection_cutoffSqrt_estimate
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU q hq
      0 W (V 0) hW ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters hR1
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hone⟩ := scalarCorrection_cutoffSqrt_estimate
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU q hq
      1 W (V 1) hW ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters hR1
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro y hy s hsr b hb
  have hy₀ : y ∈ Metric.ball q δ₀ :=
    (show dist y q < min δ₀ δ₁ from hy).trans_le (min_le_left _ _)
  have hy₁ : y ∈ Metric.ball q δ₁ :=
    (show dist y q < min δ₀ δ₁ from hy).trans_le (min_le_right _ _)
  rw [smoothAnti_ddc_cutoffSqrt A J α hs ht D W p hφ hc hφD K hK (hKU.trans hUD)
    hφone hR hsr.1 b (hcenters b hb),map_add]
  apply (norm_add_le _ _).trans
  have h₀ := hzero y hy₀ s hsr b hb
  have h₁ := hone y hy₁ s hsr b hb
  exact (add_le_add h₀ h₁).trans_eq (by ring)

end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
