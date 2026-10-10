import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialGeometricAssembly
import OAI.Geometry.TamingCompatibility.Functional.RadialSqrtDualBounds

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

def smoothPullbackCompactLM (p : X) (K : Set Space)
    (hK : K ⊆ (extChartAt Model p).target) :
    smoothForms X 2 →ₗ[ℝ] C(K, MetricForms.Form Space 2) where
  toFun a := ⟨_, ((smooth_chart a.val a.property p).continuousOn.mono hK).domRestrict⟩
  map_add' a b := by apply ContinuousMap.ext; intro z; exact (smoothPullbackLM p z).map_add a b
  map_smul' c a := by apply ContinuousMap.ext; intro z; exact (smoothPullbackLM p z).map_smul c a

include hD in

theorem harmonic_compact_dual_bound (p : X) (K : Set Space) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt Model p).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f h : antiPre A J α hs ht,
      smoothL2 A J α hs ht true h.val = (harmonicAnti A J α hs ht).starProjection
        (smoothL2 A J α hs ht true f.val) →
      ∀ y ∈ K, ‖ManifoldForms.pullback (k := 2) h.val.val (extChartAt Model p).symm y‖ ≤
        C * ‖antiEnergyDualLM A J α hs ht f‖ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  obtain ⟨C,hC,hbound⟩ := harmonic_seminorm_dual_bound (F := C(K, MetricForms.Form Space 2)) A J α hs ht D hD
    ((smoothPullbackCompactLM p K hK).comp (antiPre A J α hs ht).subtype)
  refine ⟨C,hC,?_⟩
  intro f h hh y hy
  exact ((smoothPullbackCompactLM p K hK h.val).norm_coe_le_norm ⟨y,hy⟩).trans
    (hbound f h hh)

include hD in

theorem geometric_cutoffLog_dual_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖antiEnergyDualLM A J α hs ht
        (smoothAntiProjection A J α hs ht (smoothDdc J
          (scalarChartLift_smooth p.val (translatedCutoffLog_smooth R hsr.1 b)
            (translatedCutoffLog_compact hR s b)
            (((translatedCutoffLog_support hR s b).trans (hcenters b hb)).trans
              (hKD.trans (D p).domain_subset)))))‖ ≤ C := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨C₀,hC₀,hzero⟩ := scalarEnergyDual_cutoffLog_bound A J α hs ht D hD
    p τ K hK hKD hτ (V 0) ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,hone⟩ := scalarEnergyDual_cutoffLog_bound A J α hs ht D hD
    p τ K hK hKD hτ (V 1) ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro s hsr b hb
  rw [smoothAnti_ddc_cutoffLog A J α hs ht D p hφ hc hφD K hK hKD hφone
    hR hsr.1 b (hcenters b hb),map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD 0
      (logCutoffSourceSupported (V 0) ((V 0).smooth ⊤) hR hsr.1 K b (hcenters b hb))) _).trans
    (add_le_add (hzero 0 s hsr b hb) (hone 1 s hsr b hb))

include hD in

theorem geometric_cutoffSqrt_dual_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖antiEnergyDualLM A J α hs ht
        (smoothAntiProjection A J α hs ht (smoothDdc J
          (scalarChartLift_smooth p.val (translatedCutoffSqrt_smooth R hsr.1 b)
            (translatedCutoffSqrt_compact hR s b)
            (((translatedCutoffSqrt_support hR s b).trans (hcenters b hb)).trans
              (hKD.trans (D p).domain_subset)))))‖ ≤ C := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨C₀,hC₀,hzero⟩ := scalarEnergyDual_cutoffSqrt_bound A J α hs ht D hD
    p τ K hK hKD hτ (V 0) ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,hone⟩ := scalarEnergyDual_cutoffSqrt_bound A J α hs ht D hD
    p τ K hK hKD hτ (V 1) ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro s hsr b hb
  rw [smoothAnti_ddc_cutoffSqrt A J α hs ht D p hφ hc hφD K hK hKD hφone
    hR hsr.1 b (hcenters b hb),map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD 0
      (sqrtCutoffSourceSupported (V 0) ((V 0).smooth ⊤) hR hsr.1 K b (hcenters b hb))) _).trans
    (add_le_add (hzero 0 s hsr b hb) (hone 1 s hsr b hb))

end TamingCompatibility.GeometricHilbert

end

end OAI
