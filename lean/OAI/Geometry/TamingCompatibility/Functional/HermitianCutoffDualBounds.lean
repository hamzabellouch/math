import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.RadialHarmonicCompact
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianGeometricAssembly
import OAI.Geometry.TamingCompatibility.Functional.HermitianDualBounds

namespace OAI

section
section

section

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

variable (W : Space → Space →L[ℝ] Space) (hW : ContDiff ℝ ∞ W)

include hD hW in

theorem scalarEnergyDual_logError_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (S : ℝ)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ _hsr : s ∈ Icc (0:ℝ) S, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (HermitianRadial.logErrorSupported W V hW hV hR K s b (hcenters b hb))‖ ≤ C := by
  obtain ⟨c,hc,hbound⟩ := scalarEnergyDualLM_scaled_bound A J α hs ht D hD p τ K hK hKD hτ
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.logErrorSchwartz_uniform_inputs W V hW hV hR
    (fun _ => 1) contDiff_const hK₀ S 0
  refine ⟨c*E*(3*R)^3,by positivity,?_⟩
  intro j s hsr b hb
  exact hbound j (HermitianRadial.logErrorSupported W V hW hV hR K s b (hcenters b hb)) b (3*R) E
    (by positivity) hE
    ((HermitianRadial.shiftedLogError_support W V hR s b).trans
      (Metric.closedBall_subset_ball (by linarith : 2*R < 3*R)))
    (hinput s hsr b hb).1

include hD hW in

theorem scalarEnergyDual_cutoffLog_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (HermitianRadial.logCutoffSourceSupported W V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C := by
  obtain ⟨C₀,hC₀,hsource⟩ := scalarEnergyDual_logSource_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (scaledCutoff R) V (scaledCutoff_smooth R) hV (2*R)
    (by positivity) (scaledCutoff_tsupport hR) K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,herror⟩ := scalarEnergyDual_logError_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ V hV R hR (2*R) K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro j s hsr b hb
  rw [HermitianRadial.logCutoffSourceSupported_eq W V hW hV,map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD j
      (HermitianRadial.logSourceSupported W (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hsr.1 b (hcenters b hb))) _).trans
    (add_le_add (hsource j s hsr b hb) (herror j s ⟨hsr.1.le,hsr.2⟩ b hb))

include hD hW in

theorem scalarEnergyDual_sqrtError_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (S : ℝ)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ _hsr : s ∈ Icc (0:ℝ) S, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (HermitianRadial.sqrtErrorSupported W V hW hV hR K s b (hcenters b hb))‖ ≤ C := by
  obtain ⟨c,hc,hbound⟩ := scalarEnergyDualLM_scaled_bound A J α hs ht D hD p τ K hK hKD hτ
  obtain ⟨E,hE,hinput⟩ := HermitianRadial.sqrtErrorSchwartz_uniform_inputs W V hW hV hR
    (fun _ => 1) contDiff_const hK₀ S 0
  refine ⟨c*E*(3*R)^3,by positivity,?_⟩
  intro j s hsr b hb
  exact hbound j (HermitianRadial.sqrtErrorSupported W V hW hV hR K s b (hcenters b hb)) b (3*R) E
    (by positivity) hE
    ((HermitianRadial.shiftedSqrtError_support W V hR s b).trans
      (Metric.closedBall_subset_ball (by linarith : 2*R < 3*R)))
    (hinput s hsr b hb).1

include hD hW in

theorem scalarEnergyDual_cutoffSqrt_bound
    (p : A.centers) (τ : 𝓢(Space,ℝ))
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hτ : ∀ z ∈ K, τ z * coordinateWeight A p z = 1)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin 2) s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarEnergyDualLM A J α hs ht D p K hK hKD j
        (HermitianRadial.sqrtCutoffSourceSupported W V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C := by
  obtain ⟨C₀,hC₀,hsource⟩ := scalarEnergyDual_sqrtSource_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (scaledCutoff R) V (scaledCutoff_smooth R) hV (2*R)
    (by positivity) (scaledCutoff_tsupport hR) K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,herror⟩ := scalarEnergyDual_sqrtError_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ V hV R hR (2*R) K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro j s hsr b hb
  rw [HermitianRadial.sqrtCutoffSourceSupported_eq W V hW hV,map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD j
      (HermitianRadial.sqrtSourceSupported W (scaledCutoff R) V (scaledCutoff_smooth R) hV
        (2*R) (scaledCutoff_tsupport hR) K hsr.1 b (hcenters b hb))) _).trans
    (add_le_add (hsource j s hsr b hb) (herror j s ⟨hsr.1.le,hsr.2⟩ b hb))

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

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

variable (W : Space → Space →L[ℝ] Space) (hW : ContDiff ℝ ∞ W)

include hD hW in

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
          (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffLog_smooth W R hsr.1 b)
            (HermitianRadial.translatedCutoffLog_compact W hR s b)
            (((HermitianRadial.translatedCutoffLog_support W hR s b).trans (hcenters b hb)).trans
              (hKD.trans (D p).domain_subset)))))‖ ≤ C := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨C₀,hC₀,hzero⟩ := scalarEnergyDual_cutoffLog_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (V 0) ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,hone⟩ := scalarEnergyDual_cutoffLog_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (V 1) ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro s hsr b hb
  rw [smoothAnti_ddc_cutoffLog A J α hs ht D W p hφ hc hφD K hK hKD hφone
    hR hsr.1 b (hcenters b hb),map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD 0
      (HermitianRadial.logCutoffSourceSupported W (V 0) ((V 0).smooth ⊤) hR hsr.1 K b (hcenters b hb))) _).trans
    (add_le_add (hzero 0 s hsr b hb) (hone 1 s hsr b hb))

include hD hW in

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
          (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffSqrt_smooth W R hsr.1 b)
            (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
            (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans (hcenters b hb)).trans
              (hKD.trans (D p).domain_subset)))))‖ ≤ C := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨C₀,hC₀,hzero⟩ := scalarEnergyDual_cutoffSqrt_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (V 0) ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters
  obtain ⟨C₁,hC₁,hone⟩ := scalarEnergyDual_cutoffSqrt_bound A J α hs ht D hD W hW
    p τ K hK hKD hτ (V 1) ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters
  refine ⟨C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro s hsr b hb
  rw [smoothAnti_ddc_cutoffSqrt A J α hs ht D W p hφ hc hφD K hK hKD hφone
    hR hsr.1 b (hcenters b hb),map_add]
  exact (norm_add_le
    (scalarEnergyDualLM A J α hs ht D p K hK hKD 0
      (HermitianRadial.sqrtCutoffSourceSupported W (V 0) ((V 0).smooth ⊤) hR hsr.1 K b (hcenters b hb))) _).trans
    (add_le_add (hzero 0 s hsr b hb) (hone 1 s hsr b hb))

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
