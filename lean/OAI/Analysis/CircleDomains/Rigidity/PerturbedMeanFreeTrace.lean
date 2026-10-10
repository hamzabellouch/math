import OAI.Analysis.CircleDomains.Topology.MeanIndexCircle
import OAI.Analysis.CircleDomains.Rigidity.TraceBandLevel

namespace OAI

/-! At a point avoided by the compact arc law, a vanishing correction
leaves a genuine mean trace. Its entire interval-band fiber is therefore
the single value used in ordered compatibility. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem tendsto_perturbed_mean_at_avoided_point
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {X : Type*} [TopologicalSpace X]
    (D : Set X) (x : X) (L : X → ClosedUpperHalfPlane)
    (hL : ContinuousWithinAt L D x)
    (hmiss : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (L x).val ∉ range γ.val)
    (u R : X → ℝ) (hR : Tendsto R (𝓝[D] x) (𝓝 0))
    (hu : u =ᶠ[𝓝[D] x] fun y => meanGeometricIndex hsch K hKS η (L y) + R y) :
    Tendsto u (𝓝[D] x) (𝓝 (meanGeometricIndex hsch K hKS η (L x))) := by
  have hmean := (continuousAt_meanGeometricIndex hsch hsep K hK hKS η (L x) hmiss).tendsto.comp hL
  have hsum := hmean.add hR
  simp only [add_zero] at hsum
  exact Tendsto.congr' hu.symm hsum

theorem perturbed_mean_band_at_avoided_point
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K) {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [CompactSpace X] [T2Space X]
    (D : Set X) (x : X) (hx : x ∈ closure D) (L : X → ClosedUpperHalfPlane)
    (hL : ContinuousWithinAt L D x)
    (hmiss : ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (L x).val ∉ range γ.val)
    (u R : X → ℝ) (hR : Tendsto R (𝓝[D] x) (𝓝 0))
    (hu : u =ᶠ[𝓝[D] x] fun y => meanGeometricIndex hsch K hKS η (L y) + R y)
    {B : ℝ} (hbound : ∀ y ∈ D, |u y| ≤ B) (θ : UnitAddCircle) :
    (x, θ) ∈ circleBandGraph D u ↔
      diskMeanCircle hsch K hKS η (diskRayProjection (L x).val) = θ := by
  rw [circleBandGraph_of_trace hbound hx
    (tendsto_perturbed_mean_at_avoided_point hsch hsep K hK hKS η D x L hL hmiss u R hR hu)]
  rw [diskMeanCircle_projection hsch hsep K hK hKS η]

end CircleDomainRigidity

end

end OAI
