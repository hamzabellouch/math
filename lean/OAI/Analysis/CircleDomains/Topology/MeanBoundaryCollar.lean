import OAI.Analysis.CircleDomains.Topology.MeanIndexBoundary
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! Uniform approach to the actual boundary mean. Only avoidance at the
boundary is used: the nearby lifted points need not avoid every sample arc. -/

open Set Function Filter MeasureTheory
open scoped Topology Uniformity

noncomputable section
namespace CircleDomainRigidity

 theorem mean_uniform_boundary_approximation_of_dist
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    (hmiss : ∀ x ∈ Icc (0 : ℝ) 1,
      ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (x : ℂ) ∉ range γ.val)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ClosedUpperHalfPlane,
      dist z.val (t : ℂ) < δ →
      |meanGeometricIndex hsch K hKS η z -
        boundaryIndexMean (compactArcStartingAngleLaw K η) t| < ε := by
  let B : ℝ → ClosedUpperHalfPlane := fun x => ⟨(x : ℂ), by simp⟩
  have hB : Continuous B := Complex.continuous_ofReal.subtype_mk _
  have hc : IsCompact (B '' Icc (0 : ℝ) 1) := isCompact_Icc.image hB
  have hcont : ∀ z ∈ B '' Icc (0 : ℝ) 1,
      ContinuousAt (meanGeometricIndex hsch K hKS η) z := by
    rintro _ ⟨x, hx, rfl⟩
    exact continuousAt_meanGeometricIndex hsch hsep K hK hKS η (B x) (hmiss x hx)
  have hu := hc.uniformContinuousAt_of_continuousAt
    (meanGeometricIndex hsch K hKS η) hcont (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨δ, hδ, ?_⟩
  intro t ht z hz
  have hdist : dist (B t) z < δ := by
    change dist (t : ℂ) z.val < δ
    simpa only [dist_comm] using hz
  have he := hd hdist ⟨t, ht, rfl⟩
  change dist (meanGeometricIndex hsch K hKS η (B t))
    (meanGeometricIndex hsch K hKS η z) < ε at he
  rw [meanGeometricIndex_boundary hsch K hKS η t (hmiss t ht)] at he
  simpa only [Real.dist_eq, abs_sub_comm] using he

 theorem mean_uniform_boundary_approximation
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    (hmiss : ∀ x ∈ Icc (0 : ℝ) 1,
      ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (x : ℂ) ∉ range γ.val)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ClosedUpperHalfPlane, z.val.re ∈ Icc (0 : ℝ) 1 → z.val.im < δ →
      |meanGeometricIndex hsch K hKS η z -
        boundaryIndexMean (compactArcStartingAngleLaw K η) z.val.re| < ε := by
  obtain ⟨δ, hδ, hd⟩ :=
    mean_uniform_boundary_approximation_of_dist hsch hsep K hK hKS η hmiss hε
  refine ⟨δ, hδ, fun z hz hy => hd z.val.re hz z ?_⟩
  rw [Complex.dist_of_re_eq (by simp), Complex.ofReal_im, Real.dist_eq,
    sub_zero, abs_of_nonneg z.property]
  exact hy

 theorem perturbed_mean_uniform_boundary_approximation
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    (hmiss : ∀ x ∈ Icc (0 : ℝ) 1,
      ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (x : ℂ) ∉ range γ.val)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (z : ClosedUpperHalfPlane) (r : ℝ),
      z.val.re ∈ Icc (0 : ℝ) 1 → z.val.im < δ →
      |meanGeometricIndex hsch K hKS η z + r -
        boundaryIndexMean (compactArcStartingAngleLaw K η) z.val.re| < ε + |r| := by
  obtain ⟨δ, hδ, hd⟩ := mean_uniform_boundary_approximation hsch hsep K hK hKS η hmiss hε
  refine ⟨δ, hδ, ?_⟩
  intro z r hz hy
  calc
    |meanGeometricIndex hsch K hKS η z + r -
        boundaryIndexMean (compactArcStartingAngleLaw K η) z.val.re| =
        |(meanGeometricIndex hsch K hKS η z -
        boundaryIndexMean (compactArcStartingAngleLaw K η) z.val.re) + r| := by congr 1; ring
    _ ≤ |meanGeometricIndex hsch K hKS η z -
        boundaryIndexMean (compactArcStartingAngleLaw K η) z.val.re| + |r| := abs_add_le _ _
    _ < ε + |r| := add_lt_add_left (hd z hz hy) _

end CircleDomainRigidity

end

end OAI
