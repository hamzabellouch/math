import OAI.Geometry.RCD.Coordinates.NormalizedDistanceSourceLimit
import OAI.Geometry.RCD.Sobolev.DistanceLaplacian
import OAI.Geometry.RCD.Metric.ModelVolumeComparison
import OAI.Geometry.RCD.Metric.DistanceSourceMeasure

namespace OAI

/-! # Actual distance sources for shrinking almost-maximal balls

Equal normalized limits at r and 2r force the full positive source mass,
including singular mass, to vanish in rescaled units. The sources themselves
are constructed from the retained RCD distance-Laplacian theorem.
-/

open Set Filter Metric MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.distance_sources_from_volume_limits {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    {ω : ℝ}
    (hV : Tendsto (fun k => (r k)^(-(n:ℝ))*(hausdorff n X).real (ball (p k) (r k))) atTop (𝓝 ω))
    (hW : Tendsto (fun k => (2*r k)^(-(n:ℝ))*(hausdorff n X).real (ball (p k) (2*r k))) atTop (𝓝 ω)) :
    let _ := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    ∃ σ : ℕ → Measure X,
      (∀ k, IsFiniteMeasure (σ k)) ∧
      (∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (4*r k)),
        localGamma (hausdorff n X) hX.quadratic
          (inwardSobolev (hausdorff n X) hX.quadratic (p k) (4*r k))
          (inwardSobolev (hausdorff n X) hX.quadratic (p k) (4*r k)) x=1) ∧
      (∀ k (C : ℝ) (χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic (p k) (4*r k) C)
        (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (v : X → ℝ) (L : ℝ≥0),
        LipschitzWith L v → HasCompactSupport v → tsupport v ⊆ ball (p k) (r k) →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] v →
        energyForm (hausdorff n X) hX.quadratic
          (positiveSquaredDistance (hausdorff n X) hX.quadratic
            (mul_nonneg (by norm_num) (hr k).le) χ) ψ+
          ((n:ℝ)+(-K)*(4*r k)^2)*(∫ x in ball (p k) (r k), v x ∂hausdorff n X)=∫ x, v x ∂σ k) ∧
      Tendsto (fun k => (r k)^(-(n:ℝ))*(σ k).real (ball (p k) (r k))) atTop (𝓝 0) := by
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  dsimp only
  obtain ⟨a,ha,hBG⟩ := hX.exists_model_ballVolumeComparison hn
  have hex (k : ℕ) := distance_source_and_volume_drop hX hn hX.localSquaredDistanceInput
    (neg_nonneg.mpr hK) (by simp : -(-K)≤K) (p k) (hr k) hBG
    (continuous_comparisonModelVolume (n-1) a) (comparisonModelVolume_pos (n-1) ha (hr k))
  choose σ hσ heik hmass hsource using hex
  refine ⟨σ,hσ,heik,hsource,?_⟩
  exact radial_mass_normalized_tendsto_zero (by exact_mod_cast (show 0<n by omega))
    (neg_nonneg.mpr hK) r (fun k => (σ k).real (ball (p k) (r k)))
    (fun k => (hausdorff n X).real (ball (p k) (r k)))
    (fun k => (hausdorff n X).real (ball (p k) (2*r k))) hr
    (fun _ => measureReal_nonneg) hr0 hV hW hmass

end RegularPointCoordinates

end

end OAI
