import OAI.Geometry.RCD.Transport.LocalHarmonicOptimalMean
import OAI.Geometry.RCD.Metric.DominatedCompactProbability
import OAI.Geometry.RCD.Transport.CompressedFiniteUnique

namespace OAI

/-! # Affine local harmonic means for bounded ambient endpoint laws -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
attribute [local instance] pathBorel pathBorelSpace

include hn in
theorem local_harmonic_mean_on_bounded_plan
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    {R : ℝ} (hR : 1 ≤ R)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (V : X → ℝ)
    {b : ℝ} (hb : 50*R < b)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u
      =ᵐ[(hausdorff n X).restrict (ball p b)] V)
    (hH : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) u)
    (L : ℝ≥0) (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic u u x ≤ (L:ℝ)^2)
    (c : ℝ) (hc : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c) :
    ∀ t : Time, (∫ γ, V (γ t) ∂π) =
      (1-(t:ℝ))*(∫ γ, V (γ 0) ∂π)+(t:ℝ)*(∫ γ, V (γ 1) ∂π) := by
  let m := hausdorff n X
  let S := closedBall p R
  have hSm : MeasurableSet S := measurableSet_closedBall
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall p R)
  have hs (t : Time) (ht : ∀ᵐ x ∂π.map (fun γ => γ t), dist x p ≤ R) :
      ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ S := by
    simpa only [S,mem_closedBall] using ht
  obtain ⟨μ,ρ₀,C₀,hprob₀,hμ,hm₀,hp₀,hC₀,hd₀⟩ := dominated_supported_probability_law
    m (π.map (fun γ => γ 0)) S hSm (hs 0 hs₀) hC (hcomp 0)
  obtain ⟨ν,ρ₁,C₁,hprob₁,hν,hm₁,hp₁,hC₁,hd₁⟩ := dominated_supported_probability_law
    m (π.map (fun γ => γ 1)) S hSm (hs 1 hs₁) hC (hcomp 1)
  let := hprob₀
  let := hprob₁
  obtain ⟨a₀⟩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨b₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hopt' : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))) := by rw [hμ,hν]; exact hopt
  exact hX.local_harmonic_mean_on_optimal_plan hn p a₀ b₀ ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
    hC₀ hC₁ hd₀ hd₁ hR (fun y => by simpa only [S,mem_closedBall,dist_comm] using y.property)
    (fun y => by simpa only [S,mem_closedBall,dist_comm] using y.property)
    π hgeo hopt' hC hcomp u V hb hu hH L hL c hc

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
