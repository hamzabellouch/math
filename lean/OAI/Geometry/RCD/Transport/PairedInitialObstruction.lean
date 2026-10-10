import OAI.Geometry.RCD.Transport.CompressedEvaluationInverse
import OAI.Geometry.RCD.Transport.ObservableSubplans
import OAI.Geometry.RCD.Transport.InitialEntropyObstruction
import OAI.Geometry.RCD.Coordinates.NormalizedSubplanData

namespace OAI

/-! # Paired subplans cannot separate immediately from the same initial law -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem paired_initial_obstruction (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ] (hσ : σ univ ≠ 0)
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π)
    (hinit : ∀ᵐ z ∂σ, z.1 0=z.2 0)
    (hsep : σ.map Prod.fst ⟂ₘ σ.map Prod.snd) : False := by
  let μ := hausdorff n X
  have hfin := coupling_transportCost_ne_top hp.1 hp.2.1 p
    (integrable_dist_sq_of_ae_bounded _ p hs₀) (integrable_dist_sq_of_ae_bounded _ p hs₁)
  have hlmass : (σ.map Prod.fst) univ=σ univ := by
    rw [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ]
  have hrmass : (σ.map Prod.snd) univ=σ univ := by
    rw [Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ]
  let c := (σ univ)⁻¹
  let ρ₀ := c • σ.map Prod.fst
  let ρ₁ := c • σ.map Prod.snd
  have hdata₀ := normalized_subplan_data π hg hp hfin μ hc p hs₀ hs₁
    (σ.map Prod.fst) hl (by rwa [hlmass])
  have hdata₁ := normalized_subplan_data π hg hp hfin μ hc p hs₀ hs₁
    (σ.map Prod.snd) hr (by rwa [hrmass])
  simp only [hlmass] at hdata₀
  simp only [hrmass] at hdata₁
  obtain ⟨hprob₀,hg₀,hp₀,hc₀,hs₀₀,hs₀₁⟩ := hdata₀
  obtain ⟨hprob₁,hg₁,hp₁,hc₁,hs₁₀,hs₁₁⟩ := hdata₁
  let : IsProbabilityMeasure ρ₀ := hprob₀
  let : IsProbabilityMeasure ρ₁ := hprob₁
  let D : ℝ≥0 := ⟨(c*ENNReal.ofReal C).toReal,ENNReal.toReal_nonneg⟩
  have hDe : ENNReal.ofReal D=c*ENNReal.ofReal C :=
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hσ) ENNReal.ofReal_ne_top)
  have hc₀' (t : Time) : ρ₀.map (fun γ => γ t) ≤ ENNReal.ofReal D • μ := by
    rw [hDe]; exact hc₀ t
  have hc₁' (t : Time) : ρ₁.map (fun γ => γ t) ≤ ENNReal.ofReal D • μ := by
    rw [hDe]; exact hc₁ t
  have hch₀ : EntropyChord (fun t => boltzmannEntropy μ (ρ₀.map (fun γ => γ t))) ((|K|/2)*(2*R)^2) :=
    hX.bounded_plan_entropy_chord hn p hR ρ₀ hg₀ hp₀ hc₀' hs₀₀ hs₀₁
  have hch₁ : EntropyChord (fun t => boltzmannEntropy μ (ρ₁.map (fun γ => γ t))) ((|K|/2)*(2*R)^2) :=
    hX.bounded_plan_entropy_chord hn p hR ρ₁ hg₁ hp₁ hc₁' hs₁₀ hs₁₁
  have hi : ρ₀.map (fun γ => γ 0)=ρ₁.map (fun γ => γ 0) := by
    dsimp only [ρ₀,ρ₁]
    rw [Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_map (measurable_path_eval 0) measurable_fst,
      Measure.map_map (measurable_path_eval 0) measurable_snd]
    congr 1
    exact Measure.map_congr hinit
  have hpath : ρ₀ ⟂ₘ ρ₁ := ((hsep.smul c).symm.smul c).symm
  have hac₀ : ρ₀ ≪ π := hl.absolutelyContinuous.smul_left c
  have hac₁ : ρ₁ ≪ π := hr.absolutelyContinuous.smul_left c
  have hfuture (t : Time) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1) :
      ρ₀.map (fun γ => γ t) ⟂ₘ ρ₁.map (fun γ => γ t) := by
    obtain ⟨g,hg,hgi⟩ := hX.compressed_evaluation_inverse hn p hR π hg hp hC hc hs₀ hs₁ t ht0 ht1
    exact mutuallySingular_map_of_ae_left_inverse π ρ₀ ρ₁ (measurable_path_eval t) hg hgi hac₀ hac₁ hpath
  let : IsFiniteMeasure (μ.restrict (closedBall p (3*R))) := ⟨by
    simpa [μ] using hX.finiteOnBounded (closedBall p (3*R)) isBounded_closedBall⟩
  have hstay₀ (t : Time) : ∀ᵐ x ∂ρ₀.map (fun γ => γ t), x ∈ closedBall p (3*R) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ ρ₀ hg₀ hp₀ p hR hs₀₀ hs₀₁).mono fun γ hγ => hγ.2 t
  have hstay₁ (t : Time) : ∀ᵐ x ∂ρ₁.map (fun γ => γ t), x ∈ closedBall p (3*R) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded _ _ ρ₁ hg₁ hp₁ p hR hs₁₀ hs₁₁).mono fun γ hγ => hγ.2 t
  exact initial_entropy_obstruction μ measurableSet_closedBall ρ₀ ρ₁ ENNReal.ofReal_ne_top
    hc₀' hc₁' hstay₀ hstay₁ hch₀ hch₁ hi hfuture

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
