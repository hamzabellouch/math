import OAI.Geometry.RCD.Transport.ResolvedSubplanEntropy
import OAI.Geometry.RCD.Transport.BoundedPlanEntropyBounds

namespace OAI

/-! # Mass-dependent bounds for the actual resolved branch entropy -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem resolved_subplan_entropy_bounds (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ] (hσ : σ univ ≠ 0)
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π) (q t : Time) :
    let τ := ((σ univ)⁻¹ • σ).map (resolvePathBranch q);
    -Real.log ((hausdorff n X).real (closedBall p (3*R))) ≤
      boltzmannEntropy (hausdorff n X) (τ.map (fun γ => γ t)) ∧
    boltzmannEntropy (hausdorff n X) (τ.map (fun γ => γ t)) ≤
      Real.log (2*(C:ℝ)/σ.real univ) ∧
    Integrable (fun x => ((τ.map (fun γ => γ t)).rnDeriv (hausdorff n X) x).toReal *
      Real.log ((τ.map (fun γ => γ t)).rnDeriv (hausdorff n X) x).toReal) (hausdorff n X) := by
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  have hfin := coupling_transportCost_ne_top hp.1 hp.2.1 p
    (integrable_dist_sq_of_ae_bounded _ p hs₀) (integrable_dist_sq_of_ae_bounded _ p hs₁)
  obtain ⟨hprob,hgτ,hpτ⟩ := normalized_resolved_subplan_optimal π hg hp hfin σ hσ hl hr q
  let τ := ((σ univ)⁻¹ • σ).map (resolvePathBranch q)
  let : IsProbabilityMeasure τ := hprob
  have hmass : 0 < σ.real univ := ENNReal.toReal_pos hσ (measure_ne_top _ _)
  have hD : 0 < 2*(C:ℝ)/σ.real univ := div_pos (mul_pos (by norm_num) hC) hmass
  have hcτ (u : Time) : τ.map (fun γ => γ u) ≤
      ENNReal.ofReal (2*(C:ℝ)/σ.real univ) • hausdorff n X := by
    have he : ENNReal.ofReal (2*(C:ℝ)/σ.real univ)=2*((σ univ)⁻¹*ENNReal.ofReal C) := by
      rw [div_eq_mul_inv,ENNReal.ofReal_mul (mul_nonneg (by norm_num) C.coe_nonneg),
        ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_inv_of_pos hmass]
      rw [show ENNReal.ofReal (σ.real univ)=σ univ from
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
      norm_num
      ring
    rw [he]
    exact normalized_resolved_compression (hausdorff n X) π σ hl hr hc q u
  have hsτ₀ : ∀ᵐ x ∂τ.map (fun γ => γ 0), dist x p ≤ R :=
    normalized_resolved_endpoint_support π σ hr q 0 (Or.inl rfl) hs₀
  have hsτ₁ : ∀ᵐ x ∂τ.map (fun γ => γ 1), dist x p ≤ R :=
    normalized_resolved_endpoint_support π σ hr q 1 (Or.inr rfl) hs₁
  exact bounded_plan_entropy_bounds (hausdorff n X) p hR τ hgτ hpτ hD hcτ hsτ₀ hsτ₁ t

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
