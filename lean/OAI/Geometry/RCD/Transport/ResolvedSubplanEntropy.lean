import OAI.Geometry.RCD.Transport.ResolvedSubplanCompression
import OAI.Geometry.RCD.Transport.BoundedPlanEntropyChord

namespace OAI

/-! # Entropy convexity for the actual normalized resolved branch family -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem resolved_subplan_entropy_chord (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ] (hσ : σ univ ≠ 0)
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π) (q s t r : Time) :
    let τ := ((σ univ)⁻¹ • σ).map (resolvePathBranch q)
    boltzmannEntropy (hausdorff n X) (τ.map (fun γ => γ (timeSegment s t r))) ≤
      (1-(r:ℝ))*boltzmannEntropy (hausdorff n X) (τ.map (fun γ => γ s))+
      (r:ℝ)*boltzmannEntropy (hausdorff n X) (τ.map (fun γ => γ t))+
      (|K|/2)*(2*R)^2*(r:ℝ)*(1-(r:ℝ))*|(s:ℝ)-(t:ℝ)|^2 := by
  have hfin := coupling_transportCost_ne_top hp.1 hp.2.1 p
    (integrable_dist_sq_of_ae_bounded _ p hs₀) (integrable_dist_sq_of_ae_bounded _ p hs₁)
  obtain ⟨hprob,hgτ,hpτ⟩ := normalized_resolved_subplan_optimal π hg hp hfin σ hσ hl hr q
  let τ := ((σ univ)⁻¹ • σ).map (resolvePathBranch q)
  let : IsProbabilityMeasure τ := hprob
  let c := (σ univ)⁻¹
  have hct : c≠∞ := ENNReal.inv_ne_top.mpr hσ
  let B : ℝ≥0 := ⟨2*(c.toReal*(C:ℝ)),mul_nonneg (by norm_num)
    (mul_nonneg ENNReal.toReal_nonneg C.coe_nonneg)⟩
  have hB : ENNReal.ofReal B=2*(c*ENNReal.ofReal C) := by
    change ENNReal.ofReal ((2:ℝ)*(c.toReal*(C:ℝ)))=_
    rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hct]
    norm_num
  have hcτ (u : Time) : τ.map (fun γ => γ u) ≤ ENNReal.ofReal B • hausdorff n X := by
    rw [hB]
    exact normalized_resolved_compression (hausdorff n X) π σ hl hr hcomp q u
  have hτ₀ : ∀ᵐ x ∂τ.map (fun γ => γ 0), dist x p ≤ R :=
    normalized_resolved_endpoint_support π σ hr q 0 (Or.inl rfl) hs₀
  have hτ₁ : ∀ᵐ x ∂τ.map (fun γ => γ 1), dist x p ≤ R :=
    normalized_resolved_endpoint_support π σ hr q 1 (Or.inr rfl) hs₁
  exact hX.bounded_plan_entropy_chord hn p hR τ hgτ hpτ hcτ hτ₀ hτ₁ s t r

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
