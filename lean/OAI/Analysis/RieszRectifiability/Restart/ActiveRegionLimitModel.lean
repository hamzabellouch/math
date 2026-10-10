import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLocalStabilization
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionZeroSetCapture
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSurfaceModel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

def IsActiveRegionLimitModel {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ)
    (f : S (supportCellRoot μ R hR k z) → Ambient d) : Prop :=
  Continuous f ∧ IsProperMap f ∧
  TendstoUniformly (fun t (u : S (supportCellRoot μ R hR k z)) =>
    activeRegionParameterMap μ R hR k z Good S hS t u) f atTop ∧
  (∀ t (u : S (supportCellRoot μ R hR k z)),
    dist (activeRegionParameterMap μ R hR k z Good S hS t u) (f u) ≤
      ((17039360 * ε) / 63) * latticeRadius R (k + t)) ∧
  cellRegionZeroSet μ R hR k z Good ⊆ Set.range f ∧
  cellRegionLimit μ R hR k z Good ⊆ Set.range f ∧
  ∀ (K : Set (Ambient d)) (δ : ℝ), 0 < δ →
    (∀ x ∈ K, δ ≤ cellRegionStoppingScale μ R hR k z Good x) →
    ∃ N, ∀ t, N ≤ t → Set.range f ∩ K = activeRegionSurface μ R hR k z Good S hS t ∩ K

theorem exists_active_region_limit_model {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) :
    ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
      IsActiveRegionLimitModel μ R hR k z Good S hS ε f := by
  obtain ⟨f, hf, hUnif, htail, _⟩ := exists_active_region_limit_map μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit
  obtain ⟨hproper, hsurvivors⟩ := active_region_limit_captures_region_limit μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hf htail
  have hclosed : IsClosed (Set.range f) := by
    simpa only [Set.image_univ] using! hproper.isClosedMap Set.univ isClosed_univ
  have hzero := active_region_limit_captures_zero_set μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hclosed htail
  refine ⟨f, hf, hproper, hUnif, htail, hzero, hsurvivors, ?_⟩
  intro K δ hδ hK
  exact active_region_limit_eq_finite_on_scale_set μ R hR k z Good S hS f
    (fun u => hUnif.tendsto_at u) ((17039360 * ε) / 63) (by positivity) htail K δ hδ hK

theorem exists_actual_active_region_limit_model {n d : ℕ} (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 268435456 ∧ activeProjectionError d ε ≤ 1 / 128 ∧
      let Good := fun q : SupportCellDescendant μ R hR k z =>
        bilateralBeta n μ q.center (1024 * q.radius) < ε
      ∃ (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
        (hS : ∀ i, IsAffineNPlane n (S i)),
        (∀ i, activeRegionCell Good i → bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) ∧
        ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
          IsActiveRegionLimitModel μ R hR k z Good S hS ε f := by
  obtain ⟨ε, hε, hεtiny, hsmall⟩ := exists_active_surface_precision d
  let Good := fun q : SupportCellDescendant μ R hR k z =>
    bilateralBeta n μ q.center (1024 * q.radius) < ε
  obtain ⟨S, hS, hfit, _⟩ := exists_active_level_projection_maps μ R hR k z hnd ε hε
  exact ⟨ε, hε, hεtiny, hsmall, S, hS, hfit,
    exists_active_region_limit_model μ R hR k z Good S hS ε hε hεtiny hsmall hfit⟩

end

end RieszRectifiability

end OAI
