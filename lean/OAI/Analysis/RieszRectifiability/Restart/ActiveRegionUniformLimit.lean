import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSurfaces
import OAI.Analysis.RieszRectifiability.Limits.GeometricUniformLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_active_region_limit_map {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) :
    ∃ f : S (supportCellRoot μ R hR k z) → Ambient d,
      Continuous f ∧
      TendstoUniformly (fun t (u : S (supportCellRoot μ R hR k z)) =>
        activeRegionParameterMap μ R hR k z Good S hS t u) f atTop ∧
      (∀ t (u : S (supportCellRoot μ R hR k z)),
        dist (activeRegionParameterMap μ R hR k z Good S hS t u) (f u) ≤
        ((17039360 * ε) / 63) * latticeRadius R (k + t)) ∧
      (∀ u, dist (f u) (u : Ambient d) ≤ ((17039360 * ε) / 63) * latticeRadius R k) := by
  let F : ℕ → S (supportCellRoot μ R hR k z) → Ambient d :=
    fun t u => activeRegionParameterMap μ R hR k z Good S hS t u
  let C := (17039360 * ε) * latticeRadius R (k + 1)
  have hcont : ∀ t, Continuous (F t) := by
    intro t
    exact (activeRegionParameterMap_continuous μ R hR k z Good S hS t).comp continuous_subtype_val
  have hstep : ∀ t u, dist (F t u) (F (t + 1) u) ≤ C * (1 / 64 : ℝ) ^ t := by
    intro t u
    have hu : F t u ∈ activeRegionSurface μ R hR k z Good S hS t := by
      rw [activeRegionSurface_eq_image]
      exact ⟨u, u.property, rfl⟩
    have h := activeRegionSurface_successor_displacement μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit t (F t u) hu
    have heq : (17039360 * ε) * latticeRadius R (k + (t + 1)) = C * (1 / 64 : ℝ) ^ t := by
      rw [show k + (t + 1) = k + 1 + t by omega, latticeRadius_add]
      dsimp [C]
      ring
    rw [heq] at h
    simpa only [F, activeRegionParameterMap, Function.comp_apply, dist_comm] using! h
  obtain ⟨f, hfCont, hfUnif, hfBound⟩ := exists_continuous_uniform_limit_of_geometric_steps
    F C (1 / 64) (by norm_num) (by norm_num) hcont hstep
  have htail : ∀ t u, dist (F t u) (f u) ≤ ((17039360 * ε) / 63) * latticeRadius R (k + t) := by
    intro t u
    have heq : C * (1 / 64 : ℝ) ^ t / (1 - (1 / 64 : ℝ)) =
        ((17039360 * ε) / 63) * latticeRadius R (k + t) := by
      dsimp [C]
      rw [latticeRadius_succ, latticeRadius_add]
      ring
    exact (hfBound t u).trans_eq heq
  refine ⟨f, hfCont, hfUnif, htail, ?_⟩
  intro u
  simpa only [F, activeRegionParameterMap, id_eq, Nat.add_zero, dist_comm] using! htail 0 u

end

end RieszRectifiability

end OAI
