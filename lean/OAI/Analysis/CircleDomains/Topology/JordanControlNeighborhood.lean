import OAI.Analysis.CircleDomains.Topology.AnchoredJordanLimits
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! A quantitative neighborhood for simultaneous inner and outer containment of a Jordan
fill. The interior anchor removes any choice of parametrization or orientation. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_jordan_control_radius
    (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (hγ : Continuous γ)
    (hfront : range γ = frontier (jordanInterior H))
    {z : ℂ} (hz : z ∈ jordanInterior H)
    {K O : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ jordanInterior H)
    (hO : IsOpen O) (hHO : closure (jordanInterior H) ⊆ O) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (γ' : Circle → ℂ) (z' : ℂ) (J : ℂ ≃ₜ ℂ),
      (∀ t, dist (γ' t) (γ t) < δ) → dist z' z < δ →
      range γ' = frontier (jordanInterior J) → z' ∈ jordanInterior J →
      K ⊆ jordanInterior J ∧ closure (jordanInterior J) ⊆ O := by
  by_contra! h
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have htδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose γn zn Jn hclose hzclose hfrontn hzn hfail using fun n => h (δ n) (hδ n)
  have hlim : TendstoUniformly γn γ atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [htδ.eventually (gt_mem_nhds hε)] with n hn t
    simpa only [dist_comm] using (hclose n t).trans hn
  have hzlim : Tendsto zn atTop (𝓝 z) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [htδ.eventually (gt_mem_nhds hε)] with n hn
    exact (hzclose n).trans hn
  have hinner := eventually_compact_subset_jordanInterior_of_anchor H Jn γ γn hγ hfront
    (Eventually.of_forall hfrontn) hlim hz hzlim (Eventually.of_forall hzn) hK hKH
  have houter := eventually_jordan_fill_subset_open H Jn γ γn hγ hfront
    (Eventually.of_forall hfrontn) hlim hO hHO
  obtain ⟨n, hn, hn'⟩ := (hinner.and houter).exists
  exact hfail n hn hn'

end CircleDomainRigidity

end

end OAI
