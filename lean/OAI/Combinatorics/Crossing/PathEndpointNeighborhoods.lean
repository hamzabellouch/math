import OAI.Combinatorics.Crossing.PathSubarc
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem path_near_endpoints {a b : Plane} (γ : Path a b) (ρ σ : ℝ)
    (hρ : 0 < ρ) (hσ : 0 < σ) :
    ∃ u v : unitInterval, 0 < u ∧ u < v ∧ v < 1 ∧
      dist (γ u) a < ρ ∧ dist (γ v) b < σ := by
  have he0 : ∀ᶠ t : ℝ in 𝓝 0, γ.extend t ∈ Metric.ball a ρ :=
    γ.continuous_extend.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds a hρ)
  have he1 : ∀ᶠ t : ℝ in 𝓝 1, γ.extend t ∈ Metric.ball b σ :=
    γ.continuous_extend.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds b hσ)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he0
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he1
  let p := min (δ/2) (1/4)
  let q := min (ε/2) (1/4)
  have hp : 0 < p := lt_min (by positivity) (by norm_num)
  have hq : 0 < q := lt_min (by positivity) (by norm_num)
  have hp4 : p ≤ 1/4 := min_le_right _ _
  have hq4 : q ≤ 1/4 := min_le_right _ _
  have hpd : p < δ := (min_le_left _ _).trans_lt (by linarith)
  have hqe : q < ε := (min_le_left _ _).trans_lt (by linarith)
  let u : unitInterval := ⟨p,hp.le,by linarith⟩
  let v : unitInterval := ⟨1-q,by linarith,by linarith⟩
  have hu : γ.extend p ∈ Metric.ball a ρ := hd (by simpa [Real.dist_eq,abs_of_pos hp] using hpd)
  have hv : γ.extend (1-q) ∈ Metric.ball b σ := he (by
    simpa [Real.dist_eq,abs_of_pos hq] using hqe)
  rw [show γ.extend p=γ u from γ.extend_extends' u] at hu
  rw [show γ.extend (1-q)=γ v from γ.extend_extends' v] at hv
  exact ⟨u,v,hp,(by change p < 1-q; linarith),(by change 1-q < 1; linarith),hu,hv⟩

end Zarankiewicz

end

end OAI
