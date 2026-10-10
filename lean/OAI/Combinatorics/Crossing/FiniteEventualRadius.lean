import OAI.Combinatorics.Crossing.FiniteSeparation
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace OAI

namespace Zarankiewicz
open scoped Topology

theorem finite_eventual_radius {ι : Type*} [Fintype ι] (P : ι → ℝ → Prop)
    (h : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, P i t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ i, P i t := by
  have hex (i : ι) : ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| < r → P i t := by
    obtain ⟨r,hr,hh⟩ := Metric.eventually_nhds_iff.mp (h i)
    exact ⟨r,hr,fun t ht => hh (by simpa [Real.dist_eq] using ht)⟩
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun i _ => hpos i)
  exact ⟨δ,hδ,fun t ht i => hprop i t (ht.trans (hbound i (Finset.mem_univ _)))⟩

end Zarankiewicz

end OAI
