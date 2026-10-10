import OAI.Combinatorics.Crossing.RoundDiskClearance
import OAI.Combinatorics.Crossing.MovingSegmentStability
import Mathlib.Analysis.Convex.PathConnected

namespace OAI

noncomputable section
namespace Zarankiewicz
open scoped Topology

theorem eventually_moving_segment_outside_disk (a b : ℝ → Plane) (ha : Continuous a)
    (hb : Continuous b) (z : Plane) (r : ℝ)
    (hout : segment ℝ (a 0) (b 0) ⊆ {x | r^2 < squaredLength (x-z)}) :
    ∀ᶠ ε : ℝ in 𝓝 0, segment ℝ (a ε) (b ε) ⊆ {x | r^2 < squaredLength (x-z)} := by
  have hevent : ∀ᶠ ε : ℝ in 𝓝 0, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      r^2 < squaredLength (segmentPoint (a ε) (b ε) t-z) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hc : Continuous (fun p : ℝ × ℝ => squaredLength (segmentPoint (a p.1) (b p.1) p.2-z)) := by
      dsimp [squaredLength,segmentPoint]
      fun_prop
    apply continuousAt_const.eventually_lt hc.continuousAt
    apply hout
    rw [← Path.range_segment]
    refine ⟨⟨t,ht⟩,?_⟩
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]
  filter_upwards [hevent] with ε hε
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,rfl⟩ := hx
  simpa only [Set.mem_ofPred_eq,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hε t.val t.property

theorem exists_shifted_segment_disk_radius (a b qa qb z : Plane) (r : ℝ)
    (hdis : Disjoint (closedRoundDisk z r) (segment ℝ a b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε|<δ →
      segment ℝ (a+ε • qa) (b+ε • qb) ⊆ {x | r^2 < squaredLength (x-z)} := by
  have hout : segment ℝ a b ⊆ {x | r^2 < squaredLength (x-z)} := by
    intro x hx
    change r^2 < squaredLength (x-z)
    by_contra hh
    have hmem : x ∈ closedRoundDisk z r := by
      change squaredLength (x-z) ≤ r^2
      exact not_lt.mp hh
    exact Set.disjoint_left.mp hdis hmem hx
  have he := eventually_moving_segment_outside_disk (fun ε : ℝ => a+ε • qa)
    (fun ε : ℝ => b+ε • qb) (by fun_prop) (by fun_prop) z r (by simpa using hout)
  obtain ⟨δ,hδ,hh⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ,hδ,fun ε hε => hh (by simpa [Real.dist_eq] using hε)⟩

end Zarankiewicz

end

end OAI
