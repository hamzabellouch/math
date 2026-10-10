import Mathlib
import OAI.Geometry.Cannon.Boundary.WordBall
import OAI.Geometry.Cannon.PlaneTopology.IncidentEdges

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonRelease
open Set Metric CannonGraph CannonRegularDisk CannonEmbeddedArc

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_controlled_embedded_arcs (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ L r₀ : ℝ, 1≤L ∧ 0<r₀ ∧ ∀ r : ℝ, 0<r → r≤r₀ →
      ∀ x y : Boundary D, x≠y → dist x y<2*r →
        ∃ a : Arc (Boundary D), a 0=x ∧ a 1=y ∧
          range a ⊆ ball x (L*r) ∧ Metric.diam (range a) ≤ L*r := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨c,hc,hc₁,hdisks⟩ := boundary_controlled_regular_disks D hδ φ
  refine ⟨4/c,c/2,(one_le_div hc).mpr (by linarith),half_pos hc,?_⟩
  intro r hr hrc x y hxy hd
  let s := 2*r/c
  have hs : 0<s := div_pos (by positivity) hc
  have hs₁ : s≤1 := (div_le_one hc).mpr (by linarith)
  have hcs : c*s=2*r := by dsimp [s]; field_simp
  obtain ⟨U,hU,hinner,houter⟩ := hdisks x s hs hs₁
  have hxU : x∈U := hinner (mem_ball_self (mul_pos hc hs))
  have hyU : y∈U := hinner (by simpa only [mem_ball,dist_comm,hcs] using hd)
  obtain ⟨a,ha₀,ha₁,haU⟩ := hU.exists_arc hxU hyU hxy
  have harange : range a ⊆ ball x s := haU.trans (subset_closure.trans houter)
  have heq : 2*s=(4/c)*r := by dsimp [s]; ring
  refine ⟨a,ha₀,ha₁,harange.trans (ball_subset_ball ?_),?_⟩
  · rw [←heq]
    linarith
  · rw [←heq]
    exact Metric.diam_le_of_subset_closedBall hs.le (harange.trans ball_subset_closedBall)

end CannonRelease

end
end
end
end
end
end

end OAI
