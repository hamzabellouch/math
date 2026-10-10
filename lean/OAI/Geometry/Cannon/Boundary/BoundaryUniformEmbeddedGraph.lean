import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.BoundaryControlledEmbeddedArcs
import OAI.Geometry.Cannon.PlaneTopology.SeparatedArcColoring

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
namespace CannonRelease
open Set Metric CannonGraph CannonPacking CannonEmbeddedArc CannonEmbeddedArc.Arc

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_embedded_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ L r₀ : ℝ, 1≤L ∧ 0<r₀ ∧ ∃ K : ℕ, ∀ r : ℝ, 0<r → r≤r₀ →
      ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ x∈T, ∀ y∈T, x≠y → dist x y<4*r →
           Vertex F x ∧ Vertex F y ∧ ∃ b : Arc (Boundary D), b 0=x ∧ b 1=y ∧
             range b ⊆ (⋃ j, range (F j)) ∧ diam (range b)≤3*L*r) ∧
        (∀ j, diam (range (F j))≤L*r) ∧
        (∀ x, intersectionCount F (ball x (2*L*r))≤K) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨L,s₀,hL,hs₀,harc⟩ := boundary_controlled_embedded_arcs D hδ φ
  obtain ⟨Q,C,_,hC,hp⟩ := relative_polynomial_packing D hδ
  have hLpos : 0<L := zero_lt_one.trans_le hL
  obtain ⟨K,hK⟩ := net_arc_graph Q C (2*L) hp hC.le (by linarith)
  refine ⟨2*L,min (s₀/2) (1/(14*L)),by linarith,
    lt_min (half_pos hs₀) (by positivity),K,?_⟩
  intro r hr hrs T hsep
  have hrs₀ : 2*r ≤ s₀ := by have := hrs.trans (min_le_left ..); linarith
  have hscale : 7*(2*L)*r≤1 := by
    have h := hrs.trans (min_le_right ..)
    have hh := (le_div_iff₀ (by positivity : 0<14*L)).mp h
    nlinarith
  apply hK r hr hscale T hsep
  intro x hx y hy hxy hnear
  obtain ⟨a,h₀,h₁,_,hd⟩ := harc (2*r) (by positivity) hrs₀ x y hxy (by linarith)
  exact ⟨a,h₀,h₁,by nlinarith [hd]⟩

end CannonRelease

end
end
end
end
end
end

end OAI
