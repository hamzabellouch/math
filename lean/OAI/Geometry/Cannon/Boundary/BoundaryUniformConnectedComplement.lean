import Mathlib
import OAI.Geometry.Cannon.Boundary.ExpansionGlobalUpper
import OAI.Geometry.Cannon.PlaneTopology.Lift
import OAI.Geometry.Cannon.PlaneTopology.IntersectionCountEmbedding

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonEmbeddedArc CannonEmbeddedArc.Arc

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_connected_complement_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A L r₀ : ℝ, 1≤A ∧ 1≤L ∧ 0<r₀ ∧ ∃ K : ℕ,
      ∀ r : ℝ, 0<r → r≤r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y≤r) →
      ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        IsPathConnected ((⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
        (∀ S : Set (Boundary D), IsPreconnected S →
          S⊆((⋃ j, range (F j))∪(T:Set (Boundary D)))ᶜ →
          ∀ x∈S, ∀ y∈S, dist x y<L*r) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨A,B,rG,hA,hB,hrG,K,hgraph⟩ := boundary_uniform_connected_loop_graph D hδ φ
  obtain ⟨C,η,hC,hη,hexpand⟩ := boundary_uniform_expanding_homeomorphs D hδ
  obtain ⟨L,hL,hseparate⟩ := CannonWinding.loop_approximation_separates φ hC hB hη hexpand
  have hLp : 0<L := zero_lt_one.trans_le hL
  refine ⟨A,L,min rG (1/L),hA,hL,lt_min hrG (one_div_pos.mpr hLp),K,?_⟩
  intro r hr hrs T hsep hcover
  obtain ⟨n,F,hFc,hFd,hFt,hconn,happrox⟩ := hgraph r hr (hrs.trans (min_le_left ..)) T hsep hcover
  refine ⟨n,F,hFc,hFd,hFt,hconn,?_⟩
  apply hseparate r hr (hrs.trans (min_le_right ..))
  intro f hf
  obtain ⟨H,hH₀,hH₁,hHc,hHd⟩ := happrox f hf
  let g : C(I,Boundary D) := ⟨fun t => H (1,t),by fun_prop⟩
  refine ⟨g,hHc 1,?_,?_⟩
  · rintro _ ⟨t,rfl⟩
    exact hH₁ t
  · intro t
    change dist (H (1,t)) (f t)<B*r
    rw [←hH₀ t]
    exact hHd 1 0 t

end CannonRelease

end
end
end
end
end
end
end
end

end OAI
