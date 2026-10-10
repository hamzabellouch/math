import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.NetArcGraphSet
import OAI.Geometry.Cannon.PlanarGraphs.Plane

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

noncomputable section
open Set Metric Topology

namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonEmbeddedArc CannonEmbeddedArc.Arc CannonRegularDisk

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_finite_face_graph (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ A L r₀ : ℝ, 1≤A ∧ 1≤L ∧ 0<r₀ ∧ ∃ K : ℕ,
      ∀ r : ℝ, 0<r → r≤r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T, ∀ y∈T, x≠y → r≤dist x y) →
      (∀ x : Boundary D, ∃ y∈T, dist x y≤r) →
      ∀ p : Boundary D, p∉T →
      ∃ e : Plane → Boundary D, IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ P : Finset (Plane×Plane), ∃ n : ℕ, ∃ F : Fin n → Arc (Boundary D),
        Pairwise (fun e f => Compatible (F e) (F f)) ∧
        (∀ j, diam (range (F j))≤A*r) ∧
        (∀ x, intersectionCount F (ball x (2*A*r))≤K) ∧
        IsPathConnected ((⋃ j, range (F j))∪(T:Set (Boundary D))) ∧
        (((⋃ j, range (F j))∪(T:Set (Boundary D)))⊆e '' (⋃ q∈P, segment ℝ q.1 q.2)) ∧
        Finite (ConnectedComponents ((((⋃ j, range (F j))∪(T:Set (Boundary D)))ᶜ) : Set (Boundary D))) ∧
        (∀ S : Set (Boundary D), IsPreconnected S →
          S⊆((⋃ j, range (F j))∪(T:Set (Boundary D)))ᶜ →
          ∀ x∈S, ∀ y∈S, dist x y<L*r) := by
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyConnectedSpace (Boundary D) := φ.locallyConnectedSpace
  let _ : PathConnectedSpace SphereTwo := CannonPaths.sphere_pathConnected
  let _ : PathConnectedSpace (Boundary D) := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  dsimp only
  obtain ⟨A,L,r₀,hA,hL,hr₀,K,hgraph⟩ := boundary_uniform_connected_polygonal_complement_graph D hδ φ
  refine ⟨A,L,r₀,hA,hL,hr₀,K,?_⟩
  intro r hr hrs T hsep hcover p hpT
  obtain ⟨e,he,heR,P,n,F,hFc,hFd,hFt,hconn,hFS,hsmall⟩ := hgraph r hr hrs T hsep hcover p hpT
  refine ⟨e,he,heR,P,n,F,hFc,hFd,hFt,hconn,hFS,?_,hsmall⟩
  have hclosed : IsClosed ((⋃ j, range (F j))∪(T:Set (Boundary D))) :=
    (isClosed_iUnion_of_finite (fun j => (F j).compact_range.isClosed)).union T.finite_toSet.isClosed
  exact CannonFiniteFaces.finite_components_chart_support e he p heR hclosed P hFS
end CannonRelease

end
end
end
end
end
end
end
end
end

end OAI
