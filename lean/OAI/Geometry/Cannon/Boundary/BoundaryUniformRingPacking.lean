import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryUniformCirclePacking
import OAI.Geometry.Cannon.PlaneTopology.BoundaryRadiusControl

namespace OAI

/-! Uniform radius control for the boundary circle packings. -/

section
section
section
noncomputable section
namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_ring_packing (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ M L r₀ : ℝ,1≤M ∧ 1≤L ∧ 0<r₀ ∧ ∃ N : ℕ, ∃ c : ℝ,0<c ∧ c≤1 ∧
    ∀ r : ℝ,0<r → r≤r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T,∀ y∈T,x≠y → r≤dist x y) →
      (∀ x : Boundary D,∃ y∈T,dist x y≤r) →
      ∀ p : Boundary D,p∉T →
      ∃ e : ℂ → Boundary D,IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (_ : Nonempty κ) (H : κ → Arc ℂ),
        Pairwise (fun i j=>Compatible (H i) (H j)) ∧
        ∃ Q : Finset (ℂ × ℂ),(∀ i,range (H i)⊆⋃q∈Q,segment ℝ q.1 q.2) ∧
        (T:Set (Boundary D))⊆e '' (⋃ i,range (H i)) ∧
        (∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q})) ∧
        (∀ i,∀ t s : I,dist (e (H i t)) (e (H i s))≤M*r) ∧
        (∀ d,∀ z∈closure (face H d),∀ w∈closure (face H d),dist (e z) (e w)≤L*r) ∧
        (∀ x : Boundary D,Nat.card {i : κ | ∃ t:I,dist (e (H i t)) x<2*M*r}≤N) ∧
        (∀ v : ℂ,Nat.card {i : κ | v∈range (H i)}≤N) ∧
        (∀ d : Faces H,(faceVertices H d).card=3) ∧
        ∃ _ : Fintype (Faces H),∀ out : Faces H,
          ∃ B : DevelopedFaces H out, ∃ z : ℂ → ℂ,
            (∀ d,d≠out → ∀ q∈faceVertices H d,z q=B.chart d q) ∧
            (∀ i,dist (z (H i 0)) (z (H i 1))=B.radius (H i 0)+B.radius (H i 1)) ∧
            (∀ u,Vertex H u → ∀ v,Vertex H v → u≠v →
              B.radius u+B.radius v≤dist (z u) (z v)) ∧
            (∀ j,∀ u v,Spans (H j) u v → c*B.radius u≤B.radius v ∧ c*B.radius v≤B.radius u) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨M,L,r₀,hM,hL,hr₀,N,hgraph⟩ := boundary_uniform_circle_packing D hδ φ
  obtain ⟨c,hc,hc1,hcgraph⟩ := exists_global_radius_constant N
  refine ⟨M,L,r₀,hM,hL,hr₀,N,c,hc,hc1,?_⟩
  intro r hr hrs T hsep hcover p hp
  obtain ⟨e,he,heR,κ,hκ,hκd,hκn,H,hH,Q,hQ,hT,hK,hE,hD,hN,hdeg,htri,hfaces,hpack⟩ :=
    hgraph r hr hrs T hsep hcover p hp
  let _ : Fintype κ := hκ
  let _ : DecidableEq κ := hκd
  let _ : Nonempty κ := hκn
  let _ : Fintype (Faces H) := hfaces
  refine ⟨e,he,heR,κ,hκ,hκd,hκn,H,hH,Q,hQ,hT,hK,hE,hD,hN,hdeg,htri,hfaces,?_⟩
  intro out
  obtain ⟨B,z,hz,hlen,hdis⟩:=hpack out
  obtain ⟨O⟩:=facialCycle_exists H hH Q hQ hK out (htri out)
  refine ⟨B,z,hz,hlen,hdis,?_⟩
  intro j u v huv
  constructor
  · exact hcgraph H out B hH Q hQ hK z hz hlen hdis O u v j huv.vertex_left (hdeg u) huv
  · exact hcgraph H out B hH Q hQ hK z hz hlen hdis O v u j huv.vertex_right (hdeg v) huv.symm
end CannonRelease

end
end
end
end

end OAI
