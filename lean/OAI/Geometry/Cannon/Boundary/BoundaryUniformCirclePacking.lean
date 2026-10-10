import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryUniformTriangularGraphs
import OAI.Geometry.Cannon.PlaneTopology.BoundaryBallCover
import OAI.Geometry.Cannon.PlaneTopology.DevelopedFaces

namespace OAI

/-! Uniform circle packings associated with boundary triangulations. -/

section
section
section
noncomputable section
namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_circle_packing (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ M L r₀ : ℝ,1≤M ∧ 1≤L ∧ 0<r₀ ∧ ∃ N : ℕ,
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
              B.radius u+B.radius v≤dist (z u) (z v)) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨M,L,r₀,hM,hL,hr₀,N,hgraph⟩ := boundary_uniform_triangular_graphs D hδ φ
  refine ⟨M,L,r₀,hM,hL,hr₀,N,?_⟩
  intro r hr hrs T hsep hcover p hp
  obtain ⟨e,he,heR,κ,H,hκ,hκn,hH,⟨Q,hQ⟩,hT,hK,hE,hD,hN,htri⟩ :=
    hgraph r hr hrs T hsep hcover p hp
  let _ : Finite κ := hκ
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : Nonempty κ := hκn
  have htri' (d : Faces H) : ∃ i j k : κ,i≠j ∧ j≠k ∧ k≠i ∧
      closure (face H d)=face H d∪(range (H i)∪range (H j)∪range (H k)) := by
    obtain ⟨i,j,k,hij,hjk,hki,-,hc⟩ := htri d
    exact ⟨i,j,k,hij,hjk,hki,hc⟩
  let _ : Finite (Faces H) := faces_finite H hH Q hQ
  let _ : Fintype (Faces H) := Fintype.ofFinite (Faces H)
  refine ⟨e,he,heR,κ,inferInstance,Classical.decEq κ,hκn,H,hH,Q,hQ,hT,hK,hE,hD,hN,?_,?_,inferInstance,?_⟩
  · intro v
    apply (Nat.card_le_card_of_injective (β:={i : κ | ∃ t:I,dist (e (H i t)) (e v)<2*M*r})
      (fun (i : {i : κ | v∈range (H i)})=>⟨i.val,?_⟩) (fun a b h=>Subtype.ext (congrArg (fun z : {i : κ | ∃ t:I,dist (e (H i t)) (e v)<2*M*r}=>z.val) h))).trans (hN (e v))
    obtain ⟨t,ht⟩ := i.property
    refine ⟨t,?_⟩
    rw [ht,dist_self]
    positivity
  · exact (CannonPlanarEuler.triangular_counts H hH Q hQ hK htri').1
  · intro out
    have hdata : HasIntrinsicCircleData H out := triangular_graph_radii H hH Q hQ hK htri' out
    obtain ⟨B⟩ := intrinsic_developed_faces H hH Q hQ hK out
      (CannonPlanarEuler.triangular_counts H hH Q hQ hK htri').1 hdata
    exact ⟨B,B.circle_packing hH Q hQ hK (CannonPlanarEuler.triangular_counts H hH Q hQ hK htri').1⟩
end CannonRelease

end
end
end
end

end OAI
