import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Spans

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval

variable {X ι : Type*} [MetricSpace X] [Fintype ι]
omit [Fintype ι] in
lemma graph_vertices_dense_from_original_net (H : ι → Arc ℂ) (e : ℂ → X)
    (T : Finset X) (r M : ℝ)
    (hT : (T : Set X)⊆e '' (⋃ i,range (H i)))
    (hcover : ∀ x : X,∃ y∈T,dist x y≤r)
    (hE : ∀ i,∀ t s:I,dist (e (H i t)) (e (H i s))≤M*r) :
    ∀ x : X,∃ v : GraphVertices H,dist x (e v.val)≤(1+M)*r := by
  intro x
  obtain ⟨y,hy,hxy⟩:=hcover x
  obtain ⟨z,hz,hez⟩:=hT hy
  obtain ⟨i,t,rfl⟩:=mem_iUnion.mp hz
  refine ⟨⟨H i 0,⟨i,Or.inl rfl⟩⟩,?_⟩
  have hh:=dist_triangle x (e (H i t)) (e (H i 0))
  have ht:=hE i t 0
  rw [hez] at hh ht
  change dist x (e (H i 0)) ≤ (1+M)*r
  nlinarith

omit [Fintype ι] in
lemma separated_graph_marks (H : ι → Arc ℂ) (e : ℂ → X)
    (T : Finset X) (r M s0 : ℝ) (a : Fin 3 → X)
    (hT : (T : Set X)⊆e '' (⋃ i,range (H i)))
    (hcover : ∀ x : X,∃ y∈T,dist x y≤r)
    (hE : ∀ i,∀ t s:I,dist (e (H i t)) (e (H i s))≤M*r)
    (ha : ∀ i j,i≠j → s0≤dist (a i) (a j)) (hs0 : 2*((1+M)*r)<s0) :
    ∃ b : Fin 3 → GraphVertices H,Function.Injective b ∧
      ∀ i,dist (a i) (e (b i).val)≤(1+M)*r := by
  choose b hb using fun i=>graph_vertices_dense_from_original_net H e T r M hT hcover hE (a i)
  refine ⟨b,?_,hb⟩
  intro i j hij
  by_contra hne
  have hd:=dist_triangle (a i) (e (b i).val) (a j)
  have hj:=hb j
  rw [←hij,dist_comm (a j) (e (b i).val)] at hj
  have hi:=hb i
  have hs:=ha i j hne
  linarith
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
