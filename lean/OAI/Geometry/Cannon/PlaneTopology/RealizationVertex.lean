import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.GraphVerticesDenseOriginal
import OAI.Geometry.Cannon.Conformal.NormalizePackingCenters

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval
open scoped OnePoint

variable {X ι : Type*} [MetricSpace X] [Fintype ι]
omit [MetricSpace X] [Fintype ι] in
lemma realization_at_vertex (H : ι → Arc ℂ) (e : ℂ → X)
    (z : ℂ → ℂ) (f : X → OnePoint ℂ)
    (hfedge : ∀ i t,f (e (H i t))=((Path.segment (z (H i 0))
      (z (H i 1)) t:ℂ):OnePoint ℂ)) (v : GraphVertices H) :
    f (e v.val)=(z v.val:OnePoint ℂ) := by
  obtain ⟨i,hi|hi⟩:=v.property
  · rw [←hi,hfedge]
    simp
  · rw [←hi,hfedge]
    simp

omit [Fintype ι] in
theorem packing_center_normalized_realization (H : ι → Arc ℂ) (e : ℂ → X)
    (T : Finset X) (mesh M sep : ℝ) (a : Fin 3 → X)
    (hT : (T : Set X)⊆e '' (⋃ i,range (H i)))
    (hcover : ∀ x : X,∃ y∈T,dist x y≤ mesh)
    (hE : ∀ i,∀ t s:I,dist (e (H i t)) (e (H i s))≤M*mesh)
    (ha : ∀ i j,i≠j → sep≤dist (a i) (a j)) (hsep : 2*((1+M)*mesh)<sep)
    (z : ℂ → ℂ) (rad : ℂ → ℝ) (hr : ∀ v,Vertex H v → 0<rad v)
    (hdis : ∀ u,Vertex H u → ∀ v,Vertex H v → u≠v → rad u+rad v≤dist (z u) (z v))
    (f : C(X,OnePoint ℂ)) (hfs : Function.Surjective f)
    (hfedge : ∀ i t,f (e (H i t))=((Path.segment (z (H i 0))
      (z (H i 1)) t:ℂ):OnePoint ℂ)) :
    ∃ b : Fin 3 → GraphVertices H,Function.Injective b ∧
      (∀ i,dist (a i) (e (b i).val)≤(1+M)*mesh) ∧
      ∃ N : OnePoint ℂ≃ₜOnePoint ℂ,N∈CannonMobius.biholomorphic ∧
        ∃ g : C(X,OnePoint ℂ),(∀ x,g x=N (f x)) ∧ Function.Surjective g ∧
          (∀ i,g (e (b i).val)=CannonMobius.std i) ∧
          (∀ v : GraphVertices H,IsOpen
            (N '' ((↑) '' ball (z v.val) (rad v.val) : Set (OnePoint ℂ)))) ∧
          Pairwise (fun u v : GraphVertices H=>Disjoint
            (N '' ((↑) '' ball (z u.val) (rad u.val) : Set (OnePoint ℂ)))
            (N '' ((↑) '' ball (z v.val) (rad v.val) : Set (OnePoint ℂ)))) ∧
          (∀ v : GraphVertices H,∃ i j : Fin 3,i≠j ∧
            CannonMobius.std i∉N '' ((↑) '' ball (z v.val) (rad v.val) : Set (OnePoint ℂ)) ∧
            CannonMobius.std j∉N '' ((↑) '' ball (z v.val) (rad v.val) : Set (OnePoint ℂ))) := by
  obtain ⟨b,hb,hba⟩:=separated_graph_marks H e T mesh M sep a hT hcover hE ha hsep
  obtain ⟨N,hN,hNb,hNo,hNd,hNmarks⟩:=CannonMobius.normalize_packing_centers
    (fun v : GraphVertices H=>z v.val) (fun v=>rad v.val) (fun v=>hr v.val v.property)
    (fun u v huv=>hdis u.val u.property v.val v.property (fun h=>huv (Subtype.ext h))) b hb
  let g : C(X,OnePoint ℂ):=⟨fun x=>N (f x),N.continuous.comp f.continuous⟩
  refine ⟨b,hb,hba,N,hN,g,fun x=>rfl,N.surjective.comp hfs,?_,hNo,hNd,hNmarks⟩
  intro i
  change N (f (e (b i).val))=CannonMobius.std i
  rw [realization_at_vertex H e z f hfedge]
  exact hNb i
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
