import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.IncidentFaces
import OAI.Geometry.Cannon.PlanarGraphs.Next

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem vertexLink_order (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    {q : ℂ} (hq : Vertex F q) :
    ∃ n:ℕ,∃ hn:0<n,∃ e:Fin n≃IncidentEdges F q,∃ a:Fin n≃IncidentFaces F q,
      2≤n ∧ (∀ i,(e i).val∈regionEdges F ConnectedComponents.mk (a i).val) ∧
      (∀ i,(e (CannonCycleOrder.next hn i)).val∈regionEdges F ConnectedComponents.mk (a i).val) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hgraph : CannonCycleOrder.bipartite
      (fun (e : IncidentEdges F q) (a : IncidentFaces F q)=>e.val∈regionEdges F ConnectedComponents.mk a.val)=vertexLink F q := by
    ext x y; cases x <;> cases y <;> rfl
  apply CannonCycleOrder.exists_order
    (fun (e : IncidentEdges F q) (a : IncidentFaces F q)=>e.val∈regionEdges F ConnectedComponents.mk a.val)
    (by rw [hgraph]; exact vertexLink_isCycles F hF Q hQ hK hq)
    (by rw [hgraph]; exact vertexLink_preconnected F hF Q hQ hK hq)
  obtain ⟨i,hi⟩ := hq
  have hqi : q∈range (F i) := hi.elim (fun h=>h ▸ ⟨0,rfl⟩) (fun h=>h ▸ ⟨1,rfl⟩)
  obtain ⟨face,_,_,hface,_⟩ := noncut_edge_two_faces F hF Q hQ hK i
  have hqa := region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hface hqi
  exact ⟨⟨i,hqi⟩,⟨face,hqa⟩,hface⟩
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
