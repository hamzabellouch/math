import OAI.Combinatorics.Crossing.DrawingPorts
import OAI.Combinatorics.Crossing.VertexDiskSpokes

namespace OAI

noncomputable section
namespace Zarankiewicz.DrawingPassages
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n}

def vertexMark (_C : DrawingPassages D) (v : BipartiteVertex m n) : DrawingMark D :=
  ⟨D.vertex v,Or.inl ⟨v,rfl⟩⟩

theorem vertexMark_injective (C : DrawingPassages D) : Function.Injective C.vertexMark := by
  intro v w he
  exact D.vertex_injective (congrArg Subtype.val he)

theorem exists_drawing_vertex_placement (C : DrawingPassages D) :
    ∃ v : BipartiteVertex m n → Plane, Function.Injective v ∧
      (∀ i, squaredLength (v i-D.vertex i) < C.radius^2) ∧
      (∀ i (p : C.PortsAt (C.vertexMark i)), v i ≠ C.portPoint p.val) ∧
      (∀ i (p q : C.PortsAt (C.vertexMark i)), p ≠ q →
        det2 (C.portPoint p.val-v i) (C.portPoint q.val-v i) ≠ 0) := by
  classical
  have hex (i : BipartiteVertex m n) : ∃ v : Plane,
      squaredLength (v-D.vertex i) < C.radius^2 ∧
      (∀ p : C.PortsAt (C.vertexMark i), v ≠ C.portPoint p.val) ∧
      (∀ p q : C.PortsAt (C.vertexMark i), p ≠ q → det2 (C.portPoint p.val-v) (C.portPoint q.val-v) ≠ 0) :=
    exists_vertex_disk_point (D.vertex i) C.radius C.radius_pos
      (fun p : C.PortsAt (C.vertexMark i) => C.portPoint p.val)
      (C.portPoint_injective.comp Subtype.val_injective) (C.portsAt_on_circle (C.vertexMark i))
  choose v hv hne hdet using hex
  refine ⟨v,?_,hv,hne,hdet⟩
  intro i j he
  by_contra hij
  have hd := C.disks_disjoint (C.vertexMark i) (C.vertexMark j) (C.vertexMark_injective.ne hij)
  have hi : v i ∈ closedRoundDisk (C.vertexMark i).val C.radius := (hv i).le
  have hj : v j ∈ closedRoundDisk (C.vertexMark j).val C.radius := (hv j).le
  exact Set.disjoint_left.mp hd hi (he.symm ▸ hj)

theorem vertex_spoke_injective (C : DrawingPassages D) (v : BipartiteVertex m n → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark i)) :
    Function.Injective (Path.segment (v i) (C.portPoint p.val)) := by
  apply Path.segment_injective_of_ne
  intro he
  have h := hv i
  have hp : squaredLength (C.portPoint p.val-D.vertex i)=C.radius^2 := C.portsAt_on_circle (C.vertexMark i) p
  rw [he,hp] at h
  exact lt_irrefl _ h

theorem vertex_spoke_interior (C : DrawingPassages D) (v : BipartiteVertex m n → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : BipartiteVertex m n) (p : C.PortsAt (C.vertexMark i)) (t : unitInterval)
    (ht : t < 1) : squaredLength ((Path.segment (v i) (C.portPoint p.val)) t-D.vertex i) < C.radius^2 := by
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact spoke_in_open_disk (D.vertex i) (v i) (C.portPoint p.val) C.radius (hv i)
    (C.portsAt_on_circle (C.vertexMark i) p) t.val ⟨t.property.1,ht⟩

end Zarankiewicz.DrawingPassages

end

end OAI
