import Mathlib
import OAI.Combinatorics.HoneycombCorridor.Contours

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def faceEdges (a : FaceIndex) : Finset EdgeIndex :=
  {((a.1,a.2),0), ((a.1+1,a.2),0),
   ((a.1+1,a.2-1),1), ((a.1,a.2),1),
   ((a.1+1,a.2),2), ((a.1+1,a.2-1),2)}

def faceVertices (a : FaceIndex) : Finset Vertex :=
  {.up a.1 a.2, .down a.1 (a.2-1), .up (a.1+1) (a.2-1),
   .down a.1 a.2, .up (a.1+1) a.2, .down (a.1+1) (a.2-1)}

def cellEdges (S : Finset FaceIndex) : Finset EdgeIndex := S.biUnion faceEdges

def cellVertices (S : Finset FaceIndex) : Finset Vertex := S.biUnion faceVertices

theorem mem_faceEdges (e : EdgeIndex) (a : FaceIndex) :
    e ∈ faceEdges a ↔ leftFace (canonicalDart e) = a ∨ rightFace (canonicalDart e) = a := by
  rcases e with ⟨⟨i,j⟩,k⟩
  rcases a with ⟨x,y⟩
  fin_cases k <;>
    simp [faceEdges,canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] <;> omega

theorem mem_faceVertices (v : Vertex) (a : FaceIndex) :
    v ∈ faceVertices a ↔ ∃ k : Fin 3, leftFace (v,k) = a := by
  rcases a with ⟨x,y⟩
  cases v <;>
    simp [faceVertices,Fin.exists_fin_succ,leftFace] <;> omega

theorem mem_cellEdges (S : Finset FaceIndex) (e : EdgeIndex) :
    e ∈ cellEdges S ↔ leftFace (canonicalDart e) ∈ S ∨ rightFace (canonicalDart e) ∈ S := by
  simp only [cellEdges,Finset.mem_biUnion,mem_faceEdges]
  constructor
  · rintro ⟨a,ha,h | h⟩
    · exact Or.inl (h ▸ ha)
    · exact Or.inr (h ▸ ha)
  · rintro (h | h)
    · exact ⟨_,h,Or.inl rfl⟩
    · exact ⟨_,h,Or.inr rfl⟩

theorem mem_cellVertices (S : Finset FaceIndex) (v : Vertex) :
    v ∈ cellVertices S ↔ ∃ k : Fin 3, leftFace (v,k) ∈ S := by
  simp only [cellVertices,Finset.mem_biUnion,mem_faceVertices]
  constructor
  · rintro ⟨a,ha,k,hk⟩
    exact ⟨k,hk ▸ ha⟩
  · rintro ⟨k,hk⟩
    exact ⟨_,hk,k,rfl⟩

theorem edge_mem_vertex (S : Finset FaceIndex) (g : Germ)
    (h : edgeOf g ∈ cellEdges S) : g.1 ∈ cellVertices S := by
  rw [mem_cellEdges] at h
  rcases canonicalDart_edgeOf g with hg | hg
  · rw [hg] at h
    rcases h with h | h
    · exact (mem_cellVertices S g.1).mpr ⟨g.2,h⟩
    · rcases g with ⟨v,k⟩
      rw [mem_cellVertices]
      cases v <;> fin_cases k <;>
        simp [rightFace,reverseGerm,neighbor] at h <;>
        simp_all [Fin.exists_fin_succ,leftFace]
  · rw [hg,rightFace_reverse] at h
    rcases h with h | h
    · rcases g with ⟨v,k⟩
      rw [mem_cellVertices]
      cases v <;> fin_cases k <;>
        simp [reverseGerm,neighbor] at h <;>
        simp_all [Fin.exists_fin_succ,leftFace]
    · exact (mem_cellVertices S g.1).mpr ⟨g.2,h⟩

@[simp] theorem edgeOf_reverse (g : Germ) : edgeOf (reverseGerm g) = edgeOf g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [edgeOf,reverseGerm,neighbor]

theorem edge_mem_neighbor (S : Finset FaceIndex) (g : Germ)
    (h : edgeOf g ∈ cellEdges S) : neighbor g.1 g.2 ∈ cellVertices S := by
  exact edge_mem_vertex S (reverseGerm g) (by simpa using h)

end PolynomialVacuumBridge.Corridor

end

end OAI
