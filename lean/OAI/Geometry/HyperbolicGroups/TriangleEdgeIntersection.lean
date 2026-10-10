import Mathlib
import OAI.Geometry.HyperbolicGroups.EdgeCoordinates
import OAI.Geometry.HyperbolicGroups.TriangleCoordinates
import OAI.Geometry.HyperbolicGroups.TriangleSquareFurther

namespace OAI

/-! A nondegenerate triangular simplex meets every edge in its boundary. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}

lemma triangle_boundary_of_edge {a b c d e : V} (h : {a,b,c} ∈ K.faces)
    (hi : Function.Injective ![a,b,c]) (h' : {d,e} ∈ K.faces)
    (z : Triangle) (r : I) (he : (trianglePoint h z).val = edgePath K h' r) :
    (∃ s, z = quotient (s,0)) ∨ (∃ s, z = quotient (0,s)) ∨ (∃ s, z = quotient (1,s)) := by
  have hab : a ≠ b := by intro hh; have := hi (a₁:=0) (a₂:=1) hh; exact (by decide : (0:Fin 3) ≠ 1) this
  have hac : a ≠ c := by intro hh; have := hi (a₁:=0) (a₂:=2) hh; exact (by decide : (0:Fin 3) ≠ 2) this
  have hbc : b ≠ c := by intro hh; have := hi (a₁:=1) (a₂:=2) hh; exact (by decide : (1:Fin 3) ≠ 2) this
  have hn : ¬ ({a,b,c} : Finset V) ⊆ {d,e} := by
    intro hs
    have hc := Finset.card_le_card hs
    have hc' := Finset.card_le_two (a:=d) (b:=e)
    have h3 : ({a,b,c} : Finset V).card = 3 := by simp [hab,hac,hbc]
    omega
  obtain ⟨j,hj,hjn⟩ := Finset.not_subset.mp hn
  have hz (i : Fin 3) (hij : ![a,b,c] i = j) : z.val i = 0 := by
    rw [←trianglePoint_coordinate h hi z i,hij]
    have hh := congrArg (fun x : Carrier K => x.val j) he
    rw [edgePath_coordinate] at hh
    have hd : j ≠ d := fun h => hjn (by simp [h])
    have he : j ≠ e := fun h => hjn (by simp [h])
    simpa [hd,he] using hh
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl|rfl|rfl
  · exact Or.inr (Or.inr ⟨_,eq_right_of_zero z (hz 0 rfl)⟩)
  · exact Or.inr (Or.inl ⟨_,eq_left_of_zero z (hz 1 rfl)⟩)
  · exact Or.inl ⟨_,eq_bottom_of_zero z (hz 2 rfl)⟩

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
