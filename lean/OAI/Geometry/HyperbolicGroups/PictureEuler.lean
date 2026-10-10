import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureMap
import OAI.Geometry.HyperbolicGroups.CycleCount
import OAI.Geometry.HyperbolicGroups.PermEuler
import OAI.Geometry.HyperbolicGroups.InvolutionPairs

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap
variable (M : PictureMap D)

/-- Connected components of the actual polygon identifications on darts. -/
def components : Setoid D := SameCycle.setoid M.vertex ⊔ SameCycle.setoid M.edge

omit [DecidableEq D] [Fintype D] in
lemma vertex_le_components : SameCycle.setoid M.vertex ≤ M.components := le_sup_left
omit [DecidableEq D] [Fintype D] in
lemma edge_le_components : SameCycle.setoid M.edge ≤ M.components := le_sup_right

omit [DecidableEq D] in
lemma face_le_components : SameCycle.setoid M.face ≤ M.components := by
  have h := sameCycle_mul_le M.vertex_le_components M.edge_le_components
  have he : M.vertex * M.edge = M.face := by
    rw [vertex,mul_assoc,M.edge_sq,mul_one]
  rwa [he] at h

omit [DecidableEq D] in
lemma components_le {s : Setoid D}
    (hf : ∀ x, s x (M.face x)) (he : ∀ x, s x (M.edge x)) : M.components ≤ s := by
  apply sup_le
  · exact sameCycle_mul_le (sameCycle_le_of_apply hf) (sameCycle_le_of_apply he)
  · exact sameCycle_le_of_apply he

/-- Euler's upper bound for every finite oriented side-pairing, without
assuming a drawing or the surface classification theorem. -/
theorem euler_le : M.euler ≤ 2 * (Nat.card (Quotient M.components) : ℤ) := by
  classical
  obtain ⟨l,hl,hcard,hpairs⟩ := involution_pairs M.edge M.edge_sq
  have hsupp : M.edge.support = Finset.univ := by
    ext x
    simp [mem_support,M.edge_ne]
  rw [hsupp,Finset.card_univ] at hcard
  have hprod : swaps l = M.edge := hl
  have hc : joins (SameCycle.setoid M.vertex) l = M.components := by
    apply le_antisymm
    · apply joins_le _ _ _ M.vertex_le_components
      intro ab hab
      apply M.edge_le_components
      rw [← (hpairs ab hab).2]
      exact SameCycle.rfl.apply_right
    · apply sup_le
      · exact le_joins _ _
      · have h1 : SameCycle.setoid (1 : Perm D) ≤ SameCycle.setoid M.vertex := by
          intro a b hab
          exact (hab.eq_of_left rfl).sameCycle M.vertex
        have h := sameCycle_joins h1 l
        simpa only [one_mul,hprod] using h
  have h := potential_list (p := M.vertex) (s := SameCycle.setoid M.vertex) le_rfl l
  rw [hc,hprod] at h
  have he : M.vertex * M.edge = M.face := by rw [vertex,mul_assoc,M.edge_sq,mul_one]
  rw [he,← cycles_eq_card_classes M.vertex] at h
  have hn : (Fintype.card D : ℤ) = 2 * (l.length : ℤ) := by exact_mod_cast hcard.symm
  have heuler : M.euler = cycles M.vertex + cycles M.face - l.length := by
    rw [euler,hn]
    omega
  rw [heuler]
  omega

/-- Combinatorial genus zero, expressed directly on the actual side-pairing.
This definition neither asserts nor replaces a topological realization. -/
def GenusZero : Prop := M.euler = 2 * (Nat.card (Quotient M.components) : ℤ)

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
