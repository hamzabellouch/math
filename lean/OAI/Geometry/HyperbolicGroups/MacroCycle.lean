import Mathlib
import OAI.Geometry.HyperbolicGroups.MacroCertificate

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.MacroGraph
open IncidenceTemplate

/-- Every nonempty vertex subset all of whose vertices have two distinct
neighbors in the subset contains at least three point vertices. -/
theorem three_points (S : Finset Vertex) (hne : S.Nonempty)
    (hn : ∀ v ∈ S, ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Adjacent v a ∧ Adjacent v b) :
    3 ≤ (Finset.univ.filter (fun i => point i ∈ S)).card := by
  classical
  by_contra! hc
  let P := Finset.univ.filter (fun i => point i ∈ S)
  have hP : P.card ≤ 2 := by dsimp [P]; omega
  obtain ⟨p,q,hpq⟩ : ∃ p q : Fin 7, ∀ i ∈ P, i = p ∨ i = q := by
    rcases Nat.lt_or_eq_of_le hP with h | h
    · have h' : P.card ≤ 1 := by omega
      by_cases hp : P.Nonempty
      · obtain ⟨p,hp⟩ := hp
        exact ⟨p,p,fun i hi => Or.inl ((Finset.card_le_one.mp h') i hi p hp)⟩
      · exact ⟨0,0,fun i hi => False.elim (hp ⟨i,hi⟩)⟩
    · obtain ⟨p,q,_,hpq⟩ := Finset.card_eq_two.mp h
      refine ⟨p,q,?_⟩
      intro i hi
      simpa only [hpq,Finset.mem_insert,Finset.mem_singleton] using hi
  have ha : ∀ v ∈ S, Allowed p q v := by
    intro v hv
    rcases v with ((i|l)|⟨⟩)
    · apply hpq i
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    · trivial
    · trivial
  obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image S (rank p q) hne
  obtain ⟨a,haS,b,hbS,hab,hva,hvb⟩ := hn v hv
  exact hab (certificate p q v a b ⟨ha v hv, ha a haS, ha b hbS, hva, hvb,
    hmin a haS, hmin b hbS⟩)

/-- A cyclic simple macro polygon with at least three sides, expressed by its
actual vertices and successor. The normal-form splitting must produce this
data; all template bounds below are derived. -/
structure Polygon where
  n : ℕ
  vertex : Fin n → Vertex
  next : Equiv.Perm (Fin n)
  injective : Function.Injective vertex
  adjacent : ∀ i, Adjacent (vertex i) (vertex (next i))
  no_backtrack : ∀ i, next (next i) ≠ i

namespace Polygon
variable (P : Polygon)

def vertices : Finset Vertex := Finset.univ.image P.vertex

def points : Finset (Fin 7) := Finset.univ.filter (fun i => point i ∈ P.vertices)

lemma perimeter_le : P.n ≤ 15 := by
  have h := Fintype.card_le_of_injective P.vertex P.injective
  simpa [Vertex] using h

lemma two_neighbors : ∀ v ∈ P.vertices, ∃ a ∈ P.vertices, ∃ b ∈ P.vertices,
    a ≠ b ∧ Adjacent v a ∧ Adjacent v b := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  refine ⟨P.vertex (P.next i),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,
    P.vertex (P.next.symm i),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,?_,P.adjacent i,?_⟩
  · intro h
    have hi := P.injective h
    have he := congrArg P.next hi
    simp only [Equiv.apply_symm_apply] at he
    exact P.no_backtrack i he
  · have h := adjacent_symm (P.adjacent (P.next.symm i))
    simpa only [Equiv.apply_symm_apply] using h

lemma points_ge (h : 0 < P.n) : 3 ≤ P.points.card := by
  apply three_points P.vertices _ P.two_neighbors
  exact ⟨P.vertex ⟨0,h⟩,Finset.mem_image.mpr ⟨⟨0,h⟩,Finset.mem_univ _,rfl⟩⟩

end Polygon
end HyperbolicObstruction.MacroGraph
end
end

section

end
end

end OAI
