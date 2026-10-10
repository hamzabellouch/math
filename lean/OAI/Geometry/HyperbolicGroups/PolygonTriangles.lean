import Mathlib
import OAI.Geometry.HyperbolicGroups.TriangleCoordinates
import OAI.Geometry.HyperbolicGroups.FinitePolygonModel
import OAI.Geometry.HyperbolicGroups.FinitePolygonVoltage

namespace OAI

/-! Literal ordered collar triangles and exhaustivity of their two-dimensional
faces. No uniqueness of polygon vertices is presumed. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
open FinitePolyhedron FinitePolyhedron.Voltage
variable {V E C : Type*}
  [DecidableEq V] [DecidableEq E] [DecidableEq C] (P : Data V E C)

def collarB (q : P.Position) (j : Fin 3) : P.Vertex :=
  if j.val = 0 then P.base q else P.outer (P.next q)
def collarC (q : P.Position) (j : Fin 3) : P.Vertex :=
  if j.val = 2 then P.apex q.1 else P.base (P.next q)
lemma collarFace_eq (q : P.Position) (j : Fin 3) :
    P.collarFace q j = {P.outer q,P.collarB q j,P.collarC q j} := by
  fin_cases j <;> simp [collarFace,collarB,collarC]
lemma collar_mem (q : P.Position) (j : Fin 3) :
    {P.outer q,P.collarB q j,P.collarC q j} ∈ P.complex.faces := by
  rw [←P.collarFace_eq]
  exact P.facet_face (.inr (q,j))
omit [DecidableEq V] [DecidableEq E] [DecidableEq C] in
lemma collar_injective (q : P.Position) (j : Fin 3) :
    Function.Injective ![P.outer q,P.collarB q j,P.collarC q j] := by
  obtain ⟨a,ha⟩ := P.base_graph q
  obtain ⟨b,hb⟩ := P.base_graph (P.next q)
  have hn := P.base_ne_next q
  have hq := P.next_ne q
  fin_cases j <;> simp only [collarB,collarC]
  all_goals apply three_injective
  all_goals first
    | assumption
    | solve | simp [ha,hb,outer,apex,graph]
    | simpa [outer,eq_comm] using hq

lemma three_face_collar {s : Finset P.Vertex} (hs : s ∈ P.complex.faces) (hc : s.card = 3) :
    ∃ q j, s = P.collarFace q j := by
  rcases hs.2 with hh|⟨f,hf⟩
  · omega
  · cases f with
    | inl e =>
      have hh := Finset.card_le_card hf
      have he : (P.facet (.inl e)).card ≤ 2 := by
        dsimp [facet,graphFace]; split_ifs <;> exact Finset.card_le_two
      omega
    | inr q =>
      refine ⟨q.1,q.2,Finset.eq_of_subset_of_card_le hf ?_⟩
      exact (P.simplex_card_le_three (P.facet_face (.inr q))).trans (by omega)

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
