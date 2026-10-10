import OAI.Probability.SwitchChain.PairEqualityProjection
import OAI.Probability.SwitchChain.DisjointProjectionCell
import OAI.Probability.SwitchChain.DisjointCellGlobal

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem restrictCell_mem (i j k l : Fin n) (C : GraphState n d → Prop)
    (hC : CellInvariant {i,j} C) (f : StateSpace n d)
    (hf : f ∈ equalitySpace i j k l) :
    restrictCell C f ∈ equalitySpace i j k l := by
  intro G
  obtain ⟨c, hc⟩ := hf G
  refine ⟨if C G then c else 0, fun H h => ?_⟩
  have hCH : C G ↔ C H := hC G H h
  by_cases hG : C G
  · simp only [ite_eq_left hG, restrictCell_apply, ite_eq_left (hCH.mp hG)]
    exact hc H h
  · have hH : ¬ C H := fun hh => hG (hCH.mpr hh)
    simp [restrictCell_apply, hG, hH]

theorem projection_restrictCell (i j k l : Fin n)
    (C : GraphState n d → Prop) (hC : CellInvariant {i,j} C)
    (f : StateSpace n d) :
    projection i j k l (restrictCell C f) = restrictCell C (projection i j k l f) :=
  starProjection_restrictCell (equalitySpace i j k l) C
    (fun f hf => restrictCell_mem i j k l C hC f hf) f

theorem projection_restrict_disjointCell_left (e : Fin 4 ↪ Fin n)
    (c : DisjointEncoding.CellIndex e d) (f : StateSpace n d) :
    projection (e 0) (e 1) (e 2) (e 3)
        (restrictCell (fun G => DisjointEncoding.cellIndex e G = c) f) =
      restrictCell (fun G => DisjointEncoding.cellIndex e G = c)
        (projection (e 0) (e 1) (e 2) (e 3) f) :=
  projection_restrictCell _ _ _ _ _ (DisjointEncoding.cellInvariant_left e c) f

theorem projection_restrict_disjointCell_right (e : Fin 4 ↪ Fin n)
    (c : DisjointEncoding.CellIndex e d) (f : StateSpace n d) :
    projection (e 2) (e 3) (e 0) (e 1)
        (restrictCell (fun G => DisjointEncoding.cellIndex e G = c) f) =
      restrictCell (fun G => DisjointEncoding.cellIndex e G = c)
        (projection (e 2) (e 3) (e 0) (e 1) f) :=
  projection_restrictCell _ _ _ _ _ (DisjointEncoding.cellInvariant_right e c) f

end Problem315.PairEquality

end

end OAI
