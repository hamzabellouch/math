import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteProjectionFrames
import OAI.NumberTheory.DukePrimeDegree.Geometry.FrameChangeOfBasis
import Mathlib.LinearAlgebra.Matrix.Rank

namespace OAI

/-!
# A nonzero coordinate minor of an independent frame

Maximal Gram minors of the row family select the required coordinate
minor. Row rank equals column rank, so the selected number of rows is
exactly the size of the independent column frame.
-/

noncomputable section
open Matrix Set

namespace DukePrimeDegree

theorem exists_nonzero_frameMinor_of_linearIndependent {n k : ℕ}
    (B : Matrix (Fin n) (Fin k) ℝ) (hB : LinearIndependent ℝ B.col) :
    ∃ p : Fin k ↪ Fin n, frameMinor B p ≠ 0 := by
  let e := EuclideanSpace.equiv (Fin k) ℝ
  let v : Fin n → EuclideanSpace ℝ (Fin k) := fun i => e.symm (B.row i)
  let S := maximalGramFrame v
  have hmap : (Submodule.span ℝ (Set.range v)).map e.toLinearMap =
      Submodule.span ℝ (Set.range B.row) := by
    have heq : e.toLinearMap ∘ v = B.row := by
      funext i
      exact e.apply_symm_apply (B.row i)
    rw [Submodule.map_span, ← Set.range_comp, heq]
  have hcard : S.card = k := by
    calc
      S.card = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := maximalGramFrame_card v
      _ = Module.finrank ℝ ((Submodule.span ℝ (Set.range v)).map e.toLinearMap) :=
        (e.toLinearEquiv.finrank_map_eq _).symm
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range B.row)) := by rw [hmap]
      _ = B.rank := B.rank_eq_finrank_span_row.symm
      _ = k := by
        rw [B.rank_eq_finrank_span_cols, finrank_span_eq_card hB, Fintype.card_fin]
  let q : Fin k ≃ S := (S.equivFinOfCardEq hcard).symm
  let p : Fin k ↪ Fin n := q.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have hli : LinearIndependent ℝ (fun s : S => v s) := (maximalGramFrame_spec v).linearIndependent
  have hrows : LinearIndependent ℝ (B.submatrix p id).row := by
    have hmapli := hli.map_injOn e.toLinearMap (fun _ _ _ _ h => e.injective h)
    have hcomp := hmapli.comp q q.injective
    change LinearIndependent ℝ (fun i : Fin k => e (v (q i))) at hcomp
    have heq : (fun i : Fin k => e (v (q i))) = (B.submatrix p id).row := by
      funext i
      change e (e.symm (B.row (q i))) = B.row (q i)
      exact e.apply_symm_apply _
    rw [heq] at hcomp
    exact hcomp
  refine ⟨p, ?_⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

end DukePrimeDegree

end

end OAI
