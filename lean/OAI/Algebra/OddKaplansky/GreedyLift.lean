import OAI.Algebra.OddKaplansky.GreedyColumns

namespace OAI

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.GreedyLift
noncomputable section
open scoped Classical BigOperators Matrix
open Submodule
variable {K : Type portUniverse1} {S : Type portUniverse2} [Field K] [Fintype S] [LinearOrder S]
variable (E : Matrix S S K) (hE : E*E=E)
abbrev I := GreedyColumns.Index (K := K) E.col
abbrev J := GreedyColumns.Index (K := K) (1-E).col
def columns : I E ⊕ J E → (S → K) := Sum.elim (fun i => E.col i.val) (fun j => (1-E).col j.val)
include hE in
lemma complement : IsCompl (span K (Set.range E.col)) (span K (Set.range (1-E).col)) := by
  let L := Matrix.toLinAlgEquiv' (R := K) (n := S)
  have hi : IsIdempotentElem (L E) := by change L E*L E=L E; rw [← map_mul,hE]
  have hc := LinearMap.IsIdempotentElem.isCompl hi
  rw [LinearMap.IsIdempotentElem.ker_eq_range_one_sub hi] at hc
  have hm : L (1-E)=1-L E := by rw [map_sub,map_one]
  rw [← hm] at hc
  change IsCompl (LinearMap.range (Matrix.toLin' E)) (LinearMap.range (Matrix.toLin' (1-E))) at hc
  simpa only [Matrix.range_toLin'] using hc
include hE in
lemma independent : LinearIndependent K (columns E) := by
  apply (GreedyColumns.independent E.col).sum_type (GreedyColumns.independent (1-E).col)
  rw [GreedyColumns.span_selected,GreedyColumns.span_selected]
  exact (complement E hE).disjoint
include hE in
lemma spanning : span K (Set.range (columns E))=⊤ := by
  rw [columns,Set.Sum.elim_range,span_union,GreedyColumns.span_selected,GreedyColumns.span_selected]
  exact (complement E hE).sup_eq_top

def basis : Module.Basis (I E ⊕ J E) K (S → K) :=
  Module.Basis.mk (independent E hE) (spanning E hE).ge
include hE in
lemma card_indices : Fintype.card (I E) + Fintype.card (J E)=Fintype.card S := by
  have hh := Module.finrank_eq_card_basis (basis E hE)
  simpa using hh.symm

def indices : S ≃ I E ⊕ J E :=
  (FiniteChoice.orderedIndex S).trans ((finCongr (card_indices E hE).symm).trans
    (finSumFinEquiv.symm.trans ((FiniteChoice.orderedIndex (I E)).symm.sumCongr (FiniteChoice.orderedIndex (J E)).symm)))
def matrix : Matrix S S K := fun s t => columns E (indices E hE t) s
lemma matrix_independent : LinearIndependent K (matrix E hE).col :=
  (independent E hE).comp (indices E hE) (indices E hE).injective
lemma matrix_det : (matrix E hE).det ≠ 0 :=
  Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.linearIndependent_col_iff.mp (matrix_independent E hE))
end
end OddKaplansky.GreedyLift

end

end OAI
