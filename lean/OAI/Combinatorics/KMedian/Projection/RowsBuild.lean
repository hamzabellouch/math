import Mathlib
import OAI.Combinatorics.KMedian.Machines.UnaryPolynomial
import OAI.Combinatorics.KMedian.Projection.Tables

namespace OAI

section Inline_PCPProjectionRowsBuild
namespace MetricKMedian.PCP.Compiler.ProjectionTable
open scoped Classical

variable {Z U V D S A B : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
omit [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B] in
lemma rows_build (G : BiProjection U V D S A B) {m k : ℕ} (ue : U≃Fin (m*k)) (ve : V≃Fin m)
    (so : Ordered S) (xs : List Z) (hx : xs.length=m) (row : ℕ→S→ProjectionRow A B)
    (hr : ∀v s,row (ve v).val s=((ue (G.edge.symm (v,s)).1).val,G.project (G.edge.symm (v,s)))) :
    (xs.flatMap (fun _=>List.replicate k ()),(List.range xs.length).map (fun v=>so.entries.map (row v)))=
      build G ue ((Ordered.fin m).map ve.symm) so := by
  apply Prod.ext
  · apply unitList_eq_length
    simp only [build,List.length_replicate]
    rw [length_flatMap_uniform _ _ k (by intros; simp only [List.length_replicate]),hx]
  · change (List.range xs.length).map _ = _
    rw [hx]
    simp only [build,Ordered.map,Ordered.fin,List.map_map,Function.comp_def]
    have he (i : Fin m) : (ve (ve.symm i)).val=i.val := congrArg Fin.val (ve.apply_symm_apply i)
    simp_rw [← hr,he]
    rw [RoundingList.range_finRange,List.map_map]
    rfl
end MetricKMedian.PCP.Compiler.ProjectionTable

end Inline_PCPProjectionRowsBuild

end OAI
