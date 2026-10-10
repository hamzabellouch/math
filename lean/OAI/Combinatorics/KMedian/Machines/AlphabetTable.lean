import Mathlib
import OAI.Combinatorics.KMedian.Machines.AlphabetIndex
import OAI.Combinatorics.KMedian.Machines.ListCompiler
import OAI.Combinatorics.KMedian.Machines.RectTables

namespace OAI

section Inline_PCPAlphabetTable
namespace MetricKMedian.PCP.Compiler.AlphabetProgram
open AlphabetReduction Binary Binary.Automatic
open scoped Classical

variable (K : Type) [Fintype K] [DecidableEq K]
noncomputable def seeds (s : CSPTable (BitVector K)) : List Unit :=
  ((s.1.flatMap fun _ => List.replicate (B K) ()) ++
    (s.2.flatMap fun _ => List.replicate (I K) ())) ++
    (s.2.flatMap fun _ => List.replicate (S K) ())
noncomputable def roots (s : CSPTable (BitVector K)) : List Unit := s.2.map (fun _ => ())
lemma seeds_length (s : CSPTable (BitVector K)) :
    (seeds K s).length=s.1.length*B K+s.2.length*I K+s.2.length*S K := by
  unfold seeds
  simp only [List.length_append]
  rw [length_flatMap_uniform s.1 _ (B K) (by intros; simp),
    length_flatMap_uniform s.2 _ (I K) (by intros; simp),
    length_flatMap_uniform s.2 _ (S K) (by intros; simp)]
@[fun_prop] lemma poly_seeds : Poly (seeds K) := by
  unfold seeds
  fun_prop
@[fun_prop] lemma poly_roots : Poly (roots K) := by
  unfold roots
  fun_prop
noncomputable def table (s : CSPTable (BitVector K)) : CSPTable Label :=
  CSPTable.rect (seeds K s) (roots K s) (Ordered.fixed (Tag K)).entries (row K s)
@[fun_prop] lemma poly_table : Poly (table K) := by
  unfold table
  exact CSPTable.poly_rect (seeds K) (roots K) _ (row K) (poly_seeds K) (poly_roots K) (poly_row K)
noncomputable def vertexEquiv (s : CSPTable (BitVector K)) :
    PaddedNode (Fin s.1.length) (Fin s.2.length) K ≃ Fin (seeds K s).length :=
  (nodeEquiv K _ _).trans (finCongr (seeds_length K s).symm)
noncomputable def edgeRootEquiv (s : CSPTable (BitVector K)) : Fin s.2.length ≃ Fin (roots K s).length :=
  finCongr (List.length_map _).symm
omit [Fintype K] [DecidableEq K] in
lemma row_get (s : CSPTable (BitVector K)) (e : Fin s.2.length) : CSPTable.row s e.val=s.2[e.val] := by
  simp only [CSPTable.row,List.getElem?_eq_getElem e.isLt,Option.getD_some]
end MetricKMedian.PCP.Compiler.AlphabetProgram

end Inline_PCPAlphabetTable

end OAI
