import Mathlib
import OAI.Combinatorics.KMedian.Expanders.ExpanderStep
import OAI.Combinatorics.KMedian.Machines.RotationBounds
import OAI.Combinatorics.KMedian.Machines.RotationExt

namespace OAI

section Inline_PCPExpanderTables
namespace MetricKMedian.PCP.Compiler.Expander
open ExpanderFamily RotationTable
open scoped Classical

lemma next_table (n : ℕ) :
    next (table (graph n) (vertexEquiv n))=table (graph (n+1)) (vertexEquiv (n+1)) := by
  apply ext_lookup
  · simp only [next_length,table_length,pow_succ]
  · exact blockRows_row_length _ _
  · intro row hr
    exact (table_wellFormed _ _ row hr).1
  · intro i hi d
    have hi' : i < (Fintype.card Branch)^(n+1) := by
      simpa only [next_length,table_length,pow_succ] using hi
    let w := (vertexEquiv (n+1)).symm ⟨i,hi'⟩
    have hw : (vertexEquiv (n+1) w).val=i := by
      simp only [w,Equiv.apply_symm_apply]
    obtain ⟨v,b⟩ := w
    have hj : i=nodeIndex (vertexEquiv n v).val b := by
      exact hw.symm.trans (by simpa only [nodeIndex,card_branch] using vertexEquiv_succ n v b)
    calc
      lookup (next (table (graph n) (vertexEquiv n))) i d =
          rotate (table (graph n) (vertexEquiv n)) (vertexEquiv n v).val b d := by
        rw [hj]
        exact lookup_next _ _ (by rw [table_length]; exact (vertexEquiv n v).isLt) _ _
      _ = ((vertexEquiv (n+1) ((graph (n+1)).step (v,b) d)).val,(graph (n+1)).back (v,b) d) :=
        rotate_table n v b d
      _ = lookup (table (graph (n+1)) (vertexEquiv (n+1))) (vertexEquiv (n+1) (v,b)).val d :=
        (lookup_table _ _ _ _).symm
      _ = lookup (table (graph (n+1)) (vertexEquiv (n+1))) i d := by rw [hw]
noncomputable def initial : Raw := table (graph 0) (vertexEquiv 0)
lemma iterate_sequence {A : Type} (f : A → A) (a : ℕ → A)
    (h : ∀ n, f (a n)=a (n+1)) (n : ℕ) : f^[n] (a 0)=a n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,h]
lemma iterate_table (n : ℕ) : next^[n] initial=table (graph n) (vertexEquiv n) :=
  iterate_sequence next (fun n => table (graph n) (vertexEquiv n)) next_table n
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderTables

end OAI
