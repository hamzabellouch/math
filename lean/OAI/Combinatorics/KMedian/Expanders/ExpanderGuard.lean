import Mathlib
import OAI.Combinatorics.KMedian.Expanders.ExpanderTables

namespace OAI

section Inline_PCPExpanderGuard
namespace MetricKMedian.PCP.Compiler.Expander
open ExpanderFamily RotationTable Binary Binary.Automatic
open scoped Classical

abbrev State := ℕ × Raw
noncomputable def guarded (s : State) : State :=
  (s.1, if s.2.length ≤ s.1 + 1 then next s.2 else s.2)
lemma poly_guarded : Poly guarded := by
  unfold guarded
  apply Poly.pair Poly.fst
  apply Poly.ite_prop
  · fun_prop
  · exact poly_next.comp Poly.snd
  · exact Poly.snd
lemma level_le (n : ℕ) : level n ≤ n+1 := by
  have h := Nat.log_lt_self growth (Nat.succ_ne_zero n)
  unfold level
  have h' : Nat.log growth (n+1) < n+1 := by simpa only [Nat.succ_eq_add_one] using h
  omega
noncomputable def family (n : ℕ) : Raw := table (graph n) (vertexEquiv n)
lemma family_zero : family 0=initial := Eq.refl _
lemma next_family (n : ℕ) : next (family n)=family (n+1) := next_table n
lemma family_length (n : ℕ) : (family n).length=growth^n := by
  exact (table_length (graph n) (vertexEquiv n)).trans (congrArg (fun k:ℕ => k^n) card_branch)
lemma family_wellFormed (n : ℕ) : WellFormed (family n) := by
  rw [family]
  exact table_wellFormed _ _
lemma guard_at (n i : ℕ) : (family i).length ≤ n+1 ↔ i<level n := by
  rw [family_length,level]
  exact (Nat.le_log_iff_pow_le growth_gt_one (Nat.succ_ne_zero n)).symm.trans Nat.lt_add_one_iff.symm
noncomputable def sequence (n i : ℕ) : State :=
  (n,family (min i (level n)))
lemma sequence_zero (n : ℕ) : sequence n 0=(n,initial) := by
  simp only [sequence,Nat.zero_min,family_zero]
lemma sequence_succ (n i : ℕ) : guarded (sequence n i)=sequence n (i+1) := by
  by_cases hi : i<level n
  · have h0 : min i (level n)=i := min_eq_left hi.le
    have h1 : min (i+1) (level n)=i+1 := min_eq_left hi
    have ht := (guard_at n i).mpr hi
    simp only [sequence,h0,h1,guarded,ite_eq_left ht,next_family]
  · have h0 : min i (level n)=level n := min_eq_right (by omega)
    have h1 : min (i+1) (level n)=level n := min_eq_right (by omega)
    have ht : ¬(family (level n)).length ≤ n+1 := by
      rw [guard_at]; exact lt_irrefl _
    simp only [sequence,h0,h1,guarded,ite_eq_right ht]
lemma iterate_guarded (n i : ℕ) : guarded^[i] (n,initial)=sequence n i := by
  have h := iterate_sequence guarded (sequence n) (sequence_succ n) i
  rwa [sequence_zero] at h
lemma sequence_wellFormed (n i : ℕ) : WellFormed (sequence n i).2 := by
  dsimp only [sequence]
  exact family_wellFormed (min i (level n))
lemma sequence_length (n i : ℕ) : (sequence n i).2.length ≤ growth*(n+1) := by
  dsimp only [sequence]
  rw [family_length]
  apply (Nat.pow_le_pow_right (by have := growth_gt_one; omega) (min_le_right i (level n))).trans
  simpa only [card_vertex] using padding_upper n
noncomputable def generate (xs : List Unit) : Raw := (guarded^[xs.length+1] (xs.length,initial)).2
lemma generate_table (xs : List Unit) : generate xs=table (graph (level xs.length)) (vertexEquiv (level xs.length)) := by
  unfold generate
  rw [iterate_guarded]
  dsimp only [sequence]
  rw [min_eq_right (level_le xs.length)]
  exact Eq.refl _
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderGuard

end OAI
