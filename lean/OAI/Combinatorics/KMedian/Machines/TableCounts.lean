import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PowerTable
import OAI.Combinatorics.KMedian.Machines.AlphabetTable

namespace OAI

section Inline_PCPTableCounts
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace CSPTable
variable {A B : Type}
lemma grid_counts (v : List Unit) (b : List B) (r : ℕ → B → CSPRow A) :
    (grid v b r).1.length=v.length ∧ (grid v b r).2.length=v.length*b.length := by
  constructor
  · rfl
  · unfold grid
    rw [length_flatMap_uniform _ _ b.length (by intros; simp only [List.length_map]),List.length_range]
lemma rect_counts (v e : List Unit) (b : List B) (r : ℕ → B → CSPRow A) :
    (rect v e b r).1.length=v.length ∧ (rect v e b r).2.length=e.length*b.length := by
  constructor
  · rfl
  · unfold rect
    rw [length_flatMap_uniform _ _ b.length (by intros; simp only [List.length_map]),List.length_range]
end CSPTable
namespace PowerProgram
variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
omit [DecidableEq A] in
lemma counts (t cap : ℕ) (s : CSPTable A) :
    (table t cap s).1.length=(seeds s).length ∧
    (table t cap s).2.length=(seeds s).length*(Ordered.fixed (Tag (D := RegularProgram.Port) t cap)).entries.length :=
  CSPTable.grid_counts _ _ _
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma seeds_upper (s : CSPTable A) (h : s.WellFormed) [Nonempty (Fin s.2.length)] :
    (seeds s).length ≤ (2*ExpanderFamily.growth^2)*s.2.length := by
  have hv := GlobalRegularization.node_upper (CloudSpec.C s h)
  have he := Fintype.card_congr (vertexEquiv s h)
  simp only [Fintype.card_fin] at he hv
  rw [he] at hv
  exact hv
end PowerProgram
namespace AlphabetProgram
variable (K : Type) [Fintype K] [DecidableEq K]
lemma counts (s : CSPTable (BitVector K)) :
    (table K s).1.length=s.1.length*B K+s.2.length*I K+s.2.length*S K ∧
    (table K s).2.length=s.2.length*(Ordered.fixed (Tag K)).entries.length := by
  have h := CSPTable.rect_counts (seeds K s) (roots K s) (Ordered.fixed (Tag K)).entries (row K s)
  simpa only [table,seeds_length,roots,List.length_map] using h
end AlphabetProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPTableCounts

end OAI
