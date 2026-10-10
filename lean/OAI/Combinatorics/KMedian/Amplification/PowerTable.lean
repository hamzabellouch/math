import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PowerSpec
import OAI.Combinatorics.KMedian.Amplification.RegularSpec
import OAI.Combinatorics.KMedian.Machines.AdviceInstances
import OAI.Combinatorics.KMedian.Machines.GridTables

namespace OAI

section Inline_PCPPowerTable
namespace MetricKMedian.PCP.Compiler.PowerProgram
open Binary Binary.Automatic RegularProgram CloudSpec
open scoped Classical

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
noncomputable def seeds (s : CSPTable A) : List Unit := (CloudProgram.global s).map (fun _ => ())
noncomputable def table (t cap : ℕ) (s : CSPTable A) : CSPTable (Advice Port A cap) :=
  CSPTable.grid (seeds s) (Ordered.fixed (Tag (D := Port) t cap)).entries
    (row RegularProgram.rotate RegularProgram.allowed t cap s)
omit [DecidableEq A] in
lemma poly_table (t cap : ℕ) : Poly (table (A := A) t cap) := by
  apply CSPTable.poly_grid
  · unfold seeds
    apply Poly.list_map (Automatic.Poly.const ()) CloudProgram.poly_global
  · exact poly_row RegularProgram.rotate RegularProgram.allowed RegularProgram.poly_rotate RegularProgram.poly_allowed t cap
variable (s : CSPTable A) (h : s.WellFormed) [Nonempty (Fin s.2.length)]
noncomputable def vertexEquiv : GlobalRegularization.Node (C s h) ≃ Fin (seeds s).length :=
  (ExpanderFamily.vertexEquiv _).trans (finCongr (by
    rw [seeds,List.length_map,global_table s h,RotationTable.table_length]))
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma vertexEquiv_val (v : GlobalRegularization.Node (C s h)) :
    (vertexEquiv s h v).val=vertexCode s h v := rfl
noncomputable def represents (t cap : ℕ) :
    (table t cap s).Represents ((regularCSP s h).powered (cap := cap) t) := by
  have he := CSPTable.grid_build ((regularCSP s h).powered (cap := cap) t)
    (seeds s) (vertexEquiv s h) (Ordered.fixed (Tag (D := Port) t cap))
    (edgeEquiv (G := regularGraph s h) t cap)
    (row RegularProgram.rotate RegularProgram.allowed t cap s) (by
      intro v b
      have hh := row_correct (regularCSP s h) RegularProgram.rotate RegularProgram.allowed
        (vertexCode s h) s (rotate_correct s h) (allowed_correct s h) t cap
        ((edgeEquiv (G := regularGraph s h) t cap) (v,b))
      simpa only [edgeEquiv,Equiv.coe_fn_mk,PortGraph.Walk.ofWord,PortGraph.trace_zero,
        vertexEquiv_val] using hh)
  unfold table
  rw [he]
  exact CSPTable.build_represents _ _ _
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPowerTable

end OAI
