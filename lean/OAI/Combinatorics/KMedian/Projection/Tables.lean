import Mathlib
import OAI.Combinatorics.KMedian.Hardness.ProjectionEncoding
import OAI.Combinatorics.KMedian.Machines.FiniteCoordinates
import OAI.Combinatorics.KMedian.Machines.Hardcoded
import OAI.Combinatorics.KMedian.Machines.Ordered
import OAI.Combinatorics.KMedian.Projection.Input
import OAI.Combinatorics.KMedian.Projection.Reindex

namespace OAI

section Inline_PCPProjectionTables
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace Ordered
variable {V : Type} [DecidableEq V]
lemma entries_ofFn (o : Ordered V) : List.ofFn (fun i => o.equiv.symm i)=o.entries := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    have hh := o.get_equiv (o.equiv.symm ⟨i,hj⟩)
    simpa only [Equiv.apply_symm_apply] using hh.symm
lemma map_entries {C : Type} (o : Ordered V) (f : V→C) : o.entries.map f=List.ofFn (fun i => f (o.equiv.symm i)) := by
  calc
    _ = (List.ofFn (fun i=>o.equiv.symm i)).map f := congrArg (List.map f) (entries_ofFn o).symm
    _ = _ := List.map_ofFn
end Ordered
abbrev ProjectionRow (A B : Type) := ℕ × (A→B)
abbrev ProjectionTable (A B : Type) := List Unit × List (List (ProjectionRow A B))
namespace ProjectionTable
variable {U V D S A B : Type} [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [DecidableEq V] [DecidableEq S] [DecidableEq A] [DecidableEq B]
variable (G : BiProjection U V D S A B) {nu : ℕ} (ue : U≃Fin nu) (vo : Ordered V) (so : Ordered S)
noncomputable def build : ProjectionTable A B :=
  (List.replicate nu (),vo.entries.map (fun v => so.entries.map (fun s =>
    ((ue (G.edge.symm (v,s)).1).val,G.project (G.edge.symm (v,s))))))
variable (ao : Ordered A) (bo : Ordered B)
noncomputable def raw (t : ProjectionTable A B) : Coverage.ProjectionRaw :=
  (t.1.map (fun _=>false),t.2.map (fun row => row.map (fun e =>
    (e.1,ao.entries.map (fun a => (bo.equiv (e.2 a)).val)))))
omit [DecidableEq A] in
lemma poly_raw [Nonempty B] : Poly (raw ao bo) := by
  let : Inhabited B := Classical.inhabited_of_nonempty inferInstance
  have hh : Poly (fun f : A→B => ao.entries.map (fun a => (bo.equiv (f a)).val)) := hardcoded _
  unfold raw
  apply Poly.pair
  · exact Poly.list_map (Automatic.Poly.const _) Poly.fst
  · apply Poly.list_map _ Poly.snd
    apply Poly.list_map _ Poly.snd
    exact Poly.pair (Poly.fst.comp Poly.snd) (hh.comp (Poly.snd.comp Poly.snd))
noncomputable def indexed := G.reindex ue vo.equiv (Fintype.equivFin D) so.equiv ao.equiv bo.equiv
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
include ue in
lemma nu_pos : 0<nu := by
  have hh := Fintype.card_congr ue
  have hp := Fintype.card_pos (α:=U)
  simp only [Fintype.card_fin] at hh
  omega
lemma order_pos {I : Type} [DecidableEq I] [Nonempty I] (o : Ordered I) : 0<o.entries.length := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact List.length_pos_of_mem (o.all i)
noncomputable def input (hc : G.Consistent) : Coverage.ProjectionInput so.entries.length ao.entries.length bo.entries.length :=
  (indexed G ue vo so ao bo).input (nu_pos ue) (order_pos vo) (order_pos so) (order_pos ao) (order_pos bo)
    (G.reindex_consistent _ _ _ _ _ _ hc)
omit [Fintype V] [Fintype S] [Fintype A] [Fintype B] [Nonempty D] in
lemma input_raw (hc : G.Consistent) : (input G ue vo so ao bo hc).raw=raw ao bo (build G ue vo so) := by
  simp only [Coverage.ProjectionInput.raw,input,BiProjection.input,BiProjection.system,indexed,
    BiProjection.reindex,build,raw,List.map_replicate]
  simp only [Ordered.map_entries, List.map_ofFn, Function.comp_def, Prod.map, Prod.eta,
    Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]
omit [Fintype V] [Fintype S] [Fintype A] [Fintype B] [Nonempty D] in
lemma input_perfect (hc : G.Consistent) (hy : G.Perfect) : (input G ue vo so ao bo hc).Perfect := by
  apply BiProjection.input_perfect
  exact G.reindex_perfect _ _ _ _ _ _ hy
omit [Fintype V] [Fintype S] [Fintype A] [Fintype B] [Nonempty D] in
lemma input_sound (hc : G.Consistent) (ε : ℝ) (hn : G.Sound ε) : (input G ue vo so ao bo hc).Sound ε := by
  let : Nonempty (Fin nu) := Fin.pos_iff_nonempty.mp (nu_pos ue)
  let : Nonempty (Fin vo.entries.length) := Fin.pos_iff_nonempty.mp (order_pos vo)
  let : Nonempty (Fin so.entries.length) := Fin.pos_iff_nonempty.mp (order_pos so)
  let : Nonempty (Fin ao.entries.length) := Fin.pos_iff_nonempty.mp (order_pos ao)
  let : Nonempty (Fin bo.entries.length) := Fin.pos_iff_nonempty.mp (order_pos bo)
  apply BiProjection.input_sound
  exact G.reindex_sound _ _ _ _ _ _ hn
end ProjectionTable
end MetricKMedian.PCP.Compiler

end Inline_PCPProjectionTables

end OAI
