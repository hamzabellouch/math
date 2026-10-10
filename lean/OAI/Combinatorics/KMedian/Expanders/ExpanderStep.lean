import Mathlib
import OAI.Combinatorics.KMedian.Expanders.ExpanderIndex
import OAI.Combinatorics.KMedian.Machines.BlockRotation

namespace OAI

section Inline_PCPExpanderStep

namespace MetricKMedian.PCP.Compiler.Expander
open Binary Binary.Automatic ExpanderFamily RotationTable
open scoped Classical

abbrev Raw := RotationTable Degree
noncomputable def nodeIndex (v : ℕ) (b : Branch) : ℕ := v*growth+(Fintype.equivFin Branch b).val
noncomputable def rotate (R : Raw) (v : ℕ) (b : Branch) (d : Degree) : ℕ × Degree :=
  let h1 := base.rotate (b,d.1)
  let q1 := lookup R v h1.1.1
  let q2 := lookup R q1.1 h1.1.2
  let h2 := base.rotate ((q2.2,q1.2),d.2)
  (nodeIndex q2.1 h2.1,(h2.2,h1.2))
noncomputable def next (R : Raw) : Raw :=
  (List.range R.length).flatMap (fun v => (ports (D := Branch)).map (fun b =>
    (ports (D := Degree)).map (rotate R v b)))
@[fun_prop] lemma poly_baseRotate : Poly (fun p : Branch × SmallPort => base.rotate p) := hardcoded _
@[fun_prop] lemma poly_nodeIndex : Poly (fun p : ℕ × Branch => nodeIndex p.1 p.2) := by
  unfold nodeIndex
  have h : Poly (fun b : Branch => (Fintype.equivFin Branch b).val) := hardcoded _
  exact Automatic.Poly.nat_add.comp (Automatic.Poly.pair
    (Automatic.Poly.nat_mul.comp (Automatic.Poly.pair Automatic.Poly.fst (Automatic.Poly.const growth)))
    (h.comp Automatic.Poly.snd))
@[fun_prop] lemma poly_rotate : Poly (fun p : Raw × (ℕ × (Branch × Degree)) => rotate p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold rotate
  have hl := poly_lookup (D := Degree)
  fun_prop
lemma poly_rotate4 : Poly (fun p : ((Raw × ℕ) × Branch) × Degree =>
    rotate p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  unfold rotate
  have hl := poly_lookup (D := Degree)
  fun_prop
lemma poly_next : Poly next := by
  unfold next
  apply Poly.list_flatMap
  · apply Poly.list_map
    · apply Poly.list_map
      · exact poly_rotate4
      · exact Automatic.Poly.const _
    · exact Automatic.Poly.const _
  · exact Poly.list_indices
lemma next_length (R : Raw) : (next R).length=R.length*Fintype.card Branch := by
  unfold next
  rw [length_flatMap_uniform _ _ (Fintype.card Branch) (by intro v hv; simp only [List.length_map,ports_length]),List.length_range]
lemma lookup_next (R : Raw) (v : ℕ) (hv : v<R.length) (b : Branch) (d : Degree) :
    lookup (next R) (nodeIndex v b) d=rotate R v b d := by
  change lookup (blockRows R.length (rotate R)) (nodeIndex v b) d=rotate R v b d
  have h := lookup_blockRows R.length (rotate R) v hv b d
  simpa only [nodeIndex,card_branch] using h
lemma rotate_table_aux {V : Type} {N : ℕ} (G : PortGraph V Degree) (e : V ≃ Fin N)
    (v : V) (b : Branch) (d : Degree) :
    rotate (table G e) (e v).val b d =
    let h1 := base.rotate (b,d.1)
    let u := G.step v h1.1.1
    let w := G.step u h1.1.2
    let h2 := base.rotate ((G.back u h1.1.2,G.back v h1.1.1),d.2)
    (nodeIndex (e w).val h2.1,(h2.2,h1.2)) := by
  simp only [rotate,lookup_table]
lemma graph_rotate_succ (n : ℕ) (v : Vertex n) (b : Branch) (d : Degree) :
    (graph (n+1)).rotate ((v,b),d)=
    let h1 := base.rotate (b,d.1)
    let u := (graph n).step v h1.1.1
    let w := (graph n).step u h1.1.2
    let h2 := base.rotate (((graph n).back u h1.1.2,(graph n).back v h1.1.1),d.2)
    ((w,h2.1),(h2.2,h1.2)) := rfl
lemma rotate_table (n : ℕ) (v : Vertex n) (b : Branch) (d : Degree) :
    rotate (table (graph n) (vertexEquiv n)) (vertexEquiv n v).val b d=
      ((vertexEquiv (n+1) ((graph (n+1)).step (v,b) d)).val,(graph (n+1)).back (v,b) d) := by
  have h := rotate_table_aux (graph n) (vertexEquiv n) v b d
  convert h using 1
  change ((vertexEquiv (n+1) ((graph (n+1)).rotate ((v,b),d)).1).val,
    ((graph (n+1)).rotate ((v,b),d)).2)=_
  simp only [graph_rotate_succ,vertexEquiv_succ,card_branch,nodeIndex]
end MetricKMedian.PCP.Compiler.Expander

end Inline_PCPExpanderStep

end OAI
