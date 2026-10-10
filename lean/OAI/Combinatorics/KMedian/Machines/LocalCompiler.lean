import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.FiniteConstraints
import OAI.Combinatorics.KMedian.Machines.OrderedLists
import OAI.Combinatorics.KMedian.Machines.TableBuilders

namespace OAI

section Inline_PCPLocalCompiler
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace Ordered
variable {V T : Type} [DecidableEq V] [DecidableEq T]
lemma sum_left_index (vo : Ordered V) (eo : Ordered T) (v : V) :
    ((vo.sum eo).equiv (.inl v)).val=(vo.equiv v).val := by
  classical
  let : BEq (V ⊕ T) := instBEqOfDecidableEq
  rw [Ordered.equiv_val,Ordered.equiv_val]
  simp only [Ordered.sum]
  rw [List.idxOf_append_of_mem (List.mem_map.mpr ⟨v,vo.all v,rfl⟩)]
  simp only [List.idxOf,List.findIdx_map]
  congr 1
  funext x
  simp only [Function.comp_def,Bool.beq_eq_decide_eq,Sum.inl.injEq]
lemma sum_right_index (vo : Ordered V) (eo : Ordered T) (t : T) :
    ((vo.sum eo).equiv (.inr t)).val=vo.entries.length+(eo.equiv t).val := by
  classical
  let : BEq (V ⊕ T) := instBEqOfDecidableEq
  rw [Ordered.equiv_val,Ordered.equiv_val]
  simp only [Ordered.sum]
  rw [List.idxOf_append_of_notMem (by simp),List.length_map]
  congr 1
  simp only [List.idxOf,List.findIdx_map]
  congr 1
  funext x
  simp only [Function.comp_def,Bool.beq_eq_decide_eq,Sum.inr.injEq]
end Ordered
namespace LocalCompiler
variable {X VC TC Q A : Type} [Coding X] [Coding VC] [Coding TC]
  [Fintype Q] [Fintype A] [DecidableEq A] [DecidableEq VC] [DecidableEq TC]
  [Inhabited X] [Inhabited VC] [Inhabited TC] [Inhabited Q] [Inhabited A]
  [Coding Q] [Hardcoded Q]
noncomputable instance assignmentSetCoding : Coding (Finset (Q→A)) := finiteCoding _
noncomputable instance assignmentSetHardcoded : Hardcoded (Finset (Q→A)) := ⟨fun _ _ _ f => finite_function f⟩
abbrev Label := FiniteCSP.Label (Q := Q) (A := A)
noncomputable def relation (r : Finset (Q → A)) (q : Q) : Finset (Label (Q := Q) (A := A) × Label (Q := Q) (A := A)) :=
  Finset.univ.filter (fun p => ∃ a b, p=(Sum.inl a,Sum.inr b) ∧ b∈r ∧ a=b q)
omit [Inhabited Q] [Inhabited A] in
lemma poly_relation : Poly (fun p : Finset (Q→A) × Q => relation p.1 p.2) := hardcoded _
variable (vars : X→List VC) (tests : X→List TC) (query : X→TC→Q→VC) (accept : X→TC→Finset (Q→A))
noncomputable def row (x:X) (t:TC) (q:Q) : CSPRow (Label (Q := Q) (A := A)) :=
  ((vars x).findIdx (fun v => decide (v=query x t q)),
    (vars x).length+(tests x).findIdx (fun u => decide (u=t)),relation (accept x t) q)
noncomputable def table (x:X) : CSPTable (Label (Q := Q) (A := A)) :=
  ((vars x).map (fun _=>())++(tests x).map (fun _=>()),
    (tests x).flatMap (fun t => (Ordered.fixed Q).entries.map (fun q => row vars tests query accept x t q)))
omit [Inhabited X] [Inhabited A] in
lemma poly_table (hv : Poly vars) (ht : Poly tests)
    (hq : Poly (fun p : (X×TC)×Q => query p.1.1 p.1.2 p.2))
    (ha : Poly (fun p : X×TC => accept p.1 p.2))
    (hev : Poly (fun p : VC×VC => decide (p.1=p.2)))
    (het : Poly (fun p : TC×TC => decide (p.1=p.2))) : Poly (table vars tests query accept) := by
  have hr : Poly (fun p : (X×TC)×Q => row vars tests query accept p.1.1 p.1.2 p.2) := by
    have hvv := hv.comp (Poly.fst.comp Poly.fst : Poly (fun p : (X×TC)×Q => p.1.1))
    have htt := ht.comp (Poly.fst.comp Poly.fst : Poly (fun p : (X×TC)×Q => p.1.1))
    have hl : Poly (fun p : (X×TC)×Q => (vars p.1.1).findIdx (fun v => decide (v=query p.1.1 p.1.2 p.2))) :=
      Poly.list_findIdx (hev.comp (Poly.pair Poly.snd (hq.comp Poly.fst))) hvv
    have hi : Poly (fun p : (X×TC)×Q => (tests p.1.1).findIdx (fun u => decide (u=p.1.2))) :=
      Poly.list_findIdx (het.comp (Poly.pair Poly.snd (Poly.snd.comp (Poly.fst.comp Poly.fst)))) htt
    unfold row
    exact Poly.pair hl (Poly.pair (by fun_prop) (poly_relation.comp (Poly.pair (ha.comp Poly.fst) Poly.snd)))
  unfold table
  apply Poly.pair
  · have hvm : Poly (fun x => (vars x).map (fun _=>())) := Poly.list_map (show Poly (fun _ : X×VC => ()) from Automatic.Poly.const ()) hv
    have htm : Poly (fun x => (tests x).map (fun _=>())) := Poly.list_map (show Poly (fun _ : X×TC => ()) from Automatic.Poly.const ()) ht
    exact Poly.list_append.comp (Poly.pair hvm htm)
  · exact Poly.list_flatMap (Poly.list_map hr (Automatic.Poly.const _)) ht
variable {V T : Type} [Fintype V] [Fintype T] [DecidableEq V] [DecidableEq T]
variable (C : FiniteCSP V T Q A) (vo : Ordered V) (eo : Ordered T)
  (vc : V→VC) (tc : T→TC) (hvc : Function.Injective vc) (htc : Function.Injective tc)
include hvc htc in
omit [Coding X] [Coding VC] [Coding TC] [Inhabited X] [Inhabited VC] [Inhabited TC]
  [Inhabited Q] [Inhabited A] [Coding Q] [Hardcoded Q] [Fintype V] [Fintype T] in
lemma table_build (x:X) (hv : vars x=vo.entries.map vc) (ht : tests x=eo.entries.map tc)
    (hq : ∀t q, query x (tc t) q=vc (C.query t q))
    (ha : ∀t, accept x (tc t)=C.accept t) :
    table vars tests query accept x=CSPTable.build C.binary (vo.sum eo) (eo.prod (Ordered.fixed Q)) := by
  unfold table CSPTable.build
  apply Prod.ext
  · simp only [hv,ht,Ordered.sum,List.map_append,List.map_map,Function.comp_def]
  · rw [ht]
    simp only [Ordered.prod,List.product,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]
    apply congrArg (fun f : T→List (CSPRow (Label (Q := Q) (A := A))) => eo.entries.flatMap f)
    funext t
    apply List.map_congr_left
    intro q hqmem
    unfold row
    rw [hv,ht,hq t q,ha t,← Ordered.index_coded vo vc hvc,← Ordered.index_coded eo tc htc]
    simp only [FiniteCSP.binary,Ordered.sum_left_index,Ordered.sum_right_index,List.length_map,relation]
include hvc htc in
noncomputable def represents (x:X) (hv : vars x=vo.entries.map vc) (ht : tests x=eo.entries.map tc)
    (hq : ∀t q, query x (tc t) q=vc (C.query t q))
    (ha : ∀t, accept x (tc t)=C.accept t) : (table vars tests query accept x).Represents C.binary := by
  rw [table_build vars tests query accept C vo eo vc tc hvc htc x hv ht hq ha]
  exact CSPTable.build_represents _ _ _
end LocalCompiler
end MetricKMedian.PCP.Compiler

end Inline_PCPLocalCompiler

end OAI
