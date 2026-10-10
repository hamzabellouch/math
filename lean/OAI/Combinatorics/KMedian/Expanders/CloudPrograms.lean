import Mathlib
import OAI.Combinatorics.KMedian.Expanders.ExpanderCompiler
import OAI.Combinatorics.KMedian.Machines.RawCSP

namespace OAI

section Inline_PCPCloudPrograms
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

noncomputable instance unitHardcoded : Hardcoded Unit where
  all B _ _ f := poly_congr (Automatic.Poly.const (f ())) (fun u => by cases u; rfl)
noncomputable instance boolHardcoded : Hardcoded Bool where
  all B _ _ f := poly_congr (Poly.ite Poly.identity (Automatic.Poly.const (f true)) (Automatic.Poly.const (f false)))
    (fun u => by cases u <;> rfl)
namespace CloudProgram
variable {A : Type} [Fintype A]
abbrev Dart := ℕ × Bool
noncomputable def darts (t : CSPTable A) : List Dart :=
  (List.range t.2.length).flatMap (fun e => [(e,false),(e,true)])
noncomputable def endpoint (t : CSPTable A) (d : Dart) : ℕ :=
  if d.2 then (CSPTable.row t d.1).2.1 else (CSPTable.row t d.1).1
noncomputable def incident (t : CSPTable A) (v : ℕ) : List Dart :=
  (darts t).filter (fun d => decide (endpoint t d=v))
noncomputable def active (t : CSPTable A) : List ℕ :=
  (List.range t.1.length).filter (fun v => !(incident t v).isEmpty)
noncomputable def cloud (t : CSPTable A) (v : ℕ) : Expander.Raw :=
  Expander.generate ((incident t v).tail.map (fun _ => ()))
noncomputable def nodes (t : CSPTable A) : List (ℕ × ℕ) :=
  (active t).flatMap (fun v => (List.range (cloud t v).length).map (fun j => (v,j)))
noncomputable def global (t : CSPTable A) : Expander.Raw :=
  Expander.generate ((nodes t).tail.map (fun _ => ()))
noncomputable def index (t : CSPTable A) (p : ℕ × ℕ) : ℕ :=
  (nodes t).findIdx (fun q => decide (q.1=p.1 ∧ q.2=p.2))
noncomputable def dartIndex (t : CSPTable A) (v : ℕ) (d : Dart) : ℕ :=
  (incident t v).findIdx (fun q => decide (q.1=d.1 ∧ q.2=d.2))
@[fun_prop] lemma poly_darts : Poly (darts (A := A)) := by
  unfold darts
  apply Poly.list_flatMap
  · fun_prop
  · exact Poly.list_indices.comp Poly.snd
@[fun_prop] lemma poly_endpoint : Poly (fun p : CSPTable A × Dart => endpoint p.1 p.2) := by
  unfold endpoint
  have hr := CSPTable.poly_row (A := A)
  fun_prop
@[fun_prop] lemma poly_incident : Poly (fun p : CSPTable A × ℕ => incident p.1 p.2) := by
  unfold incident
  apply Poly.list_filter
  · fun_prop
  · exact poly_darts.comp Poly.fst
@[fun_prop] lemma poly_active : Poly (active (A := A)) := by
  unfold active
  apply Poly.list_filter
  · fun_prop
  · exact Poly.list_indices.comp Poly.fst
@[fun_prop] lemma poly_cloud : Poly (fun p : CSPTable A × ℕ => cloud p.1 p.2) := by
  unfold cloud
  apply Expander.poly_generate.comp
  apply Poly.list_map
  · exact Automatic.Poly.const _
  · exact Poly.list_tail.comp poly_incident
@[fun_prop] lemma poly_nodes : Poly (nodes (A := A)) := by
  unfold nodes
  apply Poly.list_flatMap
  · apply Poly.list_map
    · fun_prop
    · exact Poly.list_indices.comp poly_cloud
  · exact poly_active
@[fun_prop] lemma poly_global : Poly (global (A := A)) := by
  unfold global
  apply Expander.poly_generate.comp
  apply Poly.list_map
  · exact Automatic.Poly.const _
  · exact Poly.list_tail.comp poly_nodes
@[fun_prop] lemma poly_index : Poly (fun p : CSPTable A × (ℕ × ℕ) => index p.1 p.2) := by
  unfold index
  apply Poly.list_findIdx
  · have he : Poly (fun p : ((CSPTable A × (ℕ × ℕ)) × (ℕ × ℕ)) =>
        decide (p.2.1=p.1.2.1) && decide (p.2.2=p.1.2.2)) := by fun_prop
    simpa only [Bool.decide_and] using he
  · exact poly_nodes.comp Poly.fst
@[fun_prop] lemma poly_dartIndex : Poly (fun p : (CSPTable A × ℕ) × Dart => dartIndex p.1.1 p.1.2 p.2) := by
  unfold dartIndex
  apply Poly.list_findIdx
  · have he : Poly (fun p : (((CSPTable A × ℕ) × Dart) × Dart) =>
        decide (p.2.1=p.1.2.1) && decide (p.2.2=p.1.2.2)) := by
      have hb : Poly (fun p : Bool × Bool => decide (p.1=p.2)) := hardcoded _
      have hb' := hb.comp (show Poly (fun p : (((CSPTable A × ℕ) × Dart) × Dart) => (p.2.2,p.1.2.2)) by fun_prop)
      fun_prop
    simpa only [Bool.decide_and] using he
  · exact poly_incident.comp Poly.fst
end CloudProgram
end MetricKMedian.PCP.Compiler

end Inline_PCPCloudPrograms

end OAI
