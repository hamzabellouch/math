import Mathlib
import OAI.Combinatorics.UniformKServer.RawExpansion

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawFilter
open RawTyped
abbrev E := List ℕ×ℕ
abbrev F := List E×List ℕ×ℕ

def cover (e : E) (r : ℕ) : Bool := e.1.any (fun x=>decide (x=r))
def allCover (s : F) (r : ℕ) : Bool := s.1.all (fun e=>cover e r)
def expand (k M r : ℕ) (e : E) : List E :=
  bif cover e r then [e] else
    bif decide (e.2<M) then (List.range k).map (fun j=>(e.1.set j r,e.2+1)) else []
def births (k M r : ℕ) (e : E) : ℕ :=
  bif cover e r then 0 else bif decide (e.2<M) then k else 0
def step (k M : ℕ) (s : F) (r : ℕ) : F :=
  bif allCover s r then s else
    (s.1.flatMap (expand k M r),s.2.1++[r],s.2.2+(s.1.map (births k M r)).sum)
def entry {n k : ℕ} (e : UniformKServer.Entry n k) : E := (config e.position,e.moves)
def state {n k : ℕ} (s : UniformKServer.FilterState n k) : F :=
  (s.live.map entry,requests s.kept,s.created)

@[simp] theorem cover_entry {n k : ℕ} (e : UniformKServer.Entry n k) (r : Fin n) :
    cover (entry e) r.val=decide (Covers e r) := by
  apply Bool.eq_iff_iff.mpr
  simp [cover,entry,config,List.any_eq_true,Covers,Fin.ext_iff]

@[simp] theorem allCover_state {n k : ℕ} (s : UniformKServer.FilterState n k) (r : Fin n) :
    allCover (state s) r.val=decide (∀e∈s.live,Covers e r) := by
  apply Bool.eq_iff_iff.mpr
  simp [allCover,state,List.all_eq_true]

@[simp] theorem expand_entry {n k : ℕ} (M : ℕ) (r : Fin n) (e : UniformKServer.Entry n k) :
    expand k M r.val (entry e)=(UniformKServer.expand M r e).map entry := by
  rw [expand,cover_entry]
  simp only [Bool.cond_decide,UniformKServer.expand]
  change (if Covers e r then [entry e] else
    if e.moves<M then (List.range k).map (fun j=>(config e.position |>.set j r.val,e.moves+1)) else []) = _
  split_ifs with hcov hm
  · rfl
  · simp only [List.map_map]
    rw [RawExpansion.range_eq_ofFn, List.map_ofFn, ←List.ofFn_eq_map]
    apply congrArg List.ofFn
    funext j
    simp only [Function.comp_apply,entry,config_set]
    rfl
  · rfl

@[simp] theorem births_entry {n k : ℕ} (M : ℕ) (r : Fin n) (e : UniformKServer.Entry n k) :
    births k M r.val (entry e)=UniformKServer.births M r e := by
  rw [births,cover_entry]
  simp only [Bool.cond_decide]
  rfl

@[simp] theorem step_state {n k : ℕ} (M : ℕ) (s : UniformKServer.FilterState n k) (r : Fin n) :
    step k M (state s) r.val=state (UniformKServer.step M s r) := by
  simp only [step,allCover_state,Bool.cond_decide,UniformKServer.step]
  split_ifs with h
  · rfl
  · simp only [state,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,
      expand_entry,births_entry,requests,List.map_append,List.map_cons,List.map_nil]

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_cover (e : α→E) (r : α→ℕ) (he : Primrec e) (hr : Primrec r) :
    Primrec (fun x=>cover (e x) (r x)) := by
  simp only [cover, List.any_eq_not_all_not]
  fun_prop
@[fun_prop] theorem primitive_allCover (s : α→F) (r : α→ℕ) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>allCover (s x) (r x)) := by unfold allCover;fun_prop
@[fun_prop] theorem primitive_expand (k M r : α→ℕ) (e : α→E)
    (hk : Primrec k) (hM : Primrec M) (hr : Primrec r) (he : Primrec e) :
    Primrec (fun x=>expand (k x) (M x) (r x) (e x)) := by
  unfold expand
  apply Primrec.cond
  · fun_prop
  · fun_prop
  · exact Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)
@[fun_prop] theorem primitive_births (k M r : α→ℕ) (e : α→E)
    (hk : Primrec k) (hM : Primrec M) (hr : Primrec r) (he : Primrec e) :
    Primrec (fun x=>births (k x) (M x) (r x) (e x)) := by
  unfold births
  apply Primrec.cond
  · fun_prop
  · fun_prop
  · exact Primrec.cond (by fun_prop) hk (by fun_prop)
@[fun_prop] theorem primitive_step (k M : α→ℕ) (s : α→F) (r : α→ℕ)
    (hk : Primrec k) (hM : Primrec M) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>step (k x) (M x) (s x) (r x)) := by
  unfold step
  exact Primrec.cond (by fun_prop) hs (by fun_prop)
end Primitive
end UniformKServer.RawFilter

end


end

end OAI
