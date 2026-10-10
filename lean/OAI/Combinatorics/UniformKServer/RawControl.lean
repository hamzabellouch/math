import Mathlib
import OAI.Combinatorics.UniformKServer.EpochControl
import OAI.Combinatorics.UniformKServer.RawFilter
import OAI.Combinatorics.UniformKServer.RawRowSelect
import OAI.Combinatorics.UniformKServer.RawFallback

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawControl
open RawTyped RawMarks
abbrev S := RawFilter.F×RawFilter.E×List Bool×List Bool×Bool

def state {n k : ℕ} (s : EpochControl.State n k) : S :=
  (RawFilter.state s.filter,RawFilter.entry s.virtual,bits s.marked,bits s.seen,s.fallback)
def initial (n k : ℕ) (u : List ℕ) : S :=
  (([(u,0)],[],1),(u,0),empty k,empty n,false)
def trackingLabel (k : ℕ) (T coins : List ℕ) (s : S) (r : ℕ) : ℕ :=
  RawRowSelect.choose k T s.1.2.1 s.2.1.1 r (coins.getD s.1.2.1.length 0)
def label (k : ℕ) (T coins : List ℕ) (s : S) (r : ℕ) : ℕ :=
  bif s.2.2.2.2 then RawFallback.label k s.2.1.1 s.2.2.1 s.2.2.2.1 r
  else bif RawFilter.allCover s.1 r then pick (covers s.2.1.1 r)
  else trackingLabel k T coins s r

def nextEntry (e : RawFilter.E) (r j : ℕ) : RawFilter.E :=
  (e.1.set j r,e.2+(bif decide (e.1.getD j 0=r) then 0 else 1))

def step (n k M : ℕ) (T coins : List ℕ) (s : S) (r : ℕ) : S :=
  bif s.2.2.2.2 then
    let j:=RawFallback.label k s.2.1.1 s.2.2.1 s.2.2.2.1 r
    (RawFilter.step k M s.1 r,(s.2.1.1.set j r,s.2.1.2),
      RawFallback.nextMarked k s.2.2.1 s.2.2.2.1 r j,
      RawFallback.nextSeen n k s.2.2.2.1 r,true)
  else bif RawFilter.allCover s.1 r then
    (s.1,s.2.1,s.2.2.1,RawFallback.nextSeen n k s.2.2.2.1 r,s.2.2.2.2)
  else
    let e:=nextEntry s.2.1 r (trackingLabel k T coins s r)
    (RawFilter.step k M s.1 r,e,empty k,RawFallback.nextSeen n k s.2.2.2.1 r,decide (M<e.2))

@[simp] theorem initial_state {n k : ℕ} (u : Configuration n k) :
    initial n k (config u)=state (EpochControl.initial u) := by
  simp only [initial,empty_bits,state,EpochControl.initial,RawFilter.state,
    UniformKServer.initial,List.map_cons,List.map_nil,RawFilter.entry,requests]

@[simp] theorem nextEntry_state {n k : ℕ} (e : Entry n k) (r : Fin n) (j : Fin k) :
    nextEntry (RawFilter.entry e) r.val j.val=RawFilter.entry (EpochShadow.nextEntry e r j) := by
  simp only [nextEntry,RawFilter.entry,config_set,config_get,Bool.cond_decide,
    EpochShadow.nextEntry,Fin.ext_iff]

/-- Local representation lemma: only the current causal selector value is needed. -/
theorem label_state {n k : ℕ} (hk : 0<k) (T coins : List ℕ) (U : EpochShadow.Selector n k)
    (s : EpochControl.State n k) (r : Fin n)
    (hselect : trackingLabel k T coins (state s) r.val=(U s.filter.kept s.virtual.position r).val) :
    label k T coins (state s) r.val=(EpochControl.label hk U s r).val := by
  have hf:=RawFallback.label_bits hk (EpochControl.asRaw s) r
  simp only [EpochControl.asRaw] at hf
  simp only [label,state,RawFilter.entry,RawFilter.allCover_state,hf,
    RawMarks.covers_bits,RawMarks.pick_bits hk,Bool.cond_eq_ite,decide_eq_true_eq,
    EpochControl.label]
  change (if s.fallback=true then _ else if ∀z∈s.filter.live,Covers z r then _ else
    trackingLabel k T coins (state s) r.val)=_
  rw [hselect]
  split_ifs <;> rfl

theorem step_state {n k : ℕ} (hk : 0<k) (M : ℕ) (T coins : List ℕ) (U : EpochShadow.Selector n k)
    (s : EpochControl.State n k) (r : Fin n)
    (hselect : trackingLabel k T coins (state s) r.val=(U s.filter.kept s.virtual.position r).val) :
    step n k M T coins (state s) r.val=state (EpochControl.step hk M U s r) := by
  have hf:=RawFallback.step_bits hk (EpochControl.asRaw s) r
  simp only [EpochControl.asRaw] at hf
  by_cases hb : s.fallback=true
  · simp only [step,state,RawFilter.entry,hb,Bool.cond_true,EpochControl.step,
      RawFilter.step_state,ite_true]
    have hp:=congrArg Prod.fst hf
    have hm:=congrArg (fun x=>x.2.1) hf
    have hs:=congrArg (fun x=>x.2.2) hf
    dsimp only at hp hm hs
    rw [hp,hm,hs]
    rfl
  · have hb' : s.fallback=false := Bool.eq_false_iff.mpr hb
    by_cases hc : ∀z∈s.filter.live,Covers z r
    · simp only [step,state,RawFilter.allCover_state,RawFilter.entry,hb',Bool.cond_false,
        Bool.cond_decide,ite_eq_left hc,EpochControl.step,RawFallback.nextSeen_bits,Bool.false_eq_true,ite_false]
    · simp only [step,EpochControl.step,state,RawFilter.entry,RawFilter.allCover_state,hb',
        Bool.cond_false,Bool.cond_decide,ite_eq_right hc,Bool.false_eq_true,ite_false]
      change (RawFilter.step k M (RawFilter.state s.filter) r.val,
        nextEntry (RawFilter.entry s.virtual) r.val (trackingLabel k T coins (state s) r.val),
        empty k,RawFallback.nextSeen n k (bits s.seen) r.val,
        decide (M<(nextEntry (RawFilter.entry s.virtual) r.val
          (trackingLabel k T coins (state s) r.val)).2)) = _
      rw [hselect,RawFilter.step_state,nextEntry_state,empty_bits,RawFallback.nextSeen_bits]
      rfl

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_initial (n k : α→ℕ) (u : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hu : Primrec u) :
    Primrec (fun x=>initial (n x) (k x) (u x)) := by unfold initial;fun_prop
@[fun_prop] theorem primitive_tracking (k : α→ℕ) (T coins : α→List ℕ) (s : α→S) (r : α→ℕ)
    (hk : Primrec k) (hT : Primrec T) (hcoins : Primrec coins) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>trackingLabel (k x) (T x) (coins x) (s x) (r x)) := by unfold trackingLabel;fun_prop
@[fun_prop] theorem primitive_label (k : α→ℕ) (T coins : α→List ℕ) (s : α→S) (r : α→ℕ)
    (hk : Primrec k) (hT : Primrec T) (hcoins : Primrec coins) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>label (k x) (T x) (coins x) (s x) (r x)) := by
  unfold label
  exact Primrec.cond (by fun_prop) (by fun_prop)
    (Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop))
@[fun_prop] theorem primitive_nextEntry (e : α→RawFilter.E) (r j : α→ℕ)
    (he : Primrec e) (hr : Primrec r) (hj : Primrec j) :
    Primrec (fun x=>nextEntry (e x) (r x) (j x)) := by
  unfold nextEntry
  exact Primrec.pair (by fun_prop) (Primrec.nat_add.comp (by fun_prop)
    (Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop)))
@[fun_prop] theorem primitive_step (n k M : α→ℕ) (T coins : α→List ℕ) (s : α→S) (r : α→ℕ)
    (hn : Primrec n) (hk : Primrec k) (hM : Primrec M) (hT : Primrec T)
    (hcoins : Primrec coins) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>step (n x) (k x) (M x) (T x) (coins x) (s x) (r x)) := by
  unfold step
  exact Primrec.cond (by fun_prop) (by fun_prop)
    (Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop))
end Primitive
end UniformKServer.RawControl

end


end

end OAI
