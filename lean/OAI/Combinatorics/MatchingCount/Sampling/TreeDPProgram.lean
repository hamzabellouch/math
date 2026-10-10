import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPCounts

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

abbrev Params := ℕ×(ℕ×Parents)
abbrev State := ℕ×(Bags×Table)

def update (x : ((Bags×Parents)×(ℕ×Table))×(ℕ×ℕ)) : Table :=
  tabulate entry (context x.1,x.2)
def updateProgram : Realizer update :=
  composition (pair (composition first contextRealizer) second) updateRealizer

def step (x : ℕ×(Params×State)) : Params×State :=
  let p:=x.2.1
  let st:=x.2.2
  let l:=x.1
  let rem:=st.1-1
  (p,(rem,(trim st.2.1 l,
    update (((st.2.1,p.2.2),(l,st.2.2)),(p.2.1,p.1*rem)))))

def stepRealizer : Realizer step := by
  let p : Realizer (fun x : ℕ×(Params×State)=>x.2.1) := second.fst
  let st : Realizer (fun x : ℕ×(Params×State)=>x.2.2) := second.snd
  let l : Realizer (fun x : ℕ×(Params×State)=>x.1) := first
  let rem := composition st.fst predecessor
  let bs := composition (pair st.snd.fst l) trimRealizer
  let B := composition (pair p.fst rem) multiply
  let inp := pair (pair (pair st.snd.fst p.snd.snd) (pair l st.snd.snd)) (pair p.snd.fst B)
  let tbl := composition inp updateProgram
  exact (pair p (pair rem (pair bs tbl))).congr (fun _=>rfl)

def runState (p : Params) : List ℕ → Bags → Table → Bags×Table
  | [],bs,t => (bs,t)
  | l::ls,bs,t => runState p ls (trim bs l)
      (update (((bs,p.2.2),(l,t)),(p.2.1,p.1*ls.length)))

def run (x : Params×(List ℕ×(Bags×Table))) : Table := (runState x.1 x.2.1 x.2.2.1 x.2.2.2).2

lemma step_fold (p : Params) (ls : List ℕ) (bs : Bags) (t : Table) :
    ls.foldl (fun z l=>step (l,z)) (p,(ls.length,(bs,t)))=
      (p,(0,runState p ls bs t)) := by
  induction ls generalizing bs t with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.foldl_cons,List.length_cons,step,Nat.add_sub_cancel]
    exact ih _ _

def runRealizer : Realizer run := by
  let init : Realizer (fun x : Params×(List ℕ×(Bags×Table))=>
      (x.2.1,(x.1,(x.2.1.length,x.2.2)))) :=
    pair second.fst (pair first (pair (composition second.fst listLength) second.snd))
  exact (composition (composition init (fold stepRealizer)) second.snd.snd).congr (by
    intro x
    change ((x.2.1.foldl (fun z l=>step (l,z)) (x.1,(x.2.1.length,x.2.2))).2.2).2=_
    rw [step_fold]
    rfl)

lemma tabulate_materialized {X : Type} (f : X×(ℕ×ℕ) → ℕ) (x : X) (m B : ℕ) :
    tabulate f (x,(m,B))=UnitRefresh.Materialized.tabulate m B (fun a r=>f (x,(a.val,r))) :=
  tabulate_eq (fun ar=>f (x,ar))

lemma update_eq {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (bags : V → Finset (Fin m)) (R : Finset V) (parent : Fin m → Option (Fin m))
    (l : Fin m) (t : Table) (B : ℕ) (ps : Parents)
    (hps : ps.getD l.val (false,0)=match parent l with | none=>(false,0) | some p=>(true,p.val)) :
    update (((activeRep bags R,ps),(l.val,t)),(m,B))=
      UnitRefresh.Materialized.update bags R parent l B t := by
  unfold update context
  simp only [hps,privateNumber_activeRep,sharedNumber_activeRep,totalNumber_activeRep]
  rw [tabulate_materialized]
  unfold UnitRefresh.Materialized.update
  congr 1
  funext a r
  exact entry_eq bags R parent l a t r

lemma privateNumber_perm {a b : Bags} (h : a.Perm b) (l : ℕ) : privateNumber a l=privateNumber b l :=
  (h.filter _).length_eq
lemma sharedNumber_perm {a b : Bags} (h : a.Perm b) (l : ℕ) : sharedNumber a l=sharedNumber b l :=
  (h.filter _).length_eq
lemma totalNumber_perm {a b : Bags} (h : a.Perm b) (l : ℕ) : totalNumber a l=totalNumber b l :=
  (h.filter _).length_eq
lemma context_perm {a b : Bags} (h : a.Perm b) (ps : Parents) (l : ℕ) (t : Table) :
    context ((a,ps),(l,t))=context ((b,ps),(l,t)) := by
  simp only [context,privateNumber_perm h,sharedNumber_perm h,totalNumber_perm h]
lemma update_perm {a b : Bags} (h : a.Perm b) (ps : Parents) (l m B : ℕ) (t : Table) :
    update (((a,ps),(l,t)),(m,B))=update (((b,ps),(l,t)),(m,B)) := by
  simp only [update,context_perm h]

def parentTag {m : ℕ} : Option (Fin m) → Bool×ℕ
  | none => (false,0)
  | some p => (true,p.val)
def parentRep {m : ℕ} (p : Fin m → Option (Fin m)) : Parents := List.ofFn (parentTag ∘ p)
@[simp] lemma parentRep_length {m : ℕ} (p : Fin m → Option (Fin m)) : (parentRep p).length=m := by
  simp [parentRep]
@[simp] lemma parentRep_getD {m : ℕ} (p : Fin m → Option (Fin m)) (l : Fin m) :
    (parentRep p).getD l.val (false,0)=parentTag (p l) := by
  simp [parentRep,List.getD,l.isLt]

lemma run_eq {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
    (ls : List (Fin m)) (R : Finset V) (t : Table) (bs : Bags)
    (hbs : bs.Perm (activeRep bags R)) :
    (runState (Fintype.card V,(m,parentRep parent)) (ls.map Fin.val) bs t).2=
      UnitRefresh.Materialized.run bags parent ls R t := by
  induction ls generalizing R bs t with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.map_cons,runState,UnitRefresh.Materialized.run,List.length_map]
    rw [update_perm hbs]
    rw [update_eq bags R parent l t _ _ (parentRep_getD parent l)]
    apply ih
    exact ((hbs.filter _).trans (trim_activeRep bags R l))

end MatchingFPRAS.ExecutableDP

end OAI
