import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeNaturalComb
import OAI.Combinatorics.MatchingCount.Machines.TreePredicate

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C : Type} [Codec A] [Codec B] [Codec C]
def Realizer.fst {f : A → B×C} (F : Realizer f) : Realizer (fun a=>(f a).1) := composition F first
def Realizer.snd {f : A → B×C} (F : Realizer f) : Realizer (fun a=>(f a).2) := composition F second
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

abbrev Table := List (List ℕ)
def read (x : Table×(ℕ×ℕ)) : ℕ := (x.1.getD x.2.1 []).getD x.2.2 0

def readRealizer : Realizer read :=
  composition (pair (composition (pair first second.fst) (getD [])) second.snd) (getD 0)

abbrev EntryCtx := (Bool×ℕ) × (ℕ × (Table × (ℕ × (ℕ × ℕ))))
def term (x : (EntryCtx×ℕ)×ℕ) : ℕ :=
  let c := x.1.1
  let r := x.1.2
  let k := x.2
  c.2.2.2.2.1.choose k * read (c.2.2.1,(c.2.1,c.2.2.2.1+k)) *
    read (c.2.2.1,(c.1.2,c.2.2.2.2.1-k+r))

def termRealizer : Realizer term := by
  let c : Realizer (fun x : (EntryCtx×ℕ)×ℕ=>x.1.1) := first.fst
  let r : Realizer (fun x : (EntryCtx×ℕ)×ℕ=>x.1.2) := first.snd
  let k : Realizer (fun x : (EntryCtx×ℕ)×ℕ=>x.2) := second
  let s := c.snd.snd.snd.snd.fst
  let u := c.snd.snd.snd.fst
  let t := c.snd.snd.fst
  let l := c.snd.fst
  let p := c.fst.snd
  let ch := composition (pair s k) natChoose
  let L := composition (pair t (pair l (composition (pair u k) add))) readRealizer
  let R := composition (pair t (pair p (composition (pair (composition (pair s k) subtract) r) add))) readRealizer
  exact composition (pair (composition (pair ch L) multiply) R) multiply

def entry (x : EntryCtx×(ℕ×ℕ)) : ℕ :=
  let c:=x.1
  let a:=x.2.1
  let r:=x.2.2
  if c.1.1 then
    if a=c.2.1 then 1 else if a=c.1.2 then
      ((List.range (c.2.2.2.2.1+1)).map fun k=>term ((c,r),k)).sum
    else read (c.2.2.1,(a,r))
  else if a=c.2.1 then read (c.2.2.1,(c.2.1,c.2.2.2.2.2))
    else read (c.2.2.1,(a,r))

def entryRealizer : Realizer entry := by
  let c : Realizer (fun x : EntryCtx×(ℕ×ℕ)=>x.1) := first
  let a : Realizer (fun x : EntryCtx×(ℕ×ℕ)=>x.2.1) := second.fst
  let r : Realizer (fun x : EntryCtx×(ℕ×ℕ)=>x.2.2) := second.snd
  let l := c.snd.fst
  let rd := composition (pair c.snd.snd.fst (pair a r)) readRealizer
  let al := composition (pair a l) natEqual
  let ap := composition (pair a c.fst.snd) natEqual
  let ks := composition (composition c.snd.snd.snd.snd.fst successor) range
  let sm := composition (composition (pair (pair c r) ks) (mapWith termRealizer)) listSum
  let rt := composition (pair c.snd.snd.fst (pair l c.snd.snd.snd.snd.snd)) readRealizer
  exact (choose c.fst.fst (choose al (constant 1) (choose ap sm rd)) (choose al rt rd)).congr (by
    intro x; simp only [entry,Function.comp_apply,decide_eq_true_eq])

variable {X Y : Type} [Codec X] [Codec Y]
def tabulate (f : X×(ℕ×ℕ) → Y) (x : X×(ℕ×ℕ)) : List (List Y) :=
  (List.range x.2.1).map fun a=>(List.range (x.2.2+1)).map fun r=>f (x.1,(a,r))

def tabulateRealizer {f : X×(ℕ×ℕ) → Y} (F : Realizer f) : Realizer (tabulate f) := by
  let rowF : Realizer (fun x : (X×ℕ)×ℕ=>f (x.1.1,(x.1.2,x.2))) :=
    composition (pair first.fst (pair first.snd second)) F
  let rows : Realizer (fun x : (X×ℕ)×ℕ=>
      (List.range (x.1.2+1)).map fun r=>f (x.1.1,(x.2,r))) :=
    composition (pair (pair first.fst second) (composition (composition first.snd successor) range))
      (mapWith rowF)
  exact composition (pair (pair first second.snd) (composition second.fst range)) (mapWith rows)

def updateRealizer : Realizer (tabulate entry) := tabulateRealizer entryRealizer

lemma read_eq (t : Table) (a r : ℕ) : read (t,(a,r))=UnitRefresh.Materialized.read t a r := rfl

lemma entry_eq {V : Type} {m : ℕ}
    (bags : V → Finset (Fin m)) (R : Finset V) (parent : Fin m → Option (Fin m))
    (l a : Fin m) (t : Table) (r : ℕ) :
    entry (((match parent l with | none=>(false,0) | some p=>(true,p.val)),
      (l.val,(t,(UnitRefresh.privateCount bags R l,
        (UnitRefresh.sharedCount bags R l,(R.filter fun x=>l∈bags x).card))))),(a.val,r))=
      UnitRefresh.Materialized.entry bags R parent l a t r := by
  have he : (a.val=l.val) ↔ a=l := Fin.val_inj
  cases hp : parent l with
  | none => simp only [entry,UnitRefresh.Materialized.entry,hp,Bool.false_eq_true,↓reduceIte,he,read_eq]
  | some p =>
    have he' : (a.val=p.val) ↔ a=p := Fin.val_inj
    simp only [entry,UnitRefresh.Materialized.entry,hp,↓reduceIte,he,he']
    split_ifs <;> try rfl

lemma tabulate_eq {m B : ℕ} (f : ℕ×ℕ → ℕ) :
    (List.range m).map (fun a=>(List.range (B+1)).map fun r=>f (a,r))=
      UnitRefresh.Materialized.tabulate m B (fun a r=>f (a.val,r)) := by
  unfold UnitRefresh.Materialized.tabulate
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    apply List.ext_getElem
    · simp
    · intro j hj hj'
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
end MatchingFPRAS.ExecutableDP

end OAI
