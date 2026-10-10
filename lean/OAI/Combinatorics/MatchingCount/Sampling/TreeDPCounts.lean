import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPEntry

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B]
def filterWith {f : A×B → Bool} (F : Realizer f) :
    Realizer (fun x : A×List B=>x.2.filter fun b=>f (x.1,b)) :=
  (composition (composition (mapWith (pair second F)) (filter second)) (map first)).congr (by
    intro x
    simp only [Function.comp_apply,List.filter_map,List.map_map]
    simp [Function.comp_def])
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

abbrev Bag := List ℕ
abbrev Bags := List Bag
abbrev Parents := List (Bool×ℕ)

def privateFlag (x : ℕ×Bag) : Bool := decide (x.2.length=1) && decide (x.1∈x.2)
def sharedFlag (x : ℕ×Bag) : Bool := decide (x.1∈x.2) && !(privateFlag x)
def totalFlag (x : ℕ×Bag) : Bool := decide (x.1∈x.2)
def privateNumber (bs : Bags) (l : ℕ) := (bs.filter fun b=>privateFlag (l,b)).length
def sharedNumber (bs : Bags) (l : ℕ) := (bs.filter fun b=>sharedFlag (l,b)).length
def totalNumber (bs : Bags) (l : ℕ) := (bs.filter fun b=>totalFlag (l,b)).length
def trim (bs : Bags) (l : ℕ) := bs.filter fun b=>!(totalFlag (l,b))

def totalFlagRealizer : Realizer totalFlag := composition (pair second first) membership
def privateFlagRealizer : Realizer privateFlag := composition
  (pair (composition (pair (composition second listLength) (constant 1)) natEqual) totalFlagRealizer) boolAnd
def sharedFlagRealizer : Realizer sharedFlag := composition
  (pair totalFlagRealizer (composition privateFlagRealizer boolNot)) boolAnd

def privateNumberRealizer : Realizer (fun x : Bags×ℕ=>privateNumber x.1 x.2) :=
  (composition (pair second first) (countWith privateFlagRealizer)).congr (fun _=>rfl)
def sharedNumberRealizer : Realizer (fun x : Bags×ℕ=>sharedNumber x.1 x.2) :=
  (composition (pair second first) (countWith sharedFlagRealizer)).congr (fun _=>rfl)
def totalNumberRealizer : Realizer (fun x : Bags×ℕ=>totalNumber x.1 x.2) :=
  (composition (pair second first) (countWith totalFlagRealizer)).congr (fun _=>rfl)
def trimRealizer : Realizer (fun x : Bags×ℕ=>trim x.1 x.2) :=
  composition (pair second first) (filterWith (composition totalFlagRealizer boolNot))

def context (x : (Bags×Parents)×(ℕ×Table)) : EntryCtx :=
  (x.1.2.getD x.2.1 (false,0),
    (x.2.1,(x.2.2,(privateNumber x.1.1 x.2.1,
      (sharedNumber x.1.1 x.2.1,totalNumber x.1.1 x.2.1)))))
def contextRealizer : Realizer context := by
  let bl : Realizer (fun x : (Bags×Parents)×(ℕ×Table)=>(x.1.1,x.2.1)) := pair first.fst second.fst
  let p := composition bl privateNumberRealizer
  let q := composition bl sharedNumberRealizer
  let r := composition bl totalNumberRealizer
  exact (pair (composition (pair first.snd second.fst) (getD (false,0)))
    (pair second.fst (pair second.snd (pair p (pair q r))))).congr (fun _=>rfl)

variable {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
noncomputable def bagRep (b : Finset (Fin m)) : Bag := b.toList.map Fin.val

noncomputable def activeRep (bags : V → Finset (Fin m)) (R : Finset V) : Bags := R.toList.map (bagRep ∘ bags)

@[simp] lemma mem_bagRep (b : Finset (Fin m)) (l : Fin m) : l.val∈bagRep b ↔ l∈b := by
  simp [bagRep,Fin.val_inj]
@[simp] lemma length_bagRep (b : Finset (Fin m)) : (bagRep b).length=b.card := by
  simp [bagRep]
lemma card_one_mem (b : Finset (Fin m)) (l : Fin m) : b.card=1 ∧ l∈b ↔ b={l} := by
  constructor
  · rintro ⟨h,hl⟩
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h
    have e : l=a := by simpa [ha] using hl
    simpa [e] using ha
  · rintro rfl; simp
@[simp] lemma privateFlag_bagRep (b : Finset (Fin m)) (l : Fin m) :
    privateFlag (l.val,bagRep b)=decide (b={l}) := by
  apply Bool.eq_iff_iff.mpr
  simp [privateFlag,card_one_mem]
@[simp] lemma sharedFlag_bagRep (b : Finset (Fin m)) (l : Fin m) :
    sharedFlag (l.val,bagRep b)=decide (l∈b ∧ b≠{l}) := by
  apply Bool.eq_iff_iff.mpr
  simp [sharedFlag,privateFlag_bagRep]
@[simp] lemma totalFlag_bagRep (b : Finset (Fin m)) (l : Fin m) :
    totalFlag (l.val,bagRep b)=decide (l∈b) := by simp [totalFlag]

omit [Fintype V] [DecidableEq V] in
lemma filter_length_toList [Fintype V] [DecidableEq V]
    (R : Finset V) (P : V → Prop) [DecidablePred P] :
    (R.toList.filter fun x=>decide (P x)).length=(R.filter P).card := by
  rw [←List.toFinset_card_of_nodup ((Finset.nodup_toList R).filter _)]
  simp

@[simp] lemma privateNumber_activeRep (bags : V → Finset (Fin m)) (R : Finset V) (l : Fin m) :
    privateNumber (activeRep bags R) l.val=UnitRefresh.privateCount bags R l := by
  simp only [privateNumber,activeRep,List.filter_map,List.length_map,Function.comp_def,privateFlag_bagRep]
  exact filter_length_toList R (fun x=>bags x={l})
@[simp] lemma sharedNumber_activeRep (bags : V → Finset (Fin m)) (R : Finset V) (l : Fin m) :
    sharedNumber (activeRep bags R) l.val=UnitRefresh.sharedCount bags R l := by
  simp only [sharedNumber,activeRep,List.filter_map,List.length_map,Function.comp_def,sharedFlag_bagRep]
  exact filter_length_toList R (fun x=>l∈bags x ∧ bags x≠{l})
@[simp] lemma totalNumber_activeRep (bags : V → Finset (Fin m)) (R : Finset V) (l : Fin m) :
    totalNumber (activeRep bags R) l.val=(R.filter fun x=>l∈bags x).card := by
  simp only [totalNumber,activeRep,List.filter_map,List.length_map,Function.comp_def,totalFlag_bagRep]
  exact filter_length_toList R (fun x=>l∈bags x)

omit [Fintype V] in
lemma trim_activeRep (bags : V → Finset (Fin m)) (R : Finset V) (l : Fin m) :
    (trim (activeRep bags R) l.val).Perm (activeRep bags (UnitRefresh.trim bags R l)) := by
  unfold trim activeRep UnitRefresh.trim
  rw [List.filter_map]
  apply List.Perm.map
  apply List.perm_of_nodup_nodup_toFinset_eq ((Finset.nodup_toList R).filter _) (Finset.nodup_toList _)
  ext x
  simp
end MatchingFPRAS.ExecutableDP

end OAI
