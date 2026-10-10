import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.Transactions

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton

def Connected {N : ℕ} (cut : Fin N → Prop) (i j : Fin N) : Prop :=
  ∀ k, min i.val j.val ≤ k.val → k.val < max i.val j.val → ¬cut k

instance {N : ℕ} (cut : Fin N → Prop) [DecidablePred cut] (i j : Fin N) :
    Decidable (Connected cut i j) := by unfold Connected; infer_instance

namespace Connected
variable {N : ℕ} {cut cut' : Fin N → Prop} {i j k a b : Fin N}
lemma refl (cut : Fin N → Prop) (i : Fin N) : Connected cut i i := by
  intro k hk hk'; omega
lemma symm (h : Connected cut i j) : Connected cut j i := by
  simpa only [Connected,min_comm,max_comm] using h
lemma trans (h : Connected cut i j) (h' : Connected cut j k) : Connected cut i k := by
  intro t ht ht'
  by_cases hh : min i.val j.val ≤ t.val ∧ t.val < max i.val j.val
  · exact h t hh.1 hh.2
  · exact h' t (by omega) (by omega)
lemma subinterval (h : Connected cut i j)
    (ha : min i.val j.val ≤ a.val) (ha' : a.val ≤ max i.val j.val)
    (hb : min i.val j.val ≤ b.val) (hb' : b.val ≤ max i.val j.val) :
    Connected cut a b := by
  intro t ht ht'
  exact h t (by omega) (by omega)
lemma adjacent_iff (hab : a.val+1=b.val) : Connected cut a b ↔ ¬cut a := by
  constructor
  · intro h; exact h a (by omega) (by omega)
  · intro h t ht ht'
    have he : t=a := Fin.ext (by omega)
    simpa only [he] using h
lemma congr (h : ∀ i, cut i ↔ cut' i) : Connected cut i j ↔ Connected cut' i j := by
  unfold Connected
  simp only [h]
lemma right_barrier (h : Connected cut i j) (hj : i.val < j.val) : ¬cut i :=
  h i (by omega) (by omega)

lemma edit_unrelated (hab : a.val+1=b.val)
    (hc : ∀ k, k≠a → (cut k ↔ cut' k))
    (hia : ¬Connected cut i a) (hib : ¬Connected cut i b) :
    Connected cut i j ↔ Connected cut' i j := by
  have not_cross (h : Connected cut' i j) :
      ¬ (min i.val j.val ≤ a.val ∧ a.val < max i.val j.val) := by
    rintro ⟨ha,ha'⟩
    by_cases hi : i.val ≤ a.val
    · apply hia
      intro t ht ht'
      have hne : t≠a := by intro he; subst t; omega
      exact (not_congr (hc t hne)).mpr (h t (by omega) (by omega))
    · apply hib
      intro t ht ht'
      have hne : t≠a := by intro he; subst t; omega
      exact (not_congr (hc t hne)).mpr (h t (by omega) (by omega))
  constructor
  · intro h t ht ht'
    have hne : t≠a := by
      intro he; subst t
      apply hia
      exact h.subinterval (by omega) (by omega) (by omega) (by omega)
    exact (not_congr (hc t hne)).mp (h t ht ht')
  · intro h t ht ht'
    have hne : t≠a := by intro he; subst t; exact not_cross h ⟨ht,ht'⟩
    exact (not_congr (hc t hne)).mpr (h t ht ht')
end Connected

variable {q N : ℕ}

def cellCut (f : Fin N → Cell q) (i : Fin N) : Prop := (f i).skeleton.rightExternal
instance (f : Fin N → Cell q) (i : Fin N) : Decidable (cellCut f i) := by
  unfold cellCut Skeleton.rightExternal Skeleton.last
  infer_instance

abbrev SameRegion (f : Fin N → Cell q) := Connected (cellCut f)

def Coherent (f : Fin N → Cell q) : Prop :=
  ∀ i j, i.val+1=j.val → Skeleton.Pair (f i).skeleton (f j).skeleton

lemma Coherent.internal {f : Fin N → Cell q} (hf : Coherent f)
    (i j : Fin N) (hij : i.val+1=j.val) (hc : SameRegion f i j) :
    Skeleton.InternalPair (f i).skeleton (f j).skeleton :=
  ⟨hf i j hij,(Connected.adjacent_iff hij).mp hc⟩

lemma SameRegion.task {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (hc : SameRegion f i j) : (f i).metadata.task=(f j).metadata.task := by
  suffices ∀ (a b : Fin N), a.val ≤ b.val → SameRegion f a b →
      (f a).metadata.task=(f b).metadata.task by
    by_cases hij : i.val ≤ j.val
    · exact this i j hij hc
    · exact (this j i (by omega) hc.symm).symm
  intro a b hab hc
  generalize hdiff : b.val-a.val=n
  induction n generalizing b with
  | zero =>
    have he : a=b := Fin.ext (by omega)
    simp [he]
  | succ n ih =>
    let p : Fin N := ⟨b.val-1,by omega⟩
    have hp : p.val+1=b.val := by dsimp [p]; omega
    have hpa : a.val ≤ p.val := by dsimp [p]; omega
    have he : p.val-a.val=n := by dsimp [p]; omega
    have hcp : SameRegion f a p := hc.subinterval (by omega) (by omega) (by omega) (by omega)
    have hcb : SameRegion f p b := hc.subinterval (by omega) (by omega) (by omega) (by omega)
    have hint := (hf.internal p b hp hcb).1.2.resolve_left
      (fun hh => (hf.internal p b hp hcb).2 hh.1)
    have hmeta := hint.2.2.2.2
    exact (ih p hpa hcp he).trans (congrArg₂ Task.mk hmeta.1 hmeta.2.1)

lemma Coherent.left_barrier {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (he : (f i).skeleton.leftExternal) (hji : j.val < i.val) : ¬SameRegion f j i := by
  intro hc
  let p : Fin N := ⟨i.val-1,by omega⟩
  have hp : p.val+1=i.val := by dsimp [p]; omega
  have hcp : SameRegion f p i := hc.subinterval (by dsimp [p]; omega)
    (by dsimp [p]; omega) (by omega) (by omega)
  have hpair := hf p i hp
  rcases hpair.2 with hh | hh
  · exact ((Connected.adjacent_iff hp).mp hcp) hh.1
  · exact hh.2.1 he

lemma Coherent.idle_component {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (hj : (f j).marker=.idle) (hc : SameRegion f i j) : i=j := by
  apply Fin.ext
  by_contra hne
  by_cases hh : i.val < j.val
  · exact hf.left_barrier (Or.inl hj) hh hc
  · exact hc.symm.right_barrier (by omega) (Or.inl hj)

lemma Coherent.right_wing {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (hi : (f i).marker=.full ∨ (f i).marker=.right)
    (hij : i.val < j.val) (hc : SameRegion f i j) : (f j).marker=.right := by
  generalize hdiff : j.val-i.val=n
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    let p : Fin N := ⟨j.val-1,by omega⟩
    have hp : p.val+1=j.val := by dsimp [p]; omega
    have hip : i.val ≤ p.val := by dsimp [p]; omega
    have hcp : SameRegion f i p := hc.subinterval (by omega) (by omega) (by omega) (by omega)
    have hpc : SameRegion f p j := hc.subinterval (by omega) (by omega) (by omega) (by omega)
    have hh : (f p).marker=.full ∨ (f p).marker=.right := by
      by_cases he : i=p
      · simpa only [←he] using hi
      · right
        apply ih (j:=p) (by have := Fin.val_ne_of_ne he; omega) hcp
        dsimp [p]; omega
    have hm := Skeleton.internal_marker_rule (hf.internal p j hp hpc)
    rcases hm with ⟨hm,_⟩ | ⟨_,hm⟩
    · rcases hh with hh | hh <;> simp [Cell.marker,hm] at hh
    · exact hm

lemma Coherent.unique_head {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (hi : (f i).skeleton.IsHead) (hj : (f j).skeleton.IsHead)
    (hc : SameRegion f i j) : i=j := by
  have hforward (a b : Fin N) (ha : (f a).skeleton.IsHead)
      (hb : (f b).skeleton.IsHead) (hab : a.val < b.val) (h : SameRegion f a b) : False := by
    rcases ha with ha | ha
    · exact h.right_barrier hab (Or.inr (Or.inl ha))
    · have hh := hf.right_wing (Or.inl ha) hab h
      rcases hb with hb | hb <;> simp [Cell.marker,hb] at hh
  apply Fin.ext
  by_contra hn
  by_cases hij : i.val < j.val
  · exact hforward i j hi hj hij hc
  · exact hforward j i hj hi (by omega) hc.symm

lemma Coherent.region_locked {f : Fin N → Cell q} (hf : Coherent f) {i j : Fin N}
    (hj : (f j).skeleton.IsHead) (hc : SameRegion f i j) : (f i).marker≠.idle := by
  intro hi
  have he := hf.idle_component hi hc.symm
  subst j
  change (f i).skeleton.marker=.idle at hi
  rcases hj with hj | hj <;> simp [hi] at hj

variable [NeZero q]

lemma Unary.cut_iff {S : Schedule q} {a b : Cell q} (he : Unary S a b) :
    a.skeleton.rightExternal ↔ b.skeleton.rightExternal := by
  cases he <;>
    simp only [Cell.idle,Cell.boundary,Cell.full,Skeleton.rightExternal,
      Skeleton.mark_marker,Skeleton.mark_last] <;> simp_all

structure UnaryAt (S : Schedule q) (f g : Fin N → Cell q) (i : Fin N) : Prop where
  off : ∀ h, h≠i → f h=g h
  edge : Unary S (f i) (g i)

namespace UnaryAt
variable {S : Schedule q} {f g : Fin N → Cell q} {i : Fin N} (hu : UnaryAt S f g i)
include hu
lemma cuts : ∀ h, cellCut f h ↔ cellCut g h := by
  intro h
  by_cases he : h=i
  · subst h; exact hu.edge.cut_iff
  · simp only [cellCut,hu.off h he]
lemma reads : ∀ h, (f h).LockedReads (g h) := by
  intro h
  by_cases he : h=i
  · subst h; exact hu.edge.lockedReads
  · rw [hu.off h he]; exact Cell.lockedReads_refl _
end UnaryAt

structure BinaryAt (S : Schedule q) (f g : Fin N → Cell q) (i j : Fin N) : Prop where
  adjacent : i.val+1=j.val
  off : ∀ h, h≠i → h≠j → f h=g h
  edge : Binary S (f i) (f j) (g i) (g j)

namespace BinaryAt
variable {S : Schedule q} {f g : Fin N → Cell q} {i j : Fin N} (hb : BinaryAt S f g i j)
include hb
lemma ne : i≠j := by intro he; have := hb.adjacent; subst j; omega
lemma reads : ∀ h, (f h).LockedReads (g h) := by
  intro h
  by_cases he : h=i
  · subst h; exact hb.edge.lockedReads.1
  · by_cases he' : h=j
    · subst h; exact hb.edge.lockedReads.2
    · rw [hb.off h he he']; exact Cell.lockedReads_refl _
lemma cuts (hi : cellCut f i ↔ cellCut g i) (hj : cellCut f j ↔ cellCut g j) :
    ∀ h, cellCut f h ↔ cellCut g h := by
  intro h
  by_cases he : h=i
  · subst h; exact hi
  · by_cases he' : h=j
    · subst h; exact hj
    · simp only [cellCut,hb.off h he he']
lemma cuts_off (hj : cellCut f j ↔ cellCut g j) :
    ∀ h, h≠i → (cellCut f h ↔ cellCut g h) := by
  intro h hi
  by_cases he : h=j
  · subst h; exact hj
  · simp only [cellCut,hb.off h hi he]
end BinaryAt

namespace Verification
open scoped BigOperators
variable (S : Schedule q)

noncomputable def sum (f : Fin N → Cell q) (h : Fin N) (j : Fin q) (t : ℕ) : Reg :=
  ∑ i : Fin N, if SameRegion f h i ∧ i.val < t then
    (f i).delta (S.clause (f h).metadata.task j) else 0
noncomputable def total (f : Fin N → Cell q) (h : Fin N) (j : Fin q) : Reg := sum S f h j N
noncomputable def leftSum (f : Fin N → Cell q) (h : Fin N) (j : Fin q) : Reg := sum S f h j h.val

omit [NeZero q] in
lemma sum_zero (f : Fin N → Cell q) (h : Fin N) (j : Fin q) : sum S f h j 0=0 := by
  simp [sum]

omit [NeZero q] in
lemma sum_succ (f : Fin N → Cell q) (h : Fin N) (j : Fin q) (a : Fin N) :
    sum S f h j (a.val+1)=sum S f h j a.val+
      if SameRegion f h a then (f a).delta (S.clause (f h).metadata.task j) else 0 := by
  classical
  have here : ∀ i : Fin N,
      (if SameRegion f h i ∧ i.val < a.val+1 then (f i).delta (S.clause (f h).metadata.task j) else 0) =
      (if SameRegion f h i ∧ i.val < a.val then (f i).delta (S.clause (f h).metadata.task j) else 0)+
      (if i=a then (if SameRegion f h a then (f a).delta (S.clause (f h).metadata.task j) else 0) else 0) := by
    intro i
    by_cases hic : SameRegion f h i
    · by_cases hi : i.val < a.val
      · have hne : i≠a := by intro he; subst i; omega
        simp [hic,hi,show i.val < a.val+1 by omega,hne]
      · by_cases he : i=a
        · subst i; simp [hic]
        · have hn : ¬ i.val < a.val+1 := by have := Fin.val_ne_of_ne he; omega
          simp [hic,hi,hn,he]
    · by_cases he : i=a
      · subst i; simp [hic]
      · simp [hic,he]
  simp only [sum,here,Finset.sum_add_distrib]
  simp

omit [NeZero q] in
lemma sum_congr {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {h k : Fin N} (hh : (f h).skeleton.IsHead) (hk : (g k).skeleton.IsHead)
    (hc : ∀ i, SameRegion f h i ↔ SameRegion g k i)
    (ht : (f h).metadata.task=(g k).metadata.task)
    (hr : ∀ i, (f i).LockedReads (g i)) (j : Fin q) (t : ℕ) :
    sum S f h j t=sum S g k j t := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : SameRegion f h i ∧ i.val < t
  · rw [ite_eq_left hm,ite_eq_left ⟨(hc i).mp hm.1,hm.2⟩]
    unfold Cell.delta
    rw [ht]
    funext r
    exact hr i (hf.region_locked hh hm.1.symm)
      (hg.region_locked hk ((hc i).mp hm.1).symm) _
  · have hm' : ¬(SameRegion g k i ∧ i.val < t) := by simpa only [←hc i] using hm
    rw [ite_eq_right hm,ite_eq_right hm']

omit [NeZero q] in
lemma leftSum_first {f : Fin N → Cell q} (hf : Coherent f) (h : Fin N) (j : Fin q)
    (he : (f h).skeleton.leftExternal) : leftSum S f h j=0 := by
  classical
  unfold leftSum sum
  apply Finset.sum_eq_zero
  intro i hi
  have hm : ¬(SameRegion f h i ∧ i.val < h.val) := by
    rintro ⟨hc,hi⟩
    exact hf.left_barrier he hi hc.symm
  simp only [ite_eq_right hm]

omit [NeZero q] in
lemma total_last {f : Fin N → Cell q} (h : Fin N) (j : Fin q)
    (he : (f h).skeleton.rightExternal) :
    total S f h j=leftSum S f h j+(f h).delta (S.clause (f h).metadata.task j) := by
  classical
  have hi : ∀ i : Fin N,
      (if SameRegion f h i ∧ i.val < N then (f i).delta (S.clause (f h).metadata.task j) else 0) =
      (if SameRegion f h i ∧ i.val < h.val then (f i).delta (S.clause (f h).metadata.task j) else 0)+
      if i=h then (f h).delta (S.clause (f h).metadata.task j) else 0 := by
    intro i
    by_cases hic : SameRegion f h i
    · by_cases hie : i=h
      · subst i; simp [hic]
      · have hih : i.val < h.val := by
          have hn := Fin.val_ne_of_ne hie
          by_contra hn'
          exact hic.right_barrier (by omega) he
        simp [hic,hih,hie]
    · have hne : i≠h := by intro he; subst i; exact hic (Connected.refl _ _)
      simp [hic,hne]
  simp only [total,leftSum,sum,hi,Finset.sum_add_distrib]
  simp

noncomputable def potential (f : Fin N → Cell q) (h : Fin N) (j : Fin q) : Phase → Reg
  | .readLeft => total S f h j-leftSum S f h j
  | .undoRight => total S f h j+leftSum S f h j
  | .readRight | .beforeGate | .afterGate | .undoLeft => total S f h j
  | _ => 0

def passed : Phase → Prop
  | .afterGate | .undoLeft | .undoRight | .finish => True
  | _ => False

def holds (f : Fin N → Cell q) (h : Fin N) (j : Fin q) : Prop :=
  (S.clause (f h).metadata.task j).truth (total S f h j)=true

def Good (f : Fin N → Cell q) (h : Fin N) : Prop :=
  let hd := (f h).head
  hd.reg=potential S f h hd.clause hd.phase ∧
    if hd.phase=.success then ∀ j : Fin q, j.val < (S.count (f h).metadata.task).val → holds S f h j
    else (∀ j : Fin q, j.val < hd.clause.val → holds S f h j) ∧
      (passed hd.phase → holds S f h hd.clause)

def AllGood (f : Fin N → Cell q) : Prop := ∀ h, (f h).marker=.full → Good S f h

lemma good_initial (f : Fin N → Cell q) (h : Fin N)
    (hp : (f h).head.phase=.acquisition) (hj : (f h).head.clause=0) (hr : (f h).head.reg=0) :
    Good S f h := by simp [Good,hp,hj,hr,potential,passed]

omit [NeZero q] in
lemma good_congr {f g : Fin N → Cell q} {h k : Fin N}
    (ht : (f h).metadata.task=(g k).metadata.task) (hh : (f h).head=(g k).head)
    (hT : ∀ j, total S f h j=total S g k j)
    (hL : ∀ j, leftSum S f h j=leftSum S g k j) : Good S f h ↔ Good S g k := by
  have hp : ∀ j p, potential S f h j p=potential S g k j p := by
    intro j p; cases p <;> simp only [potential,hT,hL]
  simp only [Good,hh,hp,ht,holds,hT]

omit [NeZero q] in
lemma good_same_cuts {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {h : Fin N} (hh : (f h).skeleton.IsHead)
    (hc : ∀ i, cellCut f i ↔ cellCut g i) (he : f h=g h)
    (hr : ∀ i, (f i).LockedReads (g i)) : Good S f h ↔ Good S g h := by
  have hk : (g h).skeleton.IsHead := he ▸ hh
  have hs := sum_congr S hf hg hh hk (fun _ => Connected.congr hc)
    (congrArg (fun c : Cell q => c.metadata.task) he) hr
  exact good_congr S (congrArg (fun c : Cell q => c.metadata.task) he)
    (congrArg Cell.head he) (fun j => hs j N) (fun j => hs j h.val)

omit [NeZero q] in
lemma good_semanticZero {f : Fin N → Cell q} {h : Fin N}
    (hg : Good S f h) (hz : SemanticZero S (f h)) :
    (f h).head.phase=.success ∧ (f h).metadata.zeroTask=true := by
  rcases hz.2 with ⟨hp,hr⟩ | ⟨hp,hf⟩ | hh
  · exfalso
    apply hr
    rcases hp with hp | hp | hp <;>
      simpa only [hp,potential] using hg.1
  · exfalso
    have hh := hg.2
    simp only [hp,reduceCtorEq,ite_false,passed,true_implies] at hh
    have htruth := hh.2
    unfold holds at htruth
    have hr : (f h).head.reg=total S f h (f h).head.clause := by
      simpa only [hp,potential] using hg.1
    rw [hr,htruth] at hf
    cases hf
  · exact hh

omit [NeZero q] in
lemma allGood_of_idle (f : Fin N → Cell q) (hf : ∀ i, (f i).marker=.idle) : AllGood S f := by
  intro h hh; simp [hf h] at hh

omit [NeZero q] in
lemma allGood_single {f g : Fin N → Cell q} (i : Fin N)
    (hf : ∀ h, h≠i → f h=g h)
    (ho : ∀ h, h≠i → (f h).marker=.full → (Good S f h ↔ Good S g h))
    (hi : ((f i).marker=.full → Good S f i) ↔ ((g i).marker=.full → Good S g i)) :
    AllGood S f ↔ AllGood S g := by
  constructor
  · intro hh h hm
    by_cases he : h=i
    · subst h; exact hi.mp (hh i) hm
    · have hm' : (f h).marker=.full := by rw [hf h he]; exact hm
      exact (ho h he hm').mp (hh h hm')
  · intro hh h hm
    by_cases he : h=i
    · subst h; exact hi.mpr (hh i) hm
    · have hm' : (g h).marker=.full := by rw [←hf h he]; exact hm
      exact (ho h he hm).mpr (hh h hm')

omit [NeZero q] in
lemma allGood_pair {f g : Fin N → Cell q} (i j : Fin N)
    (hf : ∀ h, h≠i → h≠j → f h=g h)
    (ho : ∀ h, h≠i → h≠j → (f h).marker=.full → (Good S f h ↔ Good S g h))
    (hi : (((f i).marker=.full → Good S f i) ∧ ((f j).marker=.full → Good S f j)) ↔
      (((g i).marker=.full → Good S g i) ∧ ((g j).marker=.full → Good S g j))) :
    AllGood S f ↔ AllGood S g := by
  constructor
  · intro hh h hm
    by_cases he : h=i
    · subst h; exact (hi.mp ⟨hh i,hh j⟩).1 hm
    · by_cases he' : h=j
      · subst h; exact (hi.mp ⟨hh i,hh j⟩).2 hm
      · have hm' : (f h).marker=.full := by rw [hf h he he']; exact hm
        exact (ho h he he' hm').mp (hh h hm')
  · intro hh h hm
    by_cases he : h=i
    · subst h; exact (hi.mpr ⟨hh i,hh j⟩).1 hm
    · by_cases he' : h=j
      · subst h; exact (hi.mpr ⟨hh i,hh j⟩).2 hm
      · have hm' : (g h).marker=.full := by rw [←hf h he he']; exact hm
        exact (ho h he he' hm).mpr (hh h hm')

omit [NeZero q] in
lemma total_eq_left_of_last {f : Fin N → Cell q} (i : Fin N) (j : Fin q)
    (hm : (f i).marker≠.left) (hl : (f i).skeleton.last) :
    total S f i j=leftSum S f i j := by
  have he := total_last S i j (Or.inr (Or.inr ⟨hm,hl⟩))
  rw [Cell.delta_stop _ _ hl.2,add_zero] at he
  exact he

omit [NeZero q] in
lemma leftSum_eq_zero_of_first {f : Fin N → Cell q} (hf : Coherent f) (i : Fin N) (j : Fin q)
    (hm : (f i).marker≠.right) (hl : (f i).skeleton.first) :
    leftSum S f i j=0 := leftSum_first S hf i j (Or.inr ⟨hm,hl⟩)

lemma unary_full_sums {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) {c : Cell q} {b b' : Bool}
    {j j' : Fin q} {p p' : Phase} {r r' : Reg}
    (hfi : f i=c.full b j p r) (hgi : g i=c.full b' j' p' r') :
    (∀ t, total S g i t=total S f i t) ∧
    (∀ t, leftSum S g i t=leftSum S f i t) := by
  have hs := sum_congr S hf hg (h:=i) (k:=i)
    (Or.inr (by simp [hfi,Cell.full,Skeleton.mark]))
    (Or.inr (by simp [hgi,Cell.full,Skeleton.mark]))
    (fun _ => Connected.congr hu.cuts)
    (by simp [hfi,hgi,Cell.full,Cell.metadata,Skeleton.mark]) hu.reads
  exact ⟨fun t => (hs t N).symm,fun t => (hs t i.val).symm⟩

omit [NeZero q] in
lemma below_next {P : Fin q → Prop} (i j : Fin q) (hij : i.val+1=j.val) :
    (∀ k : Fin q, k.val < j.val → P k) ↔ (∀ k : Fin q, k.val < i.val → P k) ∧ P i := by
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega),h i (by omega)⟩
  · rintro ⟨h,hi⟩ k hk
    by_cases he : k=i
    · simpa only [he] using hi
    · apply h k
      have := Fin.val_ne_of_ne he
      omega

omit [NeZero q] in
lemma below_success {P : Fin q → Prop} (i : Fin q) (m : ℕ) (hij : i.val+1=m) :
    (∀ k : Fin q, k.val < m → P k) ↔ (∀ k : Fin q, k.val < i.val → P k) ∧ P i := by
  constructor
  · intro h; exact ⟨fun k hk => h k (by omega),h i (by omega)⟩
  · rintro ⟨h,hi⟩ k hk
    by_cases he : k=i
    · simpa only [he] using hi
    · apply h k
      have := Fin.val_ne_of_ne he
      omega

lemma unary_local {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) :
    ((f i).marker=.full → Good S f i) ↔ ((g i).marker=.full → Good S g i) := by
  have he := hu.edge
  generalize hfi : f i=a at he
  generalize hgi : g i=b at he
  cases he with
  | create c b hc => simp [Cell.marker,Cell.boundary,Cell.idle,Skeleton.mark]
  | finish_acquisition c b hc =>
    have hgood : Good S g i := good_initial S g i (by simp [hgi,Cell.full])
      (by simp [hgi,Cell.full]) (by simp [hgi,Cell.full])
    simp [Cell.marker,Cell.boundary,Cell.full,Skeleton.mark,hgood]
  | read_enter c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    have hh : total S f i j=leftSum S f i j := total_eq_left_of_last S i j
      (by simp [hfi,Cell.marker,Cell.full,Skeleton.mark]) (by simpa [hfi,Cell.full] using hl)
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,hL,hh,holds]
  | read_turn c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    have hh : leftSum S f i j=0 := leftSum_eq_zero_of_first S hf i j
      (by simp [hfi,Cell.marker,Cell.full,Skeleton.mark]) (by simpa [hfi,Cell.full] using hl)
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,hh,holds]
  | read_exit c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,holds]
  | gate c b j r hl htruth =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp only [hfi,hgi,Cell.marker,Cell.full,Skeleton.mark,Good,Cell.metadata,potential,
      passed,reduceCtorEq,true_implies,ite_false,false_implies,and_true,hT,holds]
    constructor
    · rintro ⟨hr,hh⟩
      exact ⟨hr,hh,hr ▸ htruth⟩
    · rintro ⟨hr,hh,_⟩; exact ⟨hr,hh⟩
  | undo_enter c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,holds]
  | undo_turn c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    have hh : leftSum S f i j=0 := leftSum_eq_zero_of_first S hf i j
      (by simp [hfi,Cell.marker,Cell.full,Skeleton.mark]) (by simpa [hfi,Cell.full] using hl)
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,hL,hh,holds]
  | undo_exit c b j r hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    have hh : total S f i j=leftSum S f i j := total_eq_left_of_last S i j
      (by simp [hfi,Cell.marker,Cell.full,Skeleton.mark]) (by simpa [hfi,Cell.full] using hl)
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,passed,hT,hh,holds,
      CharTwo.add_self_eq_zero]
  | next c b j j' hj hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp only [hfi,hgi,Cell.marker,Cell.full,Skeleton.mark,Good,Cell.metadata,potential,
      passed,reduceCtorEq,true_implies,ite_false,false_implies,and_true,true_and,hT,holds]
    exact (below_next j j' hj).symm
  | success c b j hj hl =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp only [hfi,hgi,Cell.marker,Cell.full,Skeleton.mark,Good,Cell.metadata,potential,
      passed,reduceCtorEq,true_implies,ite_false,ite_true,true_and,hT,holds]
    exact (below_success j (S.count c.metadata.task).val hj).symm
  | pivot c b hl ht =>
    obtain ⟨hT,hL⟩ := unary_full_sums S hf hg hu hfi hgi
    simp [Good,hfi,hgi,Cell.marker,Cell.full,Cell.metadata,Skeleton.mark,potential,hT,holds]

lemma allGood_unary {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i : Fin N} (hu : UnaryAt S f g i) : AllGood S f ↔ AllGood S g := by
  apply allGood_single S i hu.off _ (unary_local S hf hg hu)
  intro h hne hh
  exact good_same_cuts S hf hg (Or.inr hh) hu.cuts (hu.off h hne) hu.reads
omit [NeZero q] in
lemma allGood_fields {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    (hc : ∀ i, cellCut f i ↔ cellCut g i)
    (hr : ∀ i, (f i).LockedReads (g i))
    (hm : ∀ i, (f i).marker=(g i).marker)
    (ht : ∀ i, (f i).metadata.task=(g i).metadata.task)
    (hh : ∀ i, (f i).head=(g i).head) : AllGood S f ↔ AllGood S g := by
  have he (i : Fin N) (hi : (f i).marker=.full) : Good S f i ↔ Good S g i := by
    have hs := sum_congr S hf hg (Or.inr hi) (Or.inr ((hm i).symm.trans hi))
      (fun _ => Connected.congr hc) (ht i) hr
    exact good_congr S (ht i) (hh i) (fun j => hs j N) (fun j => hs j i.val)
  constructor
  · intro h i hi; have hi' : (f i).marker=.full := (hm i).trans hi
    exact (he i hi').mp (h i hi')
  · intro h i hi; exact (he i hi).mpr (h i ((hm i) ▸ hi))

omit [NeZero q] in
lemma moving_sum_congr {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {h k : Fin N} (hhead : (f h).skeleton.IsHead) (khead : (g k).skeleton.IsHead)
    (hc : ∀ i, cellCut f i ↔ cellCut g i) (hconn : SameRegion f h k)
    (ht : (f h).metadata.task=(g k).metadata.task)
    (hr : ∀ i, (f i).LockedReads (g i)) (t : Fin q) (v : ℕ) :
    sum S f h t v=sum S g k t v := by
  apply sum_congr S hf hg hhead khead _ ht hr t v
  intro l
  change Connected (cellCut f) h l ↔ Connected (cellCut g) k l
  rw [←Connected.congr hc]
  exact ⟨fun hh => hconn.symm.trans hh,fun hh => hconn.trans hh⟩

omit [NeZero q] in
lemma move_sums {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j h k : Fin N} (ha : i.val+1=j.val)
    (hhead : (f h).skeleton.IsHead) (khead : (g k).skeleton.IsHead)
    (hc : ∀ i, cellCut f i ↔ cellCut g i) (hconn : SameRegion f h k)
    (hci : SameRegion f h i)
    (ht : (f h).metadata.task=(g k).metadata.task)
    (hr : ∀ i, (f i).LockedReads (g i)) :
    (∀ t, total S f h t=total S g k t) ∧
    (∀ t, sum S f h t j.val=sum S g k t i.val+(f i).delta (S.clause (f h).metadata.task t)) := by
  have hs := sum_congr S hf hg hhead khead (fun l => by
    change Connected (cellCut f) h l ↔ Connected (cellCut g) k l
    rw [←Connected.congr hc]
    exact ⟨fun hh => hconn.symm.trans hh,fun hh => hconn.trans hh⟩) ht hr
  refine ⟨fun t => hs t N,fun t => ?_⟩
  rw [←ha,sum_succ,ite_eq_left hci,hs]

omit [NeZero q] in
lemma good_read_left {f g : Fin N → Cell q} {i j : Fin N} {a b : Cell q}
    {s : Bool} {c : Fin q} {r δ : Reg}
    (hf : f j=b.full s c .readLeft r) (hg : g i=a.full s c .readLeft (r+δ))
    (ht : (f j).metadata.task=(g i).metadata.task)
    (hT : ∀ t, total S f j t=total S g i t)
    (hL : leftSum S f j c=leftSum S g i c+δ) : Good S f j ↔ Good S g i := by
  have he : r=total S f j c-leftSum S f j c ↔
      r+δ=total S g i c-leftSum S g i c := by
    rw [hT,hL]
    constructor
    · intro hr; rw [hr]; abel
    · intro hr
      apply add_right_cancel (b:=δ)
      rw [hr]; abel
  simp only [Good,hf,hg,Cell.full,reduceCtorEq,ite_false,potential,passed,false_implies,and_true]
  change (r=total S f j c-leftSum S f j c ∧ _) ↔
    (r+δ=total S g i c-leftSum S g i c ∧ _)
  rw [he]
  simp only [holds,ht,hT]

omit [NeZero q] in
lemma good_undo_right {f g : Fin N → Cell q} {i j : Fin N} {a b : Cell q}
    {s : Bool} {c : Fin q} {r δ : Reg}
    (hf : f i=a.full s c .undoRight r) (hg : g j=b.full s c .undoRight (r+δ))
    (ht : (f i).metadata.task=(g j).metadata.task)
    (hT : ∀ t, total S f i t=total S g j t)
    (hL : leftSum S g j c=leftSum S f i c+δ) : Good S f i ↔ Good S g j := by
  have he : r=total S f i c+leftSum S f i c ↔
      r+δ=total S g j c+leftSum S g j c := by
    rw [hT,hL,←add_assoc,add_left_inj]
  simp only [Good,hf,hg,Cell.full,reduceCtorEq,ite_false,potential,passed,true_implies]
  change (r=total S f i c+leftSum S f i c ∧ _) ↔
    (r+δ=total S g j c+leftSum S g j c ∧ _)
  rw [he]
  simp only [holds,ht,hT]

omit [NeZero q] in
lemma good_other_move {f g : Fin N → Cell q} {i j : Fin N}
    (ht : (f i).metadata.task=(g j).metadata.task) (hh : (f i).head=(g j).head)
    (hp : (f i).head.phase=.readRight ∨ (f i).head.phase=.undoLeft)
    (hT : ∀ t, total S f i t=total S g j t) : Good S f i ↔ Good S g j := by
  have hp' := hp
  rw [hh] at hp'
  rcases hp' with hp' | hp' <;>
    simp only [Good,hh,hp',potential,passed,false_implies,true_implies,reduceCtorEq,ite_false,
      holds,ht,hT]

lemma allGood_binary_cuts {f g : Fin N → Cell q} (hf : Coherent f) (hg : Coherent g)
    {i j : Fin N} (hb : BinaryAt S f g i j) (hc : ∀ h, cellCut f h ↔ cellCut g h)
    (hl : (((f i).marker=.full → Good S f i) ∧ ((f j).marker=.full → Good S f j)) ↔
      (((g i).marker=.full → Good S g i) ∧ ((g j).marker=.full → Good S g j))) :
    AllGood S f ↔ AllGood S g := by
  apply allGood_pair S i j hb.off _ hl
  intro h hi hj hh
  exact good_same_cuts S hf hg (Or.inr hh) hc (hb.off h hi hj) hb.reads

end Verification
end SourceBurnside.FiniteTable
end

end OAI
