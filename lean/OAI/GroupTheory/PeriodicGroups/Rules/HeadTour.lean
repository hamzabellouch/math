import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.LocalSyntax
import OAI.GroupTheory.PeriodicGroups.Rules.Palette

namespace OAI

section
universe u v w
namespace SourceBurnside.HeadTour
open scoped BigOperators

abbrev Registers := Fin 3 → ZMod 2

inductive Control (N : ℕ)
  | acquisition | readLeft (p : Fin N) | readRight (p : Fin N)
  | beforeGate | afterGate | undoLeft (p : Fin N) | undoRight (p : Fin N) | finish
  deriving DecidableEq, Fintype

structure State (N : ℕ) where
  ctrl : Control N
  reg : Registers
  side : Bool
  deriving DecidableEq

variable {N : ℕ}

structure Payload (N : ℕ) where
  nonempty : 0 < N
  delta : Fin N → Registers
  last_zero : delta ⟨N - 1, by omega⟩ = 0
  gate : Registers → Prop

namespace Payload
variable (P : Payload N)

def first : Fin N := ⟨0, P.nonempty⟩
def last : Fin N := ⟨N-1, by have := P.nonempty; omega⟩

def partialSum (k : ℕ) : Registers := ∑ p : Fin N, if p.val < k then P.delta p else 0

def total : Registers := ∑ p : Fin N, P.delta p

@[simp] lemma partialSum_zero : P.partialSum 0 = 0 := by simp [partialSum]
@[simp] lemma partialSum_N : P.partialSum N = P.total := by simp [partialSum,total]
lemma partialSum_succ (p : Fin N) : P.partialSum (p.val+1) = P.partialSum p.val + P.delta p := by
  have hh : ∀ q : Fin N, (if q.val < p.val+1 then P.delta q else 0) =
      (if q.val < p.val then P.delta q else 0) + (if q = p then P.delta p else 0) := by
    intro q
    by_cases h : q.val < p.val
    · have hn : q ≠ p := by intro e; subst q; omega
      simp [h, show q.val < p.val+1 by omega, hn]
    · by_cases e : q = p
      · subst q; simp
      · have hn : ¬ q.val < p.val+1 := by have : q.val ≠ p.val := Fin.val_ne_of_ne e; omega
        simp [h,hn,e]
  simp only [partialSum,hh,Finset.sum_add_distrib]
  simp

lemma partialSum_last : P.partialSum P.last.val = P.total := by
  have h := P.partialSum_succ P.last
  have he : P.last.val+1 = N := by have := P.nonempty; simp only [last]; omega
  rw [he,P.partialSum_N] at h
  simpa only [last,P.last_zero,add_zero] using h.symm

def potential : Control N → Registers
  | .acquisition => 0
  | .readLeft p => P.total - P.partialSum p.val
  | .readRight _ => P.total
  | .beforeGate => P.total
  | .afterGate => P.total
  | .undoLeft _ => P.total
  | .undoRight p => P.total + P.partialSum p.val
  | .finish => 0

def passed : Control N → Prop
  | .afterGate | .undoLeft _ | .undoRight _ | .finish => True
  | _ => False

def Good (s : State N) : Prop :=
  s.reg = P.potential s.ctrl ∧ (passed s.ctrl → P.gate P.total)

def SemanticZero (s : State N) : Prop :=
  ((s.ctrl = .acquisition ∨ s.ctrl = .finish) ∧ s.reg ≠ 0) ∨
    (s.ctrl = .afterGate ∧ ¬ P.gate s.reg)

inductive Edge : State N → State N → Prop
  | enter (r s) : Edge ⟨.acquisition,r,s⟩ ⟨.readLeft P.last,r,s⟩
  | read_left (p q : Fin N) (hp : q.val+1=p.val) (r s) :
      Edge ⟨.readLeft p,r,s⟩ ⟨.readLeft q,r+P.delta q,s⟩
  | read_turn (r s) : Edge ⟨.readLeft P.first,r,s⟩ ⟨.readRight P.first,r,s⟩
  | read_right (p q : Fin N) (hp : p.val+1=q.val) (r s) :
      Edge ⟨.readRight p,r,s⟩ ⟨.readRight q,r,s⟩
  | read_exit (r s) : Edge ⟨.readRight P.last,r,s⟩ ⟨.beforeGate,r,s⟩
  | gate (r s) (h : P.gate r) : Edge ⟨.beforeGate,r,s⟩ ⟨.afterGate,r,s⟩
  | undo_enter (r s) : Edge ⟨.afterGate,r,s⟩ ⟨.undoLeft P.last,r,s⟩
  | undo_left (p q : Fin N) (hp : q.val+1=p.val) (r s) :
      Edge ⟨.undoLeft p,r,s⟩ ⟨.undoLeft q,r,s⟩
  | undo_turn (r s) : Edge ⟨.undoLeft P.first,r,s⟩ ⟨.undoRight P.first,r,s⟩
  | undo_right (p q : Fin N) (hp : p.val+1=q.val) (r s) :
      Edge ⟨.undoRight p,r,s⟩ ⟨.undoRight q,r+P.delta p,s⟩
  | undo_exit (r s) : Edge ⟨.undoRight P.last,r,s⟩ ⟨.finish,r,s⟩

def Step (s t : State N) : Prop := P.Edge s t ∨ P.Edge t s
abbrev Reach := Relation.ReflTransGen P.Step

lemma edge_good {s t : State N} (he : P.Edge s t) : P.Good s ↔ P.Good t := by
  cases he with
  | enter r s => simp [Good,potential,passed,P.partialSum_last]
  | read_left p q h r s =>
    have hp : P.partialSum p.val = P.partialSum q.val + P.delta q := by
      rw [←h,P.partialSum_succ]
    simp only [Good,potential,passed,false_implies,and_true]
    rw [hp]
    constructor <;> intro hr
    · rw [hr]; abel
    · have hh := congrArg (fun x => x - P.delta q) hr
      simpa only [add_sub_cancel_right,sub_add_eq_sub_sub] using hh
  | read_turn r s => simp [Good,potential,passed,first]
  | read_right p q h r s => rfl
  | read_exit r s => rfl
  | gate r s hg =>
    simp only [Good,potential,passed,false_implies,and_true,true_implies]
    exact ⟨fun h => ⟨h,h ▸ hg⟩, And.left⟩
  | undo_enter r s => rfl
  | undo_left p q h r s => rfl
  | undo_turn r s => simp [Good,potential,passed,first]
  | undo_right p q h r s =>
    have hp : P.partialSum q.val = P.partialSum p.val + P.delta p := by
      rw [←h,P.partialSum_succ]
    simp only [Good,potential,passed,true_implies,hp]
    constructor
    · rintro ⟨hr,hg⟩; exact ⟨by rw [hr]; abel,hg⟩
    · rintro ⟨hr,hg⟩
      refine ⟨?_,hg⟩
      apply add_right_cancel (b := P.delta p)
      rw [hr]; abel
  | undo_exit r s => simp [Good,potential,passed,P.partialSum_last,CharTwo.add_self_eq_zero]

lemma reach_good {s t : State N} (h : P.Reach s t) (hg : P.Good s) : P.Good t := by
  induction h with
  | refl => exact hg
  | tail h e ih =>
    exact e.elim (fun he => (P.edge_good he).mp ih)
      (fun he => (P.edge_good he).mpr ih)

lemma good_not_zero {s : State N} (h : P.Good s) : ¬P.SemanticZero s := by
  rintro (⟨hc,hr⟩ | ⟨hc,hg⟩)
  · rcases hc with hc | hc <;> exact hr (h.1.trans (by simp [hc,potential]))
  · have hp : passed s.ctrl := by simp [hc,passed]
    have hh := h.2 hp
    apply hg
    simpa only [h.1,hc,potential] using hh

lemma good_initial (s : Bool) : P.Good ⟨.acquisition,0,s⟩ := by simp [Good,potential,passed]

theorem acquisition_safe {s : Bool} {t : State N}
    (h : P.Reach ⟨.acquisition,0,s⟩ t) : ¬ P.SemanticZero t :=
  P.good_not_zero (P.reach_good h (P.good_initial s))

theorem finish_sound {r : Registers} {s t : Bool}
    (h : P.Reach ⟨.acquisition,0,s⟩ ⟨.finish,r,t⟩) : P.gate P.total ∧ r=0 := by
  have hg := P.reach_good h (P.good_initial s)
  exact ⟨hg.2 trivial,hg.1⟩

def rank : Control N → ℕ
  | .acquisition => 0
  | .readLeft p => 1 + (N-1-p.val)
  | .readRight p => 1 + N + p.val
  | .beforeGate => 1 + 2*N
  | .afterGate => 2 + 2*N
  | .undoLeft p => 3 + 2*N + (N-1-p.val)
  | .undoRight p => 3 + 3*N + p.val
  | .finish => 3 + 4*N

lemma predecessor (s : State N) (h : s.ctrl ≠ .acquisition) :
    P.SemanticZero s ∨ ∃ t, P.Edge t s ∧ rank t.ctrl < rank s.ctrl ∧ t.side=s.side := by
  have hn := P.nonempty
  rcases s with ⟨c,r,b⟩
  cases c with
  | acquisition => exact (h rfl).elim
  | readLeft p =>
    by_cases hp : p = P.last
    · subst p
      exact Or.inr ⟨⟨.acquisition,r,b⟩,Edge.enter r b,by simp [rank],rfl⟩
    · have hp' : p.val+1 < N := by
        have hh : p.val ≠ N-1 := by intro he; apply hp; apply Fin.ext; exact he
        omega
      let q : Fin N := ⟨p.val+1,hp'⟩
      refine Or.inr ⟨⟨.readLeft q,r-P.delta p,b⟩,?_,by simp only [rank,q]; omega,rfl⟩
      simpa only [sub_add_cancel] using Edge.read_left (P:=P) q p rfl (r-P.delta p) b
  | readRight p =>
    by_cases hp : p=P.first
    · subst p
      exact Or.inr ⟨⟨.readLeft P.first,r,b⟩,Edge.read_turn r b,
        by simp only [rank,first]; omega,rfl⟩
    · have hp' : 0 < p.val := by
        have hh : p.val ≠ 0 := by intro he; apply hp; apply Fin.ext; exact he
        omega
      let q : Fin N := ⟨p.val-1,by omega⟩
      exact Or.inr ⟨⟨.readRight q,r,b⟩,Edge.read_right q p (by dsimp [q]; omega) r b,
        by dsimp [rank,q]; omega,rfl⟩
  | beforeGate =>
    exact Or.inr ⟨⟨.readRight P.last,r,b⟩,Edge.read_exit r b,
      by simp only [rank,last]; omega,rfl⟩
  | afterGate =>
    by_cases hg : P.gate r
    · exact Or.inr ⟨⟨.beforeGate,r,b⟩,Edge.gate r b hg,by simp [rank],rfl⟩
    · exact Or.inl (Or.inr ⟨rfl,hg⟩)
  | undoLeft p =>
    by_cases hp : p = P.last
    · subst p
      exact Or.inr ⟨⟨.afterGate,r,b⟩,Edge.undo_enter r b,by simp [rank,last],rfl⟩
    · have hp' : p.val+1 < N := by
        have hh : p.val ≠ N-1 := by intro he; apply hp; apply Fin.ext; exact he
        omega
      let q : Fin N := ⟨p.val+1,hp'⟩
      exact Or.inr ⟨⟨.undoLeft q,r,b⟩,Edge.undo_left q p rfl r b,
        by simp only [rank,q]; omega,rfl⟩
  | undoRight p =>
    by_cases hp : p=P.first
    · subst p
      exact Or.inr ⟨⟨.undoLeft P.first,r,b⟩,Edge.undo_turn r b,
        by simp only [rank,first]; omega,rfl⟩
    · have hp' : 0 < p.val := by
        have hh : p.val ≠ 0 := by intro he; apply hp; apply Fin.ext; exact he
        omega
      let q : Fin N := ⟨p.val-1,by omega⟩
      refine Or.inr ⟨⟨.undoRight q,r-P.delta q,b⟩,?_,by dsimp [rank,q]; omega,rfl⟩
      simpa only [sub_add_cancel] using
        Edge.undo_right (P:=P) q p (by dsimp [q]; omega) (r-P.delta q) b
  | finish =>
    exact Or.inr ⟨⟨.undoRight P.last,r,b⟩,Edge.undo_exit r b,
      by simp only [rank,last]; omega,rfl⟩

theorem rollback (s : State N) :
    P.Reach s ⟨.acquisition,0,s.side⟩ ∨ ∃ z, P.Reach s z ∧ P.SemanticZero z := by
  generalize he : rank s.ctrl = i
  induction i using Nat.strong_induction_on generalizing s with
  | h i ih =>
    by_cases hc : s.ctrl=.acquisition
    · by_cases hr : s.reg=0
      · left; convert (Relation.ReflTransGen.refl : P.Reach s s) using 1
        cases s; simp_all
      · exact Or.inr ⟨s,.refl,Or.inl ⟨Or.inl hc,hr⟩⟩
    · rcases P.predecessor s hc with hz | ⟨t,ht,hl,hs⟩
      · exact Or.inr ⟨s,.refl,hz⟩
      · have hb : P.Reach s t := Relation.ReflTransGen.single (Or.inr ht)
        rcases ih (rank t.ctrl) (by omega) t rfl with h | ⟨z,h,hz⟩
        · exact Or.inl (by simpa only [hs] using hb.trans h)
        · exact Or.inr ⟨z,hb.trans h,hz⟩

lemma reach_symm {s t : State N} (h : P.Reach s t) : P.Reach t s := by
  induction h with
  | refl => exact .refl
  | tail h e ih =>
    exact (Relation.ReflTransGen.single (show P.Step _ _ from e.symm)).trans ih

theorem finish_iff (s : Bool) :
    P.Reach ⟨.acquisition,0,s⟩ ⟨.finish,0,s⟩ ↔ P.gate P.total := by
  constructor
  · intro h; exact (P.finish_sound h).1
  · intro hg
    have hgood : P.Good ⟨.finish,0,s⟩ := ⟨rfl,fun _ => hg⟩
    rcases P.rollback ⟨.finish,0,s⟩ with h | ⟨z,h,hz⟩
    · exact P.reach_symm h
    · exact (P.good_not_zero (P.reach_good h hgood) hz).elim

lemma addressed_total (data : Fin N → ZMod 2) (addr : Fin 3 → Fin N)
    (hd : ∀ i k, P.delta i k = if i=addr k then data i else 0) :
    P.total = data ∘ addr := by
  ext k
  simp [total,Finset.sum_apply,hd]

end Payload

inductive FullControl (m N : ℕ)
  | clause (j : Fin m) (c : Control N)
  | success
  deriving DecidableEq, Fintype

structure FullState (m N : ℕ) where
  ctrl : FullControl m N
  reg : Registers
  side : Bool
  deriving DecidableEq

def atClause {m N : ℕ} (j : Fin m) (s : State N) : FullState m N :=
  ⟨.clause j s.ctrl,s.reg,s.side⟩

structure Plan (m N : ℕ) where
  nonempty : 0 < m
  payload : Fin m → Payload N
  zeroTask : Bool

namespace Plan
variable {m : ℕ} (Q : Plan m N)

def first : Fin m := ⟨0,Q.nonempty⟩
def last : Fin m := ⟨m-1,by have := Q.nonempty; omega⟩
def Holds (j : Fin m) : Prop := (Q.payload j).gate (Q.payload j).total

def Before (j : Fin m) : Prop := ∀ i : Fin m, i.val < j.val → Q.Holds i

def Good (s : FullState m N) : Prop := match s.ctrl with
  | .clause j c => (Q.payload j).Good ⟨c,s.reg,s.side⟩ ∧ Q.Before j
  | .success => s.reg=0 ∧ ∀ j, Q.Holds j

def Bad (s : FullState m N) : Prop := match s.ctrl with
  | .clause j c => (Q.payload j).SemanticZero ⟨c,s.reg,s.side⟩
  | .success => s.reg ≠ 0

def SemanticZero (s : FullState m N) : Prop :=
  Q.Bad s ∨ (s.ctrl=.success ∧ Q.zeroTask=true)

inductive Edge : FullState m N → FullState m N → Prop
  | tour (j : Fin m) {s t : State N} (h : (Q.payload j).Edge s t) :
      Edge (atClause j s) (atClause j t)
  | next (i j : Fin m) (h : i.val+1=j.val) (s : Bool) :
      Edge (atClause i ⟨.finish,0,s⟩) (atClause j ⟨.acquisition,0,s⟩)
  | done (s : Bool) : Edge (atClause Q.last ⟨.finish,0,s⟩) ⟨.success,0,s⟩
  | flip (s : Bool) (h : Q.zeroTask=false) : Edge ⟨.success,0,s⟩ ⟨.success,0,!s⟩

def Step (s t : FullState m N) : Prop := Q.Edge s t ∨ Q.Edge t s
abbrev Reach := Relation.ReflTransGen Q.Step

lemma before_next (i j : Fin m) (h : i.val+1=j.val) :
    Q.Before j ↔ Q.Holds i ∧ Q.Before i := by
  constructor
  · intro hb; exact ⟨hb i (by omega),fun t ht => hb t (by omega)⟩
  · rintro ⟨hi,hb⟩ t ht
    by_cases he : t=i
    · simpa only [he] using hi
    · apply hb
      have hne : t.val ≠ i.val := Fin.val_ne_of_ne he
      omega

lemma before_last : (Q.Holds Q.last ∧ Q.Before Q.last) ↔ ∀ i, Q.Holds i := by
  constructor
  · rintro ⟨hh,hb⟩ i
    by_cases he : i=Q.last
    · simpa only [he] using hh
    · apply hb
      have hne : i.val ≠ m-1 := by intro h; apply he; apply Fin.ext; exact h
      have := i.isLt
      dsimp [last]; omega
  · intro h; exact ⟨h _,fun i _ => h i⟩

lemma edge_good {s t : FullState m N} (h : Q.Edge s t) : Q.Good s ↔ Q.Good t := by
  cases h with
  | tour j h => exact and_congr_left (fun _ => (Q.payload j).edge_good h)
  | next i j h s =>
    simp only [Good,atClause,Payload.Good,Payload.potential,Payload.passed,
      true_implies,false_implies,and_true,true_and]
    exact (Q.before_next i j h).symm
  | done s =>
    simp only [Good,atClause,Payload.Good,Payload.potential,Payload.passed,
      true_implies,true_and]
    exact Q.before_last
  | flip s h => rfl

lemma reach_good {s t : FullState m N} (h : Q.Reach s t) (hg : Q.Good s) : Q.Good t := by
  induction h with
  | refl => exact hg
  | tail h e ih =>
    exact e.elim (fun he => (Q.edge_good he).mp ih) (fun he => (Q.edge_good he).mpr ih)

lemma good_not_bad {s : FullState m N} (h : Q.Good s) : ¬Q.Bad s := by
  cases hc : s.ctrl with
  | clause j c =>
    have hh : (Q.payload j).Good ⟨c,s.reg,s.side⟩ ∧ Q.Before j :=
      by simpa only [Good,hc] using h
    simpa only [Bad,hc] using (Q.payload j).good_not_zero hh.1
  | success =>
    have hh : s.reg=0 ∧ ∀ j, Q.Holds j := by simpa only [Good,hc] using h
    simpa only [Bad,hc] using not_not.mpr hh.1

lemma good_initial (s : Bool) : Q.Good (atClause Q.first ⟨.acquisition,0,s⟩) := by
  exact ⟨(Q.payload Q.first).good_initial s,fun i hi => (by dsimp [first] at hi; omega)⟩

theorem success_sound {r : Registers} {s t : Bool}
    (h : Q.Reach (atClause Q.first ⟨.acquisition,0,s⟩) ⟨.success,r,t⟩) :
    r=0 ∧ ∀ j, Q.Holds j := Q.reach_good h (Q.good_initial s)

theorem zero_sound {s : Bool} {t : FullState m N}
    (h : Q.Reach (atClause Q.first ⟨.acquisition,0,s⟩) t) (hz : Q.SemanticZero t) :
    t.ctrl=.success ∧ Q.zeroTask=true ∧ t.reg=0 ∧ ∀ j, Q.Holds j := by
  have hg := Q.reach_good h (Q.good_initial s)
  rcases hz with hb | ⟨hc,hz⟩
  · exact (Q.good_not_bad hg hb).elim
  · exact ⟨hc,hz,by simpa only [Good,hc] using hg⟩

lemma lift_reach (j : Fin m) {s t : State N} (h : (Q.payload j).Reach s t) :
    Q.Reach (atClause j s) (atClause j t) := by
  induction h with
  | refl => exact .refl
  | tail h e ih =>
    exact ih.tail (e.elim (fun he => Or.inl (Edge.tour j he))
      (fun he => Or.inr (Edge.tour j he)))

lemma rollback_clause (j : Fin m) (s : State N) :
    Q.Reach (atClause j s) (atClause Q.first ⟨.acquisition,0,s.side⟩) ∨
      ∃ z, Q.Reach (atClause j s) z ∧ Q.Bad z := by
  generalize he : j.val = i
  induction i using Nat.strong_induction_on generalizing j s with
  | h i ih =>
    rcases (Q.payload j).rollback s with hr | ⟨z,hz,hb⟩
    · have hr' := Q.lift_reach j hr
      by_cases hj : j=Q.first
      · left; simpa only [hj] using hr'
      · have hp : 0 < j.val := by
          have hh : j.val ≠ 0 := by intro h; apply hj; apply Fin.ext; exact h
          omega
        let p : Fin m := ⟨j.val-1,by omega⟩
        have hm : Q.Reach (atClause j ⟨.acquisition,0,s.side⟩)
            (atClause p ⟨.finish,0,s.side⟩) :=
          Relation.ReflTransGen.single (Or.inr (Edge.next p j (by dsimp [p]; omega) s.side))
        rcases ih p.val (by dsimp [p]; omega) p ⟨.finish,0,s.side⟩ rfl with hh | ⟨z,hz,hb⟩
        · exact Or.inl (hr'.trans (hm.trans hh))
        · exact Or.inr ⟨z,hr'.trans (hm.trans hz),hb⟩
    · exact Or.inr ⟨atClause j z,Q.lift_reach j hz,hb⟩

theorem rollback (s : FullState m N) :
    Q.Reach s (atClause Q.first ⟨.acquisition,0,s.side⟩) ∨
      ∃ z, Q.Reach s z ∧ Q.Bad z := by
  rcases s with ⟨c,r,b⟩
  cases c with
  | clause j c => exact Q.rollback_clause j ⟨c,r,b⟩
  | success =>
    by_cases hr : r=0
    · subst r
      have hm : Q.Reach ⟨.success,0,b⟩ (atClause Q.last ⟨.finish,0,b⟩) :=
        Relation.ReflTransGen.single (Or.inr (Edge.done b))
      rcases Q.rollback_clause Q.last ⟨.finish,0,b⟩ with hh | ⟨z,hz,hb⟩
      · exact Or.inl (hm.trans hh)
      · exact Or.inr ⟨z,hm.trans hz,hb⟩
    · exact Or.inr ⟨⟨.success,r,b⟩,.refl,hr⟩

lemma reach_symm {s t : FullState m N} (h : Q.Reach s t) : Q.Reach t s := by
  induction h with
  | refl => exact .refl
  | tail h e ih =>
    exact (Relation.ReflTransGen.single (show Q.Step _ _ from e.symm)).trans ih

theorem success_iff (s : Bool) :
    Q.Reach (atClause Q.first ⟨.acquisition,0,s⟩) ⟨.success,0,s⟩ ↔
      ∀ j, Q.Holds j := by
  constructor
  · intro h; exact (Q.success_sound h).2
  · intro hg
    have hgood : Q.Good ⟨.success,0,s⟩ := ⟨rfl,hg⟩
    rcases Q.rollback ⟨.success,0,s⟩ with h | ⟨z,h,hz⟩
    · exact Q.reach_symm h
    · exact (Q.good_not_bad (Q.reach_good h hgood) hz).elim

end Plan
end SourceBurnside.HeadTour

namespace SourceBurnside.FiniteTable
open LocalSyntax
open LocalSyntax.Skeleton

abbrev Meta := Metadata 10
abbrev Reg := Fin 3 → ZMod 2

instance : Fintype Marker := Fintype.ofList
  [.idle,.left,.boundary,.full,.right] (by intro x; cases x <;> simp)
deriving instance Fintype for Position
deriving instance Fintype for Metadata
deriving instance Fintype for Skeleton
deriving instance Fintype for Palette.Check

inductive Phase
  | acquisition | readLeft | readRight | beforeGate | afterGate
  | undoLeft | undoRight | finish | success
  deriving DecidableEq

instance : Fintype Phase := Fintype.ofList
  [.acquisition,.readLeft,.readRight,.beforeGate,.afterGate,.undoLeft,.undoRight,.finish,.success]
  (by intro x; cases x <;> simp)

structure Head (q : ℕ) where
  side : Bool
  clause : Fin q
  phase : Phase
  reg : Reg
  deriving DecidableEq, Fintype

structure Cell (q : ℕ) where
  skeleton : Skeleton q 10
  checker : Palette.Check (Fin q)
  data : Bool → ZMod 2
  certificate : ZMod 2
  head : Head q
  deriving DecidableEq, Fintype

structure Task where
  arity : Fin 10
  zeroTask : Bool
  deriving DecidableEq, Fintype

def Meta.task (m : Meta) : Task := ⟨m.arity,m.zeroTask⟩

inductive Address (q : ℕ)
  | data (side : Bool) (block : Fin 10) (position : Fin q)
  | certificate (position : Fin q)
  deriving DecidableEq, Fintype

structure Clause (q : ℕ) where
  address : Fin 3 → Address q
  truth : Reg → Bool

structure Schedule (q : ℕ) where
  count : Task → Fin (q+1)
  positive : ∀ t, 0 < (count t).val
  clause : Task → Fin q → Clause q

variable {q : ℕ} [NeZero q]

def defaultMeta : Meta := ⟨0,false,0⟩
def defaultHead : Head q := ⟨false,0,.acquisition,0⟩

namespace Cell

def pos (c : Cell q) : Position q := c.skeleton.pos
def marker (c : Cell q) : Marker := c.skeleton.marker
def metadata (c : Cell q) : Meta := c.skeleton.metadata

def wing (c : Cell q) (m : Marker) : Cell q :=
  { c with skeleton := c.skeleton.mark m, head := defaultHead }

def boundary (c : Cell q) (side : Bool) : Cell q :=
  { c with skeleton := c.skeleton.mark .boundary, head := {defaultHead with side := side} }

def full (c : Cell q) (side : Bool) (clause : Fin q) (phase : Phase) (reg : Reg) : Cell q :=
  { c with skeleton := c.skeleton.mark .full, head := ⟨side,clause,phase,reg⟩ }

def idle (c : Cell q) (side : Bool) : Cell q :=
  { c with
    skeleton := ⟨c.pos, .idle, defaultMeta⟩
    data := fun s => if s then 0 else c.data side
    certificate := 0
    head := defaultHead }

def setChecker (c : Cell q) (ch : Palette.Check (Fin q)) : Cell q :=
  { c with checker := ch }

def setColor (c : Cell q) (a : Fin q) : Cell q :=
  { c with skeleton := {c.skeleton with pos := .palette a} }

def isPalette (c : Cell q) : Prop := ∃ a, c.pos = .palette a
def isCore (c : Cell q) : Prop := ∃ p, c.pos = .core p

def endpoint (p : Phase) : Prop := p = .acquisition ∨ p = .beforeGate ∨
  p = .afterGate ∨ p = .finish ∨ p = .success

def Format (S : Schedule q) (dataSize : ℕ) (c : Cell q) : Prop :=
  c.skeleton.Admissible ∧
  (¬ c.isPalette → c.checker = .idle) ∧
  (∀ p, c.pos = .core p → dataSize ≤ p.val → c.data = 0) ∧
  (¬ c.isCore → c.data = 0 ∧ c.certificate = 0) ∧
  (c.marker = .idle → c.metadata = defaultMeta ∧ c.head = defaultHead ∧
    c.data true = 0 ∧ c.certificate = 0) ∧
  (c.marker = .left ∨ c.marker = .right → c.head = defaultHead) ∧
  (c.marker = .boundary → c.head.clause = 0 ∧ c.head.phase = .acquisition ∧ c.head.reg = 0) ∧
  (IsHead c.skeleton → (c.metadata.zeroTask = true → c.head.side = false)) ∧
  (c.marker = .full →
    (c.head.phase = .success → c.head.clause = 0) ∧
    (c.head.phase ≠ .success → c.head.clause.val < (S.count c.metadata.task).val) ∧
    (endpoint c.head.phase → c.skeleton.last))

def read (a : Address q) (c : Cell q) : ZMod 2 :=
  match a, c.pos with
  | .data s b p, .core r =>
      if c.metadata.block.val = b.val ∧ r = p then c.data s else 0
  | .certificate p, .core r =>
      if c.metadata.block.val = 0 ∧ r=p then c.certificate else 0
  | _, _ => 0

def delta (C : Clause q) (c : Cell q) : Reg := fun i => c.read (C.address i)

omit [NeZero q] in
lemma read_stop (a : Address q) (c : Cell q) (h : c.pos = .stop) : c.read a = 0 := by
  cases a <;> simp [read,h]

omit [NeZero q] in
lemma delta_stop (C : Clause q) (c : Cell q) (h : c.pos = .stop) : c.delta C = 0 := by
  funext i; exact read_stop (C.address i) c h

def SameNonColor (a b : Cell q) : Prop :=
  ∃ x y, a.pos = .palette x ∧ b.pos = .palette y ∧ a.setColor y = b

def HeadFree (c : Cell q) : Prop :=
  ¬ IsHead c.skeleton ∧ ∀ x, c.checker ≠ .head x

end Cell

def CheckerPair (a b : Cell q) : Prop :=
  (a.isPalette ∧ b.isPalette → Palette.Pair a.checker b.checker) ∧
  (a.isPalette ∧ b.pos = .stop → Palette.LastOK a.checker)

def Pair (a b : Cell q) : Prop := LocalSyntax.Skeleton.Pair a.skeleton b.skeleton ∧ CheckerPair a b

inductive Unary (S : Schedule q) : Cell q → Cell q → Prop
  | create (c : Cell q) (s : Bool) (h : c.skeleton.first) :
      Unary S (c.idle s) (c.boundary s)
  | finish_acquisition (c : Cell q) (s : Bool) (h : c.skeleton.last) :
      Unary S (c.boundary s) (c.full s 0 .acquisition 0)
  | read_enter (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.last) :
      Unary S (c.full s j .acquisition r) (c.full s j .readLeft r)
  | read_turn (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.first) :
      Unary S (c.full s j .readLeft r) (c.full s j .readRight r)
  | read_exit (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.last) :
      Unary S (c.full s j .readRight r) (c.full s j .beforeGate r)
  | gate (c : Cell q) (s : Bool) (j : Fin q) (r : Reg)
      (h : c.skeleton.last) (hg : (S.clause c.metadata.task j).truth r = true) :
      Unary S (c.full s j .beforeGate r) (c.full s j .afterGate r)
  | undo_enter (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.last) :
      Unary S (c.full s j .afterGate r) (c.full s j .undoLeft r)
  | undo_turn (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.first) :
      Unary S (c.full s j .undoLeft r) (c.full s j .undoRight r)
  | undo_exit (c : Cell q) (s : Bool) (j : Fin q) (r : Reg) (h : c.skeleton.last) :
      Unary S (c.full s j .undoRight r) (c.full s j .finish r)
  | next (c : Cell q) (s : Bool) (j j' : Fin q) (hj : j.val+1=j'.val)
      (h : c.skeleton.last) :
      Unary S (c.full s j .finish 0) (c.full s j' .acquisition 0)
  | success (c : Cell q) (s : Bool) (j : Fin q)
      (hj : j.val+1=(S.count c.metadata.task).val) (h : c.skeleton.last) :
      Unary S (c.full s j .finish 0) (c.full s 0 .success 0)
  | pivot (c : Cell q) (s : Bool) (h : c.skeleton.last) (ht : c.metadata.zeroTask=false) :
      Unary S (c.full s 0 .success 0) (c.full (!s) 0 .success 0)

inductive Binary (S : Schedule q) : Cell q → Cell q → Cell q → Cell q → Prop
  | acquire (a b : Cell q) (s : Bool)
      (hp : LocalSyntax.Skeleton.Pair (a.skeleton.mark .left) (b.skeleton.mark .boundary)) :
      Binary S (a.boundary s) (b.idle s) (a.wing .left) (b.boundary s)
  | read_left (a b : Cell q) (s : Bool) (j : Fin q) (r : Reg)
      (hp : LocalSyntax.Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right)) :
      Binary S (a.wing .left) (b.full s j .readLeft r)
        (a.full s j .readLeft (r+a.delta (S.clause a.metadata.task j))) (b.wing .right)
  | read_right (a b : Cell q) (s : Bool) (j : Fin q) (r : Reg)
      (hp : LocalSyntax.Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right)) :
      Binary S (a.full s j .readRight r) (b.wing .right)
        (a.wing .left) (b.full s j .readRight r)
  | undo_left (a b : Cell q) (s : Bool) (j : Fin q) (r : Reg)
      (hp : LocalSyntax.Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right)) :
      Binary S (a.wing .left) (b.full s j .undoLeft r)
        (a.full s j .undoLeft r) (b.wing .right)
  | undo_right (a b : Cell q) (s : Bool) (j : Fin q) (r : Reg)
      (hp : LocalSyntax.Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right)) :
      Binary S (a.full s j .undoRight r) (b.wing .right)
        (a.wing .left) (b.full s j .undoRight (r+a.delta (S.clause a.metadata.task j)))
  | checker_create (a b : Cell q) (p : Fin q) (x : Fin q)
      (ha : a.pos = .core p) (hp : p.val+1=q) (hb : b.isPalette) :
      Binary S a (b.setChecker .idle) a (b.setChecker (.head x))
  | checker_advance (a b : Cell q) (v x : Fin q)
      (ha : a.pos = .palette v) (hb : b.isPalette) (hv : v ≠ x) :
      Binary S (a.setChecker (.head x)) (b.setChecker .idle)
        (a.setChecker (.passed x)) (b.setChecker (.head x))
  | swap (a b : Cell q) (x y : Fin q) (ha : a.pos = .palette x) (hb : b.pos = .palette y)
      (he : a.setColor y = b) (hf : a.HeadFree) (hf' : b.HeadFree) :
      Binary S a b b a

def Replacement (S : Schedule q) (dataSize : ℕ) (v w : List (Cell q)) : Prop :=
  (∀ c ∈ v++w, c.Format S dataSize) ∧
  ((∃ a b, v=[a] ∧ w=[b] ∧ (Unary S a b ∨ Unary S b a)) ∨
   (∃ a b a' b', v=[a,b] ∧ w=[a',b'] ∧
     (Binary S a b a' b' ∨ Binary S a' b' a b)))

def SemanticZero (S : Schedule q) (c : Cell q) : Prop :=
  c.marker = .full ∧
    (((c.head.phase = .acquisition ∨ c.head.phase = .finish ∨ c.head.phase = .success) ∧
      c.head.reg ≠ 0) ∨
     (c.head.phase = .afterGate ∧ (S.clause c.metadata.task c.head.clause).truth c.head.reg = false) ∨
     (c.head.phase = .success ∧ c.metadata.zeroTask = true))

def UnaryZero (S : Schedule q) (dataSize : ℕ) (c : Cell q) : Prop :=
  ¬ c.Format S dataSize ∨ SemanticZero S c ∨
    ∃ x, c.pos = .palette x ∧ c.checker = .passed x

def BinaryZero (a b : Cell q) : Prop :=
  ¬ Pair a b ∨ (∃ x, a.pos = .palette x ∧ b.pos = .palette x) ∨
    ∃ x y, a.pos = .palette x ∧ a.checker = .head y ∧ b.pos = .stop ∧ x ≠ y

def Zero (S : Schedule q) (dataSize : ℕ) (v : List (Cell q)) : Prop :=
  (∃ c, v=[c] ∧ UnaryZero S dataSize c) ∨
  (∃ a b, v=[a,b] ∧ BinaryZero a b)

lemma replacement_lengths (S : Schedule q) (dataSize : ℕ) (v w : List (Cell q))
    (h : Replacement S dataSize v w) :
    v.length=w.length ∧ 1≤v.length ∧ v.length≤2 := by
  rcases h.2 with ⟨a,b,rfl,rfl,_⟩ | ⟨a,b,a',b',rfl,rfl,_⟩ <;> simp

lemma zero_lengths (S : Schedule q) (dataSize : ℕ) (v : List (Cell q))
    (h : Zero S dataSize v) : 1≤v.length ∧ v.length≤2 := by
  rcases h with ⟨c,rfl,_⟩ | ⟨a,b,rfl,_⟩ <;> simp

lemma replacement_symm (S : Schedule q) (dataSize : ℕ) (v w : List (Cell q)) :
    Replacement S dataSize v w ↔ Replacement S dataSize w v := by
  simp only [Replacement,List.mem_append,or_imp,forall_and]
  constructor <;> rintro ⟨⟨hv,hw⟩, hh⟩
  · refine ⟨⟨hw,hv⟩,?_⟩
    rcases hh with ⟨a,b,rfl,rfl,hh⟩ | ⟨a,b,a',b',rfl,rfl,hh⟩
    · exact Or.inl ⟨b,a,rfl,rfl,hh.symm⟩
    · exact Or.inr ⟨a',b',a,b,rfl,rfl,hh.symm⟩
  · refine ⟨⟨hw,hv⟩,?_⟩
    rcases hh with ⟨a,b,rfl,rfl,hh⟩ | ⟨a,b,a',b',rfl,rfl,hh⟩
    · exact Or.inl ⟨b,a,rfl,rfl,hh.symm⟩
    · exact Or.inr ⟨a',b',a,b,rfl,rfl,hh.symm⟩

end SourceBurnside.FiniteTable

end

end OAI
