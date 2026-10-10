import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.WordRewriting

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Cell
lemma idle_format (c : Cell q) (S : Schedule q) (s : Bool) (hc : c.PayloadFormat d) :
    (c.idle s).Format S d := by
  dsimp [PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hc
  simp only [Format,idle,marker,metadata,pos,isPalette,isCore,Skeleton.Admissible,
    Skeleton.IsHead]
  simp only [reduceCtorEq,false_implies,or_self,and_true,true_implies,true_and]
  refine ⟨hc.1,?_,?_,rfl⟩
  · intro p hp hd
    have he := hc.2.1 p hp hd
    funext b
    simp [he]
  · intro hp
    have he := (hc.2.2 hp).1
    exact (by funext b; simp [he])

lemma boundary_format (c : Cell q) (S : Schedule q) (s : Bool) (hc : c.PayloadFormat d)
    (hs : c.metadata.zeroTask=true → s=false) : (c.boundary s).Format S d := by
  dsimp [PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hc
  simp only [Format,boundary,marker,metadata,pos,isPalette,isCore,Skeleton.Admissible,
    Skeleton.IsHead,Skeleton.mark]
  simpa only [reduceCtorEq,false_implies,true_implies,or_true,true_or,and_true,true_and,
    implies_true,defaultHead,false_or] using ⟨hc.1,hc.2.1,hc.2.2,hs⟩
end Cell

namespace Region
variable (R : Region q d) (S : Schedule q)

def boundaryCell (cursor : Fin R.size) (s : Bool) (i : Fin R.size) : Cell q :=
  if i<cursor then (R.cell i).wing .left else
    if i=cursor then (R.cell i).boundary s else (R.cell i).idle s

def boundaryWord (cursor : Fin R.size) (s : Bool) : List (Cell q) :=
  List.ofFn (R.boundaryCell cursor s)

def idleWord (s : Bool) : List (Cell q) := List.ofFn (fun i => (R.cell i).idle s)

lemma boundaryCell_format (cursor : Fin R.size) (s : Bool)
    (hs : R.task.zeroTask=true → s=false) (i : Fin R.size) :
    (R.boundaryCell cursor s i).Format S d := by
  unfold boundaryCell
  split
  · rename_i hi
    let state : HeadTour.FullState (S.count R.task).val R.size :=
      HeadTour.atClause (R.plan S).first ⟨.readLeft cursor,0,s⟩
    have hh := R.realizeCell_format S state hs i
    simpa [state,realizeCell,position,controlPosition,HeadTour.atClause,hi] using hh
  · split
    · apply Cell.boundary_format _ S s (R.payload_format i)
      intro ht
      exact hs ((congrArg Task.zeroTask (R.task_eq i)).symm.trans ht)
    · exact Cell.idle_format _ S s (R.payload_format i)

lemma boundaryCell_cursor (cursor : Fin R.size) (s : Bool) :
    R.boundaryCell cursor s cursor=(R.cell cursor).boundary s := by simp [boundaryCell]

omit [NeZero q] in
lemma acquisition_pair (i j : Fin R.size) (hij : i.val+1=j.val) :
    Skeleton.Pair ((R.cell i).skeleton.mark .left) ((R.cell j).skeleton.mark .boundary) := by
  obtain ⟨hstr,hi⟩ := R.adjacent i j hij
  refine ⟨hstr,Or.inr ?_⟩
  simp only [Skeleton.rightExternal,Skeleton.leftExternal,Skeleton.mark_marker,
    Skeleton.mark_last,Skeleton.mark_first,Skeleton.acceptsRight,Skeleton.acceptsLeft,
    Skeleton.internal_mark_left,Skeleton.internal_mark_right]
  simpa using And.intro hi.2.2.2.1 hi

lemma release_step (i j : Fin R.size) (hij : i.val+1=j.val) (s : Bool)
    (hs : R.task.zeroTask=true → s=false) :
    Step S d (R.boundaryWord j s) (R.boundaryWord i s) := by
  unfold boundaryWord
  apply step_two_ofFn _ _ i j hij
  · intro z hzi hzj
    have hi : z < i ↔ z < j := by
      have hzine : z.val≠i.val := fun h => hzi (Fin.ext h)
      have hzjne : z.val≠j.val := fun h => hzj (Fin.ext h)
      simp only [Fin.lt_def]
      omega
    simp only [boundaryCell,hi,hzi,hzj,ite_false]
  · have hij' : i < j := by simp only [Fin.lt_def]; omega
    have hji : ¬ j < i := by omega
    have hne : j≠i := by omega
    refine ⟨?_,Or.inr ⟨_,_,_,_,rfl,rfl,Or.inr ?_⟩⟩
    · intro c hc
      simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl <;> apply R.boundaryCell_format S _ s hs
    · simpa only [boundaryCell,hij',hji,hne,ne_eq,hne,ite_true,ite_false,lt_self_iff_false]
        using Binary.acquire (S:=S) (R.cell i) (R.cell j) s (R.acquisition_pair i j hij)

lemma remove_first (s : Bool) (hs : R.task.zeroTask=true → s=false) :
    Step S d (R.boundaryWord R.first s) (R.idleWord s) := by
  unfold boundaryWord idleWord
  apply step_one_ofFn _ _ R.first
  · intro i hi
    have hlt : ¬ i < R.first := by change ¬ i.val < 0; omega
    simp [boundaryCell,hlt,hi]
  · refine ⟨?_,Or.inl ⟨_,_,rfl,rfl,Or.inr ?_⟩⟩
    · intro c hc
      simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl
      · exact R.boundaryCell_format S _ s hs _
      · exact Cell.idle_format _ S s (R.payload_format _)
    · rw [R.boundaryCell_cursor]
      exact Unary.create _ _ R.first_first

theorem release (cursor : Fin R.size) (s : Bool) (hs : R.task.zeroTask=true → s=false) :
    Reach S d (R.boundaryWord cursor s) (R.idleWord s) := by
  generalize he : cursor.val=n
  induction n generalizing cursor with
  | zero =>
    have hx : cursor=R.first := Fin.ext he
    subst cursor
    exact Relation.ReflTransGen.single (R.remove_first S s hs)
  | succ n ih =>
    let i : Fin R.size := ⟨n,by omega⟩
    have he' : i.val+1=cursor.val := by dsimp [i]; omega
    exact (Relation.ReflTransGen.single (R.release_step S i cursor he' s hs)).trans
      (ih i rfl)

lemma unfinish (s : Bool) (hs : R.task.zeroTask=true → s=false) :
    Step S d (R.realize S (HeadTour.atClause (R.plan S).first ⟨.acquisition,0,s⟩))
      (R.boundaryWord R.last s) := by
  unfold realize boundaryWord
  apply step_one_ofFn _ _ R.last
  · intro i hi
    have hil : i<R.last := by
      have hh := i.isLt
      have hn : i.val≠R.last.val := fun h => hi (Fin.ext h)
      dsimp [last] at *
      exact show i.val<R.size-1 by omega
    simp [realizeCell,position,controlPosition,HeadTour.atClause,boundaryCell,hil]
  · refine ⟨?_,Or.inl ⟨_,_,rfl,rfl,Or.inr ?_⟩⟩
    · intro c hc
      simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl
      · exact R.realizeCell_format S _ hs _
      · exact R.boundaryCell_format S _ s hs _
    · rw [R.boundaryCell_cursor]
      simpa [realizeCell,position,controlPosition,HeadTour.atClause,phase,controlPhase,
        clause,clauseIndex,HeadTour.Plan.first]
        using Unary.finish_acquisition (S:=S) (R.cell R.last) s R.last_last

theorem literal_rollback_release (s : HeadTour.FullState (S.count R.task).val R.size)
    (hs : R.SideOK S s) :
    Reach S d (R.realize S s) (R.idleWord s.side) ∨
      ∃ w p a z, Reach S d (R.realize S s) w ∧ w=p++[a]++z ∧ Zero S d [a] := by
  rcases R.literal_rollback S s hs with hh | hz
  · left
    exact hh.trans ((Relation.ReflTransGen.single (R.unfinish S s.side hs)).trans
      (R.release S R.last s.side hs))
  · exact Or.inr hz

def actualState (h : Fin R.size) (hf : (R.cell h).Format S d)
    (hm : (R.cell h).marker=.full) : HeadTour.FullState (S.count R.task).val R.size :=
  let c := R.cell h
  { ctrl := if hp : c.head.phase=.success then .success else
      let j : Fin (S.count R.task).val := ⟨c.head.clause.val,by
        have hb := (hf.2.2.2.2.2.2.2.2 hm).2.1 hp
        rwa [R.task_eq h] at hb⟩
      .clause j (match c.head.phase with
        | .acquisition => .acquisition
        | .readLeft => .readLeft h
        | .readRight => .readRight h
        | .beforeGate => .beforeGate
        | .afterGate => .afterGate
        | .undoLeft => .undoLeft h
        | .undoRight => .undoRight h
        | .finish => .finish
        | .success => .finish)
    reg := c.head.reg
    side := c.head.side }

lemma actualState_side (h : Fin R.size) (hf : (R.cell h).Format S d)
    (hm : (R.cell h).marker=.full) :
    R.SideOK S (R.actualState S h hf hm) := by
  intro ht
  apply hf.2.2.2.2.2.2.2.1 (Or.inr hm)
  exact (congrArg Task.zeroTask (R.task_eq h)).trans ht

lemma actualState_position (h : Fin R.size) (hf : (R.cell h).Format S d)
    (hm : (R.cell h).marker=.full) :
    R.position S (R.actualState S h hf hm)=h := by
  have hend : Cell.endpoint (R.cell h).head.phase → R.last=h := by
    intro he
    have hh := (R.last_iff h).mp ((hf.2.2.2.2.2.2.2.2 hm).2.2 he)
    apply Fin.ext
    dsimp [last]
    omega
  cases hp : (R.cell h).head.phase <;>
    simp_all [actualState,position,controlPosition,Cell.endpoint]

lemma actualState_phase (h : Fin R.size) (hf : (R.cell h).Format S d)
    (hm : (R.cell h).marker=.full) :
    R.phase S (R.actualState S h hf hm)=(R.cell h).head.phase := by
  cases hp : (R.cell h).head.phase <;> simp [actualState,hp,phase,controlPhase]

lemma actualState_clause (h : Fin R.size) (hf : (R.cell h).Format S d)
    (hm : (R.cell h).marker=.full) :
    R.clause S (R.actualState S h hf hm)=(R.cell h).head.clause := by
  by_cases hp : (R.cell h).head.phase=.success
  · simp only [actualState,hp,dite_eq_left,clause]
    exact ((hf.2.2.2.2.2.2.2.2 hm).1 hp).symm
  · simp [actualState,hp,clause,clauseIndex]

lemma actualState_realize (h : Fin R.size) (hf : ∀ i, (R.cell i).Format S d)
    (hm : (R.cell h).marker=.full)
    (hl : ∀ i < h, (R.cell i).marker=.left) (hr : ∀ i, h < i → (R.cell i).marker=.right) :
    R.realize S (R.actualState S h (hf h) hm)=List.ofFn R.cell := by
  unfold realize
  apply congrArg List.ofFn
  funext i
  simp only [realizeCell,R.actualState_position S h (hf h) hm]
  split
  · rename_i hi
    have hmi := hl i hi
    have hh := (hf i).2.2.2.2.2.1 (Or.inl hmi)
    cases he : R.cell i with
    | mk sk ch da ce hd =>
      cases sk
      simp_all [Cell.marker,Cell.wing,Skeleton.mark]
  · rename_i hi
    split
    · rename_i hi'
      have hmi := hr i hi'
      have hh := (hf i).2.2.2.2.2.1 (Or.inr hmi)
      cases he : R.cell i with
      | mk sk ch da ce hd =>
        cases sk
        simp_all [Cell.marker,Cell.wing,Skeleton.mark]
    · rename_i hi'
      have hei : i=h := Fin.ext (by omega)
      subst i
      rw [R.actualState_clause,R.actualState_phase]
      change (R.cell h).full (R.cell h).head.side (R.cell h).head.clause
        (R.cell h).head.phase (R.cell h).head.reg=R.cell h
      cases he : R.cell h with
      | mk sk ch da ce hd =>
        cases sk
        cases hd
        simp_all [Cell.marker,Cell.full,Skeleton.mark]

theorem actual_rollback_release (h : Fin R.size) (hf : ∀ i, (R.cell i).Format S d)
    (hm : (R.cell h).marker=.full)
    (hl : ∀ i < h, (R.cell i).marker=.left) (hr : ∀ i, h < i → (R.cell i).marker=.right) :
    Reach S d (List.ofFn R.cell) (R.idleWord (R.cell h).head.side) ∨
      ∃ w p a z, Reach S d (List.ofFn R.cell) w ∧ w=p++[a]++z ∧ Zero S d [a] := by
  have hh := R.literal_rollback_release S (R.actualState S h (hf h) hm)
    (R.actualState_side S h (hf h) hm)
  rwa [R.actualState_realize S h hf hm hl hr] at hh

end Region
end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d N : ℕ} [NeZero q] {S : Schedule q}

omit [NeZero q] in
lemma Coherent.left_wing {f : Fin N → Cell q} (hf : Coherent f) {i h : Fin N}
    (hh : (f h).skeleton.IsHead) (hih : i.val<h.val) (hc : SameRegion f i h) :
    (f i).marker=.left := by
  cases hm : (f i).marker with
  | left => rfl
  | idle => exact (hf.region_locked hh hc hm).elim
  | boundary => exact (hc.right_barrier hih (Or.inr (Or.inl hm))).elim
  | full =>
    have he := hf.unique_head (Or.inr hm) hh hc
    have := congrArg Fin.val he
    omega
  | right =>
    have he := hf.right_wing (Or.inr hm) hih hc
    rcases hh with hh | hh
    · change (f h).marker=.boundary at hh
      rw [he] at hh
      cases hh
    · change (f h).marker=.full at hh
      rw [he] at hh
      cases hh

namespace Component
variable (f : Fin N → Cell q) (i : Fin N)
noncomputable def headIndex : Fin (size f i) :=
  ⟨i.val-(left f i).val,by
    have := left_le_self f i
    have := self_le_right f i
    dsimp [size]
    omega⟩
omit [NeZero q] in
lemma offset_headIndex : offset f i (headIndex f i)=i := by
  apply Fin.ext
  have := left_le_self f i
  dsimp [offset,headIndex]
  omega

omit [NeZero q] in
lemma before_head (hf : Coherent f) (hi : (f i).skeleton.IsHead)
    (j : Fin (size f i)) (hj : j<headIndex f i) : (f (offset f i j)).marker=.left := by
  apply hf.left_wing hi _ (connected_offset f i j).symm
  have := left_le_self f i
  change j.val < i.val-(left f i).val at hj
  change (left f i).val + j.val < i.val
  omega

omit [NeZero q] in
lemma after_head (hf : Coherent f) (hi : (f i).marker=.full)
    (j : Fin (size f i)) (hj : headIndex f i<j) : (f (offset f i j)).marker=.right := by
  apply hf.right_wing (Or.inl hi) _ (connected_offset f i j)
  have := left_le_self f i
  change i.val-(left f i).val < j.val at hj
  change i.val < (left f i).val + j.val
  omega

theorem actual_rollback_release (hs : Syntax S d (List.ofFn f)) (hi : (f i).marker=.full) :
    Reach S d (List.ofFn (region f i hs hi).cell)
      ((region f i hs hi).idleWord (f i).head.side) ∨
      ∃ w p a z, Reach S d (List.ofFn (region f i hs hi).cell) w ∧
        w=p++[a]++z ∧ Zero S d [a] := by
  have hm : ((region f i hs hi).cell (headIndex f i)).marker=.full := by
    change (f (offset f i (headIndex f i))).marker=.full
    rw [offset_headIndex]
    exact hi
  have hh := (region f i hs hi).actual_rollback_release S (headIndex f i)
    (fun j => hs.2.2 _ (List.mem_ofFn.mpr ⟨offset f i j,rfl⟩)) hm
    (before_head f i (Verification.coherent_of_syntax S hs) (Or.inr hi))
    (after_head f i (Verification.coherent_of_syntax S hs) hi)
  have he : (region f i hs hi).cell (headIndex f i)=f i := by
    change f (offset f i (headIndex f i))=f i
    rw [offset_headIndex]
  rwa [he] at hh

end Component
end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}
namespace Cell
omit [NeZero q] in
@[simp] lemma setChecker_self (c : Cell q) : c.setChecker c.checker=c := by cases c; rfl
omit [NeZero q] in
@[simp] lemma setChecker_setChecker (c : Cell q) (a b : Palette.Check (Fin q)) :
    (c.setChecker a).setChecker b=c.setChecker b := rfl
omit [NeZero q] in
@[simp] lemma setChecker_checker (c : Cell q) (a : Palette.Check (Fin q)) :
    (c.setChecker a).checker=a := rfl
omit [NeZero q] in
@[simp] lemma setChecker_pos (c : Cell q) (a : Palette.Check (Fin q)) :
    (c.setChecker a).pos=c.pos := rfl
@[simp] lemma setChecker_color (c : Cell q) (a : Palette.Check (Fin q)) :
    (c.setChecker a).color=c.color := rfl
omit [NeZero q] in
@[simp] lemma setChecker_palette (c : Cell q) (a : Palette.Check (Fin q)) :
    (c.setChecker a).isPalette ↔ c.isPalette := Iff.rfl
lemma setChecker_format (c : Cell q) (a : Palette.Check (Fin q)) (hp : c.isPalette) :
    (c.setChecker a).Format S d ↔ c.Format S d := by
  simp [Format,setChecker,isPalette,isCore,pos,marker,metadata] at hp ⊢
  obtain ⟨x,hx⟩ := hp
  simp [hx]
end Cell

def checkerIdle (w : List (Cell q)) : List (Cell q) := w.map (fun c => c.setChecker .idle)
omit [NeZero q] in
@[simp] lemma checkerIdle_append (v w : List (Cell q)) :
    checkerIdle (v++w)=checkerIdle v++checkerIdle w := List.map_append
omit [NeZero q] in
@[simp] lemma checkerIdle_cons (a : Cell q) (w : List (Cell q)) :
    checkerIdle (a::w)=a.setChecker .idle::checkerIdle w := rfl
omit [NeZero q] in
lemma checkerIdle_eq {w : List (Cell q)} (h : ∀ a∈w, a.checker=.idle) : checkerIdle w=w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [checkerIdle_cons,←h a (by simp),Cell.setChecker_self,ih]
    exact fun b hb => h b (by simp [hb])

lemma checker_create_step (a b : Cell q) (p x : Fin q) (ha : a.pos=.core p)
    (hp : p.val+1=q) (hb : b.isPalette) (hfa : a.Format S d) (hfb : b.Format S d) :
    Step S d [a,b.setChecker .idle] [a,b.setChecker (.head x)] := by
  refine ⟨[],[],[a,b.setChecker .idle],[a,b.setChecker (.head x)],rfl,rfl,?_,Or.inr ⟨_,_,_,_,rfl,rfl,Or.inl ?_⟩⟩
  · intro c hc
    simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl
    · exact hfa
    · exact (b.setChecker_format _ hb).mpr hfb
    · exact hfa
    · exact (b.setChecker_format _ hb).mpr hfb
  · exact Binary.checker_create a b p x ha hp hb

lemma checker_advance_step (a b : Cell q) (x : Fin q) (ha : a.isPalette)
    (hb : b.isPalette) (hn : a.color≠x) (hfa : a.Format S d) (hfb : b.Format S d) :
    Step S d [a.setChecker (.head x),b.setChecker .idle]
      [a.setChecker (.passed x),b.setChecker (.head x)] := by
  obtain ⟨v,hv⟩ := ha
  refine ⟨[],[],[a.setChecker (.head x),b.setChecker .idle],
    [a.setChecker (.passed x),b.setChecker (.head x)],rfl,rfl,?_,
    Or.inr ⟨_,_,_,_,rfl,rfl,Or.inl ?_⟩⟩
  · intro c hc
    simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl
    · exact (a.setChecker_format _ ⟨v,hv⟩).mpr hfa
    · exact (b.setChecker_format _ hb).mpr hfb
    · exact (a.setChecker_format _ ⟨v,hv⟩).mpr hfa
    · exact (b.setChecker_format _ hb).mpr hfb
  · exact Binary.checker_advance a b v x hv hb (by simpa [Cell.color,hv] using hn)

lemma checker_rollback_head (c : Cell q) (p : List (Cell q)) (a : Cell q)
    (s : List (Cell q)) (x t : Fin q) (hc : c.pos=.core t) (ht : t.val+1=q)
    (hfc : c.Format S d)
    (hf : ∀ b∈p++a::s, b.Format S d) (hpal : ∀ b∈p++a::s, b.isPalette)
    (hp : ∀ b∈p, b.checker=.passed x) (hn : ∀ b∈p, b.color≠x)
    (hs : ∀ b∈s, b.checker=.idle) :
    Reach S d (c::(p++a.setChecker (.head x)::s)) (c::checkerIdle (p++a::s)) := by
  induction p using List.reverseRecOn generalizing a s with
  | nil =>
    have st := step_symm (checker_create_step c a t x hc ht
      (hpal a (by simp)) hfc (hf a (by simp)))
    have he := step_context st [] s
    simpa only [List.nil_append,List.cons_append,List.nil_append,checkerIdle_cons,
      checkerIdle_eq hs] using Relation.ReflTransGen.single he
  | append_singleton p b ih =>
    have hb := hp b (by simp)
    have hb' := hn b (by simp)
    have hpb : b.isPalette := hpal b (by simp)
    have hpa : a.isPalette := hpal a (by simp)
    have hfb : b.Format S d := hf b (by simp)
    have hfa : a.Format S d := hf a (by simp)
    have hbp : b.setChecker (.passed x)=b := by rw [←hb,Cell.setChecker_self]
    have st := step_context (step_symm (checker_advance_step b a x hpb hpa hb' hfb hfa))
      (c::p) s
    have rest := ih b (a.setChecker .idle::s)
      (by intro z hz; simp only [List.mem_append,List.mem_cons] at hz; rcases hz with hz|rfl|hz
          · exact hf z (by simp [hz])
          · exact hfb
          · rcases hz with rfl|hz
            · exact (a.setChecker_format _ hpa).mpr hfa
            · exact hf z (by simp [hz]))
      (by intro z hz; simp only [List.mem_append,List.mem_cons] at hz; rcases hz with hz|rfl|hz
          · exact hpal z (by simp [hz])
          · exact hpb
          · rcases hz with rfl|hz
            · exact hpa
            · exact hpal z (by simp [hz]))
      (fun z hz => hp z (by simp [hz])) (fun z hz => hn z (by simp [hz]))
      (by simp only [List.forall_mem_cons,Cell.setChecker_checker]; exact ⟨True.intro,hs⟩)
    have he : checkerIdle (p++b::a.setChecker .idle::s)=checkerIdle ((p++[b])++a::s) := by
      simp [List.append_assoc]
    rw [he] at rest
    apply Relation.ReflTransGen.head _ rest
    simpa only [List.cons_append,List.append_assoc,List.nil_append,hbp] using st

def asChecker (c : Cell q) : Palette.Cell (Fin q) (Cell q) := ⟨c.color,c.checker,c⟩
lemma checker_pattern (w : List (Cell q))
    (hc : w.IsChain (fun a b => Palette.Pair a.checker b.checker))
    (hl : ∀ a∈w.getLast?, Palette.LastOK a.checker) :
    (∀ a∈w, a.checker=.idle) ∨
    ∃ p a s x, w=p++a::s ∧ a.checker=.head x ∧
      (∀ b∈p, b.checker=.passed x) ∧ (∀ b∈s, b.checker=.idle) := by
  have ht : Palette.Syntax (w.map asChecker) := by
    constructor
    · simpa [List.isChain_map,asChecker] using hc
    · intro a ha
      simp only [List.getLast?_map,Option.mem_def,Option.map_eq_some_iff] at ha
      obtain ⟨b,hb,rfl⟩ := ha
      exact hl b hb
  have hcheck : ∀ a∈w.map asChecker, a.aux.checker=a.check := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    rfl
  rcases Palette.syntax_form (w.map asChecker) ht with hi|⟨p,a,s,x,he,ha,hp,hs⟩
  · left; intro a ha
    exact hi (asChecker a) (List.mem_map.mpr ⟨a,ha,rfl⟩)
  · have he' := congrArg (List.map Palette.Cell.aux) he
    simp only [List.map_map,Function.comp_def,asChecker,List.map_append,
      List.map_cons] at he'
    have he'' : w=p.map Palette.Cell.aux++a.aux::s.map Palette.Cell.aux := by simpa using he'
    refine Or.inr ⟨p.map Palette.Cell.aux,a.aux,s.map Palette.Cell.aux,x,he'',?_,?_,?_⟩
    · rw [hcheck a (by rw[he]; simp),ha]
    · intro b hb
      obtain ⟨e,he',rfl⟩ := List.mem_map.mp hb
      exact (hcheck e (by rw[he]; simp [he'])).trans (hp e he')
    · intro b hb
      obtain ⟨e,he',rfl⟩ := List.mem_map.mp hb
      exact (hcheck e (by rw[he]; simp [he'])).trans (hs e he')

theorem Survives.checker_rollback {c z : Cell q} {w : List (Cell q)} {t : Fin q}
    (hw : Survives S d (c::w++[z])) (hc : c.pos=.core t) (ht : t.val+1=q)
    (hz : z.pos=.stop) (hp : ∀ a∈w, a.isPalette) :
    Reach S d (c::w++[z]) (c::checkerIdle w++[z]) := by
  have hv : Survives S d w := hw.infix ⟨[c],[z],rfl⟩
  have hchain : w.IsChain (fun a b => Palette.Pair a.checker b.checker) := by
    exact hv.chain.imp_of_mem_imp (fun a b ha hb hab => hab.2.1 ⟨hp a ha,hp b hb⟩)
  have hlast : ∀ a∈w.getLast?, Palette.LastOK a.checker := by
    intro a ha
    obtain ⟨p,rfl⟩ := List.getLast?_eq_some_iff.mp ha
    exact (hw.pair ⟨c::p,[],by simp⟩).2.2 ⟨hp a (by simp),hz⟩
  rcases checker_pattern w hchain hlast with hi|⟨p,a,s,x,rfl,ha,hp',hs⟩
  · rw [checkerIdle_eq hi]
  · have hn : ∀ b∈p, b.color≠x := by
      intro b hb he
      have hbx : b.pos=.palette x := by
        obtain ⟨y,hy⟩ := hp b (by simp [hb])
        have hyx : y=x := by simpa [Cell.color,hy] using he
        simpa [hyx] using hy
      have hzero : Zero S d [b] := Or.inl ⟨b,rfl,Or.inr (Or.inr ⟨x,hbx,hp' b hb⟩)⟩
      exact (hv.infix ((List.singleton_infix_iff _ _).mpr (by simp [hb]))).not_zero hzero
    have hh := checker_rollback_head c p a s x t hc ht
      (hw.format (by simp)) (fun b hb => hv.format hb) hp hp' hn hs
    have hea : a.setChecker (.head x)=a := by rw [←ha,Cell.setChecker_self]
    simpa only [List.nil_append,List.cons_append,hea] using reach_context hh [] [z]

lemma checker_seek_missing (c : Cell q) (p : List (Cell q)) (a : Cell q)
    (s : List (Cell q)) (z : Cell q) (x : Fin q) (hz : z.pos=.stop)
    (hf : ∀ b∈a::s, b.Format S d) (hp : ∀ b∈a::s, b.isPalette)
    (ha : a.color≠x) (hs : ∀ b∈s, b.checker=.idle) (hn : ∀ b∈s, b.color≠x) :
    ∃ v l u r, Reach S d (c::p++a.setChecker (.head x)::s++[z]) v ∧
      v=l++u++r ∧ Zero S d u := by
  induction s generalizing p a with
  | nil =>
    obtain ⟨y,hy⟩ := hp a (by simp)
    refine ⟨_,c::p,[a.setChecker (.head x),z],[],.refl,by simp,
      Or.inr ⟨a.setChecker (.head x),z,rfl,Or.inr (Or.inr ?_)⟩⟩
    exact ⟨y,x,hy,rfl,hz,by simpa [Cell.color,hy] using ha⟩
  | cons b s ih =>
    have hpb := hp b (by simp)
    have hpa := hp a (by simp)
    have hfb := hf b (by simp)
    have hfa := hf a (by simp)
    have hb : b.setChecker .idle=b := by rw [←hs b (by simp),Cell.setChecker_self]
    have st := step_context (checker_advance_step a b x hpa hpb ha hfa hfb) (c::p) (s++[z])
    obtain ⟨v,l,u,r,hr,he,hzero⟩ := ih (p++[a.setChecker (.passed x)]) b
      (fun e he => hf e (by simp [he])) (fun e he => hp e (by simp [he]))
      (hn b (by simp)) (fun e he => hs e (by simp [he])) (fun e he => hn e (by simp [he]))
    refine ⟨v,l,u,r,.head ?_ hr,he,hzero⟩
    simpa only [List.cons_append,List.nil_append,List.append_assoc,hb] using st

lemma Survives.idle_palette_all_colors {c z : Cell q} {w : List (Cell q)} {t : Fin q}
    (hw : Survives S d (c::w++[z])) (hc : c.pos=.core t) (ht : t.val+1=q)
    (hz : z.pos=.stop) (hwn : w≠[]) (hp : ∀ a∈w, a.isPalette)
    (hi : ∀ a∈w, a.checker=.idle) : ∀ x, x∈w.map Cell.color := by
  intro x
  by_contra hmiss
  have hn : ∀ a∈w, a.color≠x := by
    intro a ha hx
    exact hmiss (List.mem_map.mpr ⟨a,ha,hx⟩)
  cases w with
  | nil => exact hwn rfl
  | cons a s =>
    have haa : a.setChecker .idle=a := by rw [←hi a (by simp),Cell.setChecker_self]
    have st := step_context (checker_create_step c a t x hc ht
      (hp a (by simp)) (hw.format (by simp)) (hw.format (by simp))) [] (s++[z])
    obtain ⟨v,l,u,r,hr,he,hzero⟩ := checker_seek_missing c [] a s z x hz
      (fun b hb => hw.format (by
        simp only [List.mem_cons] at hb
        simp only [List.mem_cons,List.mem_append]
        tauto)) hp (hn a (by simp))
      (fun b hb => hi b (by simp [hb])) (fun b hb => hn b (by simp [hb]))
    apply hw l u r _ hzero
    rw [←he]
    apply Relation.ReflTransGen.head _ hr
    simpa only [List.nil_append,List.cons_append,haa] using st

theorem Survives.palette_all_colors {c z : Cell q} {w : List (Cell q)} {t : Fin q}
    (hw : Survives S d (c::w++[z])) (hc : c.pos=.core t) (ht : t.val+1=q)
    (hz : z.pos=.stop) (hwn : w≠[]) (hp : ∀ a∈w, a.isPalette) :
    ∀ x, x∈w.map Cell.color := by
  have hr := hw.checker_rollback hc ht hz hp
  have hw' := hw.of_reach hr
  have hn : checkerIdle w≠[] := by simpa [checkerIdle] using hwn
  have hp' : ∀ a∈checkerIdle w, a.isPalette := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hp b hb
  have hi : ∀ a∈checkerIdle w, a.checker=.idle := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    rfl
  have hh := hw'.idle_palette_all_colors hc ht hz hn hp' hi
  simpa [checkerIdle,List.map_map,Function.comp_def] using hh

namespace Cell
lemma palette_idle_canonical (c : Cell q) (bits : Fin d → ZMod 2) (hc : c.Format S d)
    (hp : c.isPalette) (hm : c.marker=.idle) (hi : c.checker=.idle) :
    c=canonicalCell bits (.palette c.color) := by
  obtain ⟨x,hx⟩ := hp
  have hc' := hc.2.2.2.1 (by simp [isCore,hx])
  have hm' := hc.2.2.2.2.1 hm
  have hmeta := hm'.1
  have hhead := hm'.2.1
  have hd := hc'.1
  have hz := hc'.2
  have hsk : c.skeleton=⟨.palette x,.idle,defaultMeta⟩ := by
    cases c with
    | mk sk ch dat cert head => cases sk; simp_all [marker,pos,metadata]
  cases c with
  | mk sk ch dat cert head =>
    dsimp only [Cell.checker] at hi
    simp_all [canonicalCell,color,pos]
    rfl
end Cell

lemma canonical_palette_swap (bits : Fin d → ZMod 2) (a b : Fin q) :
    Replacement S d [canonicalCell bits (.palette a),canonicalCell bits (.palette b)]
      [canonicalCell bits (.palette b),canonicalCell bits (.palette a)] := by
  apply replacement_swap_of_same_fields
  · exact ⟨a,rfl⟩
  · exact ⟨b,rfl⟩
  · exact canonicalCell_format bits _
  · exact canonicalCell_format bits _
  · rfl
  · simp [Cell.HeadFree,canonicalCell,Skeleton.IsHead]
  · simp [Cell.HeadFree,canonicalCell,Skeleton.IsHead]

def canonicalPalette (bits : Fin d → ZMod 2) (w : List (Fin q)) : List (Cell q) :=
  w.map (fun x => canonicalCell bits (.palette x))

lemma canonicalPalette_perm (bits : Fin d → ZMod 2) {v w : List (Fin q)} (h : v.Perm w) :
    Reach S d (canonicalPalette bits v) (canonicalPalette bits w) := by
  induction h with
  | nil => exact .refl
  | cons a h ih =>
    simpa only [canonicalPalette,List.map_cons,List.singleton_append,List.append_nil] using
      reach_context ih [canonicalCell bits (.palette a)] []
  | swap a b w =>
    exact .single ⟨[],canonicalPalette bits w,
      [canonicalCell bits (.palette b),canonicalCell bits (.palette a)],
      [canonicalCell bits (.palette a),canonicalCell bits (.palette b)],rfl,rfl,
      canonical_palette_swap bits b a⟩
  | trans _ _ ih ih' => exact ih.trans ih'

theorem Survives.idle_palette_normalize {c z : Cell q} {w : List (Cell q)} {t : Fin q}
    (hw : Survives S d (c::w++[z])) (hc : c.pos=.core t) (ht : t.val+1=q)
    (hz : z.pos=.stop) (hwn : w≠[]) (hp : ∀ a∈w, a.isPalette)
    (hm : ∀ a∈w, a.marker=.idle) (hi : ∀ a∈w, a.checker=.idle)
    (bits : Fin d → ZMod 2) :
    w.length=q ∧ Reach S d w (canonicalPalette bits (List.finRange q)) := by
  have hv : Survives S d w := hw.infix ⟨[c],[z],rfl⟩
  have he : w=canonicalPalette bits (w.map Cell.color) := by
    unfold canonicalPalette
    rw [List.map_map]
    calc
      w = w.map id := (List.map_id w).symm
      _ = _ := List.map_congr_left (fun a ha =>
        a.palette_idle_canonical bits (hv.format ha) (hp a ha) (hm a ha) (hi a ha))
  have hfields : ∀ a∈w,∀ b∈w,a.eraseColor=b.eraseColor := by
    intro a ha b hb
    rw [a.palette_idle_canonical bits (hv.format ha) (hp a ha) (hm a ha) (hi a ha),
      b.palette_idle_canonical bits (hv.format hb) (hp b hb) (hm b hb) (hi b hb)]
    rfl
  have hnd := eligible_run_distinct hv hp hfields
  have hall := hw.idle_palette_all_colors hc ht hz hwn hp hi
  have hperm : (w.map Cell.color).Perm (List.finRange q) :=
    (List.perm_ext_iff_of_nodup hnd (List.nodup_finRange q)).mpr (by simp [hall])
  have hlen := hperm.length_eq
  refine ⟨by simpa using hlen,?_⟩
  rw [he]
  exact canonicalPalette_perm bits hperm
end SourceBurnside.FiniteTable

end

end OAI
