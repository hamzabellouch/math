import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.TableEncoding

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

namespace Cell
@[simp] lemma read_wing (a : Address q) (c : Cell q) (m : Marker) : (c.wing m).read a = c.read a := rfl
@[simp] lemma read_boundary (a : Address q) (c : Cell q) (s : Bool) : (c.boundary s).read a = c.read a := rfl
omit [NeZero q] in
@[simp] lemma read_full (a : Address q) (c : Cell q) (s : Bool) (j : Fin q) (p : Phase) (r : Reg) :
    (c.full s j p r).read a = c.read a := rfl
omit [NeZero q] in
@[simp] lemma read_setChecker (a : Address q) (c : Cell q) (ch : Palette.Check (Fin q)) :
    (c.setChecker ch).read a = c.read a := rfl
omit [NeZero q] in
lemma read_palette (a : Address q) (c : Cell q) (h : c.isPalette) : c.read a = 0 := by
  obtain ⟨x,hx⟩ := h
  cases a <;> simp [read,hx]
omit [NeZero q] in
@[simp] lemma read_setColor (a : Address q) (c : Cell q) (x : Fin q) : (c.setColor x).read a = 0 := by
  apply read_palette
  exact ⟨x,rfl⟩

def LockedReads (a b : Cell q) : Prop :=
  a.marker ≠ .idle → b.marker ≠ .idle → ∀ x : Address q, a.read x = b.read x
omit [NeZero q] in
lemma lockedReads_refl (a : Cell q) : a.LockedReads a := by intro _ _ x; rfl
omit [NeZero q] in
lemma LockedReads.symm {a b : Cell q} (h : a.LockedReads b) : b.LockedReads a := by
  intro hb ha x; exact (h ha hb x).symm
end Cell

lemma Unary.lockedReads {a b : Cell q} (h : Unary S a b) : a.LockedReads b := by
  cases h <;> intro ha hb x <;> simp only [Cell.read_full,Cell.read_boundary]
  case create c s h => exact (ha rfl).elim

lemma Binary.lockedReads {a b a' b' : Cell q} (h : Binary S a b a' b') :
    a.LockedReads a' ∧ b.LockedReads b' := by
  cases h with
  | acquire a b s hp =>
    constructor
    · intro ha hb x; rfl
    · intro ha hb x; exact (ha rfl).elim
  | swap a b x y ha hb he hf hf' =>
    constructor <;> intro _ _ z
    · rw [Cell.read_palette z a ⟨x,ha⟩,Cell.read_palette z b ⟨y,hb⟩]
    · rw [Cell.read_palette z a ⟨x,ha⟩,Cell.read_palette z b ⟨y,hb⟩]
  | read_left a b s j r hp => constructor <;> intro _ _ x <;> rfl
  | read_right a b s j r hp => constructor <;> intro _ _ x <;> rfl
  | undo_left a b s j r hp => constructor <;> intro _ _ x <;> rfl
  | undo_right a b s j r hp => constructor <;> intro _ _ x <;> rfl
  | checker_create a b p x ha hp hb => constructor <;> intro _ _ x <;> rfl
  | checker_advance a b v x ha hb hv => constructor <;> intro _ _ x <;> rfl

lemma replacement_lockedReads {v w : List (Cell q)} (h : Replacement S d v w) :
    List.Forall₂ Cell.LockedReads v w := by
  rcases h.2 with ⟨a,b,rfl,rfl,he⟩ | ⟨a,b,a',b',rfl,rfl,he⟩
  · have hh : a.LockedReads b := he.elim Unary.lockedReads (fun h => h.lockedReads.symm)
    exact .cons hh .nil
  · have hh : a.LockedReads a' ∧ b.LockedReads b' := he.elim Binary.lockedReads
      (fun h => ⟨h.lockedReads.1.symm,h.lockedReads.2.symm⟩)
    exact .cons hh.1 (.cons hh.2 .nil)

lemma step_lockedReads {v w : List (Cell q)} (h : Step S d v w) :
    List.Forall₂ Cell.LockedReads v w := by
  obtain ⟨p,s,a,b,rfl,rfl,hh⟩ := h
  have hr (l : List (Cell q)) : List.Forall₂ Cell.LockedReads l l := by
    induction l with
    | nil => exact .nil
    | cons a l ih => exact .cons (Cell.lockedReads_refl a) ih
  have happ {a b c e : List (Cell q)} (hab : List.Forall₂ Cell.LockedReads a b)
      (hce : List.Forall₂ Cell.LockedReads c e) : List.Forall₂ Cell.LockedReads (a++c) (b++e) := by
    induction hab with
    | nil => exact hce
    | cons h _ ih => exact .cons h ih
  exact happ (happ (hr p) (replacement_lockedReads hh)) (hr s)

def Cell.PayloadFormat (d : ℕ) (c : Cell q) : Prop :=
  (¬ c.isPalette → c.checker = .idle) ∧
  (∀ p, c.pos = .core p → d ≤ p.val → c.data = 0) ∧
  (¬ c.isCore → c.data = 0 ∧ c.certificate = 0)

structure Region (q d : ℕ) where
  size : ℕ
  positive : 0 < size
  task : Task
  cell : Fin size → Cell q
  task_eq : ∀ i, (cell i).metadata.task = task
  first_iff : ∀ i, (cell i).skeleton.first ↔ i.val = 0
  last_iff : ∀ i, (cell i).skeleton.last ↔ i.val + 1 = size
  adjacent : ∀ i j, i.val + 1 = j.val →
    Skeleton.Structural (cell i).skeleton (cell j).skeleton ∧
      Skeleton.Internal (cell i).skeleton (cell j).skeleton
  payload_format : ∀ i, (cell i).PayloadFormat d

namespace Region
variable (R : Region q d) (S : Schedule q)
def first : Fin R.size := ⟨0,R.positive⟩
def last : Fin R.size := ⟨R.size-1,by have := R.positive; omega⟩

omit [NeZero q] in
lemma first_first : (R.cell R.first).skeleton.first := (R.first_iff _).mpr rfl
omit [NeZero q] in
lemma last_last : (R.cell R.last).skeleton.last := by
  apply (R.last_iff _).mpr
  have := R.positive
  dsimp [last]; omega

def clauseIndex (j : Fin (S.count R.task).val) : Fin q :=
  ⟨j.val,lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ (S.count R.task).isLt)⟩

def plan : HeadTour.Plan (S.count R.task).val R.size where
  nonempty := S.positive R.task
  zeroTask := R.task.zeroTask
  payload j :=
    { nonempty := R.positive
      delta := fun i => (R.cell i).delta (S.clause R.task (R.clauseIndex S j))
      gate := fun r => (S.clause R.task (R.clauseIndex S j)).truth r = true
      last_zero := Cell.delta_stop _ _ R.last_last.2 }

def controlPosition : HeadTour.Control R.size → Fin R.size
  | .readLeft p | .readRight p | .undoLeft p | .undoRight p => p
  | _ => R.last

def controlPhase : HeadTour.Control R.size → Phase
  | .acquisition => .acquisition
  | .readLeft _ => .readLeft
  | .readRight _ => .readRight
  | .beforeGate => .beforeGate
  | .afterGate => .afterGate
  | .undoLeft _ => .undoLeft
  | .undoRight _ => .undoRight
  | .finish => .finish

def position (s : HeadTour.FullState (S.count R.task).val R.size) : Fin R.size :=
  match s.ctrl with
  | .clause _ c => R.controlPosition c
  | .success => R.last

def phase (s : HeadTour.FullState (S.count R.task).val R.size) : Phase :=
  match s.ctrl with
  | .clause _ c => R.controlPhase c
  | .success => .success

def clause (s : HeadTour.FullState (S.count R.task).val R.size) : Fin q :=
  match s.ctrl with
  | .clause j _ => R.clauseIndex S j
  | .success => 0

def realizeCell (s : HeadTour.FullState (S.count R.task).val R.size) (i : Fin R.size) : Cell q :=
  if i.val < (R.position S s).val then (R.cell i).wing .left
  else if (R.position S s).val < i.val then (R.cell i).wing .right
  else (R.cell i).full s.side (R.clause S s) (R.phase S s) s.reg

def realize (s : HeadTour.FullState (S.count R.task).val R.size) : List (Cell q) :=
  List.ofFn (R.realizeCell S s)

lemma realize_head (s : HeadTour.FullState (S.count R.task).val R.size) :
    R.realizeCell S s (R.position S s) =
      (R.cell (R.position S s)).full s.side (R.clause S s) (R.phase S s) s.reg := by
  simp [realizeCell]

lemma realizeCell_read (s : HeadTour.FullState (S.count R.task).val R.size)
    (i : Fin R.size) (a : Address q) : (R.realizeCell S s i).read a = (R.cell i).read a := by
  unfold realizeCell
  split
  · simp
  · split <;> simp

lemma realizeCell_payload (s : HeadTour.FullState (S.count R.task).val R.size)
    (i : Fin R.size) : (R.realizeCell S s i).PayloadFormat d := by
  have h := R.payload_format i
  unfold realizeCell
  split
  · exact h
  · split <;> exact h

omit [NeZero q] in
lemma endpoint_position (s : HeadTour.FullState (S.count R.task).val R.size)
    (h : Cell.endpoint (R.phase S s)) : R.position S s = R.last := by
  cases hs : s.ctrl with
  | success => simp [position,hs]
  | clause j c =>
    cases c <;> simp_all [Cell.endpoint,phase,controlPhase,position,controlPosition]

lemma realizeCell_format (s : HeadTour.FullState (S.count R.task).val R.size)
    (hs : R.task.zeroTask=true → s.side=false) (i : Fin R.size) :
    (R.realizeCell S s i).Format S d := by
  have hbase := R.payload_format i
  have htask := R.task_eq i
  have ht : (R.cell i).metadata.zeroTask=R.task.zeroTask := congrArg Task.zeroTask htask
  unfold realizeCell
  split
  · rename_i hi
    simp only [Cell.Format,Cell.wing,Cell.marker,Cell.metadata,Skeleton.mark,Cell.pos,
      Skeleton.Admissible,Skeleton.IsHead,Cell.isPalette,Cell.isCore]
    dsimp [Cell.PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hbase
    refine ⟨?_,hbase.1,hbase.2.1,hbase.2.2,?_⟩ <;> simp
    intro hlast
    have hlast' := (R.last_iff i).mp hlast
    have := (R.position S s).isLt
    omega
  · rename_i hi
    split
    · rename_i hi'
      simp only [Cell.Format,Cell.wing,Cell.marker,Cell.metadata,Skeleton.mark,Cell.pos,
        Skeleton.Admissible,Skeleton.IsHead,Cell.isPalette,Cell.isCore]
      dsimp [Cell.PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hbase
      refine ⟨?_,hbase.1,hbase.2.1,hbase.2.2,?_⟩ <;> simp
      intro hfirst
      have hfirst' := (R.first_iff i).mp hfirst
      omega
    · rename_i hi'
      have he : i=R.position S s := Fin.ext (by omega)
      subst i
      simp only [Cell.Format,Cell.full,Cell.marker,Cell.metadata,Skeleton.mark,Cell.pos,
        Skeleton.Admissible,Skeleton.IsHead,Cell.isPalette,Cell.isCore]
      dsimp [Cell.PayloadFormat,Cell.isPalette,Cell.isCore,Cell.pos] at hbase
      refine ⟨?_,hbase.1,hbase.2.1,hbase.2.2,?_⟩ <;> simp
      refine ⟨?_,?_,?_,?_⟩
      · rw [←ht] at hs
        exact hs
      · intro he
        cases hc : s.ctrl with
        | success => simp [clause,hc]
        | clause j c => cases c <;> simp [phase,hc,controlPhase] at he
      · intro hn
        cases hc : s.ctrl with
        | success => exact (hn (by simp [phase,hc])).elim
        | clause j c =>
          change (R.clause S s).val < (S.count (R.cell (R.position S s)).metadata.task).val
          rw [htask]
          simpa only [clause,hc,clauseIndex] using j.isLt
      · intro hep
        have hey := R.endpoint_position S s hep
        change (R.cell (R.position S s)).skeleton.last
        rw [hey]
        exact R.last_last
end Region

section LocalEdits
variable {N : ℕ} {α : Type*}
lemma ofFn_take_congr (f g : Fin N → α) (i : ℕ)
    (h : ∀ j, j.val < i → f j = g j) : (List.ofFn f).take i = (List.ofFn g).take i := by
  apply List.ext_getElem (by simp)
  intro j hj hk
  simp only [List.getElem_take,List.getElem_ofFn]
  apply h
  simp only [List.length_take,List.length_ofFn] at hj
  change j < i
  omega

lemma ofFn_drop_congr (f g : Fin N → α) (i : ℕ)
    (h : ∀ j, i ≤ j.val → f j = g j) : (List.ofFn f).drop i = (List.ofFn g).drop i := by
  apply List.ext_getElem (by simp)
  intro j hj hk
  simp only [List.getElem_drop,List.getElem_ofFn]
  apply h
  change i ≤ i+j
  omega

lemma ofFn_split_one (f : Fin N → α) (i : Fin N) :
    List.ofFn f = (List.ofFn f).take i.val ++ [f i] ++ (List.ofFn f).drop (i.val+1) := by
  conv_lhs => rw [←List.take_append_drop i.val (List.ofFn f)]
  rw [List.drop_eq_getElem_cons (by simp)]
  simp

lemma ofFn_split_two (f : Fin N → α) (i j : Fin N) (hij : i.val+1=j.val) :
    List.ofFn f = (List.ofFn f).take i.val ++ [f i,f j] ++ (List.ofFn f).drop (j.val+1) := by
  have ht : (List.ofFn f).drop (i.val+1) = f j :: (List.ofFn f).drop (j.val+1) := by
    rw [hij,List.drop_eq_getElem_cons (by simp)]
    simp
  conv_lhs => rw [ofFn_split_one f i]
  rw [ht]
  simp

lemma step_one_ofFn (f g : Fin N → Cell q) (i : Fin N)
    (hf : ∀ j, j ≠ i → f j = g j) (hr : Replacement S d [f i] [g i]) :
    Step S d (List.ofFn f) (List.ofFn g) := by
  refine ⟨(List.ofFn f).take i.val,(List.ofFn f).drop (i.val+1),[f i],[g i],
    ofFn_split_one f i,?_,hr⟩
  have hp := ofFn_take_congr f g i.val (fun j hj => hf j (by intro he; subst j; omega))
  have hs := ofFn_drop_congr f g (i.val+1) (fun j hj => hf j (by intro he; subst j; omega))
  rw [hp,hs]
  exact ofFn_split_one g i

lemma step_two_ofFn (f g : Fin N → Cell q) (i j : Fin N) (hij : i.val+1=j.val)
    (hf : ∀ k, k ≠ i → k ≠ j → f k = g k)
    (hr : Replacement S d [f i,f j] [g i,g j]) :
    Step S d (List.ofFn f) (List.ofFn g) := by
  refine ⟨(List.ofFn f).take i.val,(List.ofFn f).drop (j.val+1),[f i,f j],[g i,g j],
    ofFn_split_two f i j hij,?_,hr⟩
  have hp := ofFn_take_congr f g i.val (fun k hk => hf k
    (by intro he; subst k; omega) (by intro he; subst k; omega))
  have hs := ofFn_drop_congr f g (j.val+1) (fun k hk => hf k
    (by intro he; subst k; omega) (by intro he; subst k; omega))
  rw [hp,hs]
  exact ofFn_split_two g i j hij
end LocalEdits

namespace Region
variable (R : Region q d) (S : Schedule q)

def SideOK (s : HeadTour.FullState (S.count R.task).val R.size) : Prop :=
  R.task.zeroTask=true → s.side=false

omit [NeZero q] in
lemma edge_side {s t : HeadTour.FullState (S.count R.task).val R.size}
    (h : (R.plan S).Edge s t) : R.SideOK S s ↔ R.SideOK S t := by
  cases h with
  | tour j h => cases h <;> rfl
  | next i j h b => rfl
  | done b => rfl
  | flip b h =>
    change R.task.zeroTask=false at h
    simp [SideOK,h]

omit [NeZero q] in
lemma adjacent_pair (i j : Fin R.size) (hij : i.val+1=j.val) :
    Skeleton.Pair ((R.cell i).skeleton.mark .full) ((R.cell j).skeleton.mark .right) := by
  obtain ⟨hstr,hi⟩ := R.adjacent i j hij
  refine ⟨hstr,Or.inr ?_⟩
  simp only [Skeleton.rightExternal,Skeleton.leftExternal,Skeleton.mark_marker,
    Skeleton.mark_last,Skeleton.mark_first,Skeleton.acceptsRight,Skeleton.acceptsLeft,
    Skeleton.internal_mark_left,Skeleton.internal_mark_right]
  simpa using And.intro hi.2.2.2.2 hi

lemma realizeCell_eq_off_head (s t : HeadTour.FullState (S.count R.task).val R.size)
    (hp : R.position S s = R.position S t) (i : Fin R.size) (hi : i ≠ R.position S s) :
    R.realizeCell S s i = R.realizeCell S t i := by
  simp only [realizeCell,←hp]
  split
  · rfl
  · rename_i h1
    split
    · rfl
    · rename_i h2
      exact (hi (Fin.ext (by omega))).elim

lemma step_unary {s t : HeadTour.FullState (S.count R.task).val R.size}
    (hs : R.SideOK S s) (ht : R.SideOK S t) (hp : R.position S s=R.position S t)
    (he : Unary S
      ((R.cell (R.position S s)).full s.side (R.clause S s) (R.phase S s) s.reg)
      ((R.cell (R.position S t)).full t.side (R.clause S t) (R.phase S t) t.reg)) :
    Step S d (R.realize S s) (R.realize S t) := by
  apply step_one_ofFn (R.realizeCell S s) (R.realizeCell S t) (R.position S s)
  · exact fun i hi => R.realizeCell_eq_off_head S s t hp i hi
  · refine ⟨?_,Or.inl ⟨_,_,rfl,rfl,Or.inl ?_⟩⟩
    · intro c hc
      simp only [List.singleton_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl
      · exact R.realizeCell_format S s hs _
      · exact R.realizeCell_format S t ht _
    · rw [R.realize_head, hp,R.realize_head]
      simpa only [hp] using he

lemma realizeCell_eq_off_adjacent (s t : HeadTour.FullState (S.count R.task).val R.size)
    (i j : Fin R.size) (hij : i.val+1=j.val)
    (hs : R.position S s=i ∨ R.position S s=j)
    (ht : R.position S t=i ∨ R.position S t=j)
    (k : Fin R.size) (hki : k≠i) (hkj : k≠j) :
    R.realizeCell S s k = R.realizeCell S t k := by
  have hne : k.val≠i.val := Fin.val_ne_of_ne hki
  have hne' : k.val≠j.val := Fin.val_ne_of_ne hkj
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    simp only [realizeCell,hs,ht]
  all_goals by_cases hk : k.val < i.val
  all_goals first
    | simp [hk,show k.val < j.val by omega]
    | simp [hk,show ¬k.val < j.val by omega,show i.val < k.val by omega,show j.val < k.val by omega]

lemma step_adjacent {s t : HeadTour.FullState (S.count R.task).val R.size}
    (hs : R.SideOK S s) (ht : R.SideOK S t)
    (i j : Fin R.size) (hij : i.val+1=j.val)
    (hps : R.position S s=i ∨ R.position S s=j)
    (hpt : R.position S t=i ∨ R.position S t=j)
    (he : Binary S (R.realizeCell S s i) (R.realizeCell S s j)
      (R.realizeCell S t i) (R.realizeCell S t j)) :
    Step S d (R.realize S s) (R.realize S t) := by
  apply step_two_ofFn (R.realizeCell S s) (R.realizeCell S t) i j hij
  · exact R.realizeCell_eq_off_adjacent S s t i j hij hps hpt
  · refine ⟨?_,Or.inr ⟨_,_,_,_,rfl,rfl,Or.inl he⟩⟩
    intro c hc
    simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact R.realizeCell_format S s hs _
    · exact R.realizeCell_format S s hs _
    · exact R.realizeCell_format S t ht _
    · exact R.realizeCell_format S t ht _

omit [NeZero q] in
@[simp] lemma payload_first (j : Fin (S.count R.task).val) :
    ((R.plan S).payload j).first=R.first := rfl
omit [NeZero q] in
@[simp] lemma payload_last (j : Fin (S.count R.task).val) :
    ((R.plan S).payload j).last=R.last := rfl

lemma tour_realize_step (j : Fin (S.count R.task).val) {s t : HeadTour.State R.size}
    (he : ((R.plan S).payload j).Edge s t)
    (hs : R.SideOK S (HeadTour.atClause j s)) :
    Step S d (R.realize S (HeadTour.atClause j s))
      (R.realize S (HeadTour.atClause j t)) := by
  have ht := (R.edge_side S (.tour j he)).mp hs
  cases he with
  | enter r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.read_enter (R.cell R.last) b (R.clauseIndex S j) r R.last_last
  | read_turn r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.read_turn (R.cell R.first) b (R.clauseIndex S j) r R.first_first
  | read_exit r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.read_exit (R.cell R.last) b (R.clauseIndex S j) r R.last_last
  | gate r b hg =>
    apply R.step_unary S hs ht rfl
    have hg' : (S.clause (R.cell R.last).metadata.task (R.clauseIndex S j)).truth r = true := by
      rw [R.task_eq]
      exact hg
    exact Unary.gate (R.cell R.last) b (R.clauseIndex S j) r R.last_last hg'
  | undo_enter r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.undo_enter (R.cell R.last) b (R.clauseIndex S j) r R.last_last
  | undo_turn r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.undo_turn (R.cell R.first) b (R.clauseIndex S j) r R.first_first
  | undo_exit r b =>
    apply R.step_unary S hs ht rfl
    exact Unary.undo_exit (R.cell R.last) b (R.clauseIndex S j) r R.last_last
  | read_left p z hp r b =>
    apply R.step_adjacent S hs ht z p hp (Or.inr rfl) (Or.inl rfl)
    have hz : z.val < p.val := by omega
    simpa [realizeCell,position,phase,clause,controlPosition,controlPhase,HeadTour.atClause,
      hz,not_lt_of_gt hz,plan,R.task_eq] using
      Binary.read_left (R.cell z) (R.cell p) b (R.clauseIndex S j) r (R.adjacent_pair z p hp)
  | read_right p z hp r b =>
    apply R.step_adjacent S hs ht p z hp (Or.inl rfl) (Or.inr rfl)
    have hz : p.val < z.val := by omega
    simpa [realizeCell,position,phase,clause,controlPosition,controlPhase,HeadTour.atClause,
      hz,not_lt_of_gt hz] using
      Binary.read_right (R.cell p) (R.cell z) b (R.clauseIndex S j) r (R.adjacent_pair p z hp)
  | undo_left p z hp r b =>
    apply R.step_adjacent S hs ht z p hp (Or.inr rfl) (Or.inl rfl)
    have hz : z.val < p.val := by omega
    simpa [realizeCell,position,phase,clause,controlPosition,controlPhase,HeadTour.atClause,
      hz,not_lt_of_gt hz] using
      Binary.undo_left (R.cell z) (R.cell p) b (R.clauseIndex S j) r (R.adjacent_pair z p hp)
  | undo_right p z hp r b =>
    apply R.step_adjacent S hs ht p z hp (Or.inl rfl) (Or.inr rfl)
    have hz : p.val < z.val := by omega
    simpa [realizeCell,position,phase,clause,controlPosition,controlPhase,HeadTour.atClause,
      hz,not_lt_of_gt hz,plan,R.task_eq] using
      Binary.undo_right (R.cell p) (R.cell z) b (R.clauseIndex S j) r (R.adjacent_pair p z hp)

lemma edge_realize_step {s t : HeadTour.FullState (S.count R.task).val R.size}
    (he : (R.plan S).Edge s t) (hs : R.SideOK S s) :
    Step S d (R.realize S s) (R.realize S t) := by
  have ht := (R.edge_side S he).mp hs
  cases he with
  | tour j h => exact R.tour_realize_step S j h hs
  | next i j hij b =>
    apply R.step_unary S hs ht rfl
    exact Unary.next (R.cell R.last) b (R.clauseIndex S i) (R.clauseIndex S j) hij R.last_last
  | done b =>
    apply R.step_unary S hs ht rfl
    apply Unary.success _ _ _ _ R.last_last
    change (R.clauseIndex S (R.plan S).last).val+1=(S.count (R.cell R.last).metadata.task).val
    rw [R.task_eq]
    have hc := S.positive R.task
    dsimp [clauseIndex,HeadTour.Plan.last]
    omega
  | flip b hz =>
    apply R.step_unary S hs ht rfl
    apply Unary.pivot _ _ R.last_last
    have he : (R.cell R.last).metadata.zeroTask=R.task.zeroTask := congrArg Task.zeroTask (R.task_eq R.last)
    rw [he]
    exact hz

omit [NeZero q] in
lemma reach_side {s t : HeadTour.FullState (S.count R.task).val R.size}
    (h : (R.plan S).Reach s t) (hs : R.SideOK S s) : R.SideOK S t := by
  induction h with
  | refl => exact hs
  | tail h e ih =>
    exact e.elim (fun e => (R.edge_side S e).mp ih)
      (fun e => (R.edge_side S e).mpr ih)

lemma realize_reach {s t : HeadTour.FullState (S.count R.task).val R.size}
    (h : (R.plan S).Reach s t) (hs : R.SideOK S s) :
    Reach S d (R.realize S s) (R.realize S t) := by
  induction h with
  | refl => exact .refl
  | tail h e ih =>
    have hm := R.reach_side S h hs
    apply ih.tail
    rcases e with e | e
    · exact R.edge_realize_step S e hm
    · exact step_symm (R.edge_realize_step S e ((R.edge_side S e).mpr hm))

lemma realize_semanticZero (s : HeadTour.FullState (S.count R.task).val R.size)
    (hz : (R.plan S).SemanticZero s) :
    SemanticZero S (R.realizeCell S s (R.position S s)) := by
  rw [R.realize_head]
  refine ⟨rfl,?_⟩
  rcases hz with hz | ⟨hc,hz⟩
  · cases hc : s.ctrl with
    | success =>
      simp only [HeadTour.Plan.Bad,hc] at hz
      exact Or.inl ⟨Or.inr (Or.inr (by simp [phase,hc,Cell.full])),hz⟩
    | clause j c =>
      simp only [HeadTour.Plan.Bad,hc,HeadTour.Payload.SemanticZero] at hz
      rcases hz with ⟨hc',hr⟩ | ⟨rfl,hg⟩
      · left
        constructor
        · rcases hc' with rfl | rfl
          · exact Or.inl (by simp [phase,hc,controlPhase,Cell.full])
          · exact Or.inr (Or.inl (by simp [phase,hc,controlPhase,Cell.full]))
        · exact hr
      · right; left
        refine ⟨by simp [phase,hc,controlPhase,Cell.full],?_⟩
        simp only [Cell.full,clause,hc]
        change (S.clause (R.cell (R.position S s)).metadata.task (R.clauseIndex S j)).truth s.reg=false
        rw [R.task_eq]
        exact Bool.eq_false_of_not_eq_true hg
  · right; right
    refine ⟨by simp [phase,hc,Cell.full],?_⟩
    change (R.cell (R.position S s)).metadata.zeroTask=true
    have he := congrArg Task.zeroTask (R.task_eq (R.position S s))
    exact he.trans hz

theorem literal_rollback (s : HeadTour.FullState (S.count R.task).val R.size)
    (hs : R.SideOK S s) :
    Reach S d (R.realize S s)
      (R.realize S (HeadTour.atClause (R.plan S).first ⟨.acquisition,0,s.side⟩)) ∨
    ∃ w p a z, Reach S d (R.realize S s) w ∧ w=p++[a]++z ∧ Zero S d [a] := by
  rcases (R.plan S).rollback s with h | ⟨t,h,hz⟩
  · exact Or.inl (R.realize_reach S h hs)
  · right
    refine ⟨R.realize S t,(R.realize S t).take (R.position S t).val,
      R.realizeCell S t (R.position S t),(R.realize S t).drop ((R.position S t).val+1),
      R.realize_reach S h hs,ofFn_split_one _ _,?_⟩
    exact Or.inl ⟨_,rfl,Or.inr (Or.inl (R.realize_semanticZero S t (Or.inl hz)))⟩

theorem literal_success (b : Bool) (hb : R.task.zeroTask=true → b=false)
    (hc : ∀ j, (R.plan S).Holds j) :
    Reach S d (R.realize S (HeadTour.atClause (R.plan S).first ⟨.acquisition,0,b⟩))
      (R.realize S ⟨.success,0,b⟩) :=
  R.realize_reach S (((R.plan S).success_iff b).mpr hc) hb
end Region

end SourceBurnside.FiniteTable

end

end OAI
