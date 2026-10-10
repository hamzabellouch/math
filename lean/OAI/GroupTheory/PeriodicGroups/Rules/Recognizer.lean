import Mathlib
import OAI.GroupTheory.PeriodicGroups.Rules.TableEncoding

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable.Recognizer
open LocalSyntax Skeleton
variable {q : ℕ} [NeZero q]

private def firstTest (c : Skeleton q 10) : Prop :=
  c.metadata.block.val=0 ∧ match c.pos with
  | .core p => p.val=0
  | _ => False
private lemma firstTest_iff (c : Skeleton q 10) : firstTest c ↔ c.first := by
  cases hp : c.pos <;> simp [firstTest,Skeleton.first,hp]
instance decideFirst (c : Skeleton q 10) : Decidable c.first := by
  haveI : Decidable (firstTest c) := by unfold firstTest; cases c.pos <;> infer_instance
  exact decidable_of_iff (firstTest c) (firstTest_iff c)
instance decideLast (c : Skeleton q 10) : Decidable c.last :=
  inferInstanceAs (Decidable (c.metadata.block.val=c.metadata.arity.val ∧ c.pos=.stop))
instance decideAdmissible (c : Skeleton q 10) : Decidable c.Admissible :=
  inferInstanceAs (Decidable ((c.marker=.right → ¬c.first) ∧ (c.marker=.left → ¬c.last)))
instance decideLeftExternal (c : Skeleton q 10) : Decidable c.leftExternal :=
  inferInstanceAs (Decidable (c.marker=.idle ∨ (c.marker≠.right ∧ c.first)))
instance decideRightExternal (c : Skeleton q 10) : Decidable c.rightExternal :=
  inferInstanceAs (Decidable (c.marker=.idle ∨ c.marker=.boundary ∨ (c.marker≠.left ∧ c.last)))
instance decideAcceptsLeft (c : Skeleton q 10) (m : Marker) : Decidable (c.acceptsLeft m) := by
  unfold acceptsLeft
  infer_instance
instance decideAcceptsRight (c : Skeleton q 10) (m : Marker) : Decidable (c.acceptsRight m) := by
  unfold acceptsRight
  infer_instance
instance decideStructural (a b : Skeleton q 10) : Decidable (Structural a b) := by
  unfold Structural
  cases a.pos <;> cases b.pos <;> infer_instance
instance decideInternal (a b : Skeleton q 10) : Decidable (Internal a b) := by
  unfold Internal
  infer_instance
instance decidePair (a b : Skeleton q 10) : Decidable (Skeleton.Pair a b) := by
  unfold Skeleton.Pair
  infer_instance

private def paletteTest (c : Cell q) : Prop := match c.pos with
  | .palette _ => True
  | _ => False
private def coreTest (c : Cell q) : Prop := match c.pos with
  | .core _ => True
  | _ => False
private lemma paletteTest_iff (c : Cell q) : paletteTest c ↔ c.isPalette := by
  cases hp : c.pos <;> simp [paletteTest,Cell.isPalette,hp]
private lemma coreTest_iff (c : Cell q) : coreTest c ↔ c.isCore := by
  cases hp : c.pos <;> simp [coreTest,Cell.isCore,hp]
instance decidePalette (c : Cell q) : Decidable c.isPalette := by
  haveI : Decidable (paletteTest c) := by unfold paletteTest; cases c.pos <;> infer_instance
  exact decidable_of_iff (paletteTest c) (paletteTest_iff c)
instance decideCore (c : Cell q) : Decidable c.isCore := by
  haveI : Decidable (coreTest c) := by unfold coreTest; cases c.pos <;> infer_instance
  exact decidable_of_iff (coreTest c) (coreTest_iff c)
instance decideHead (c : Skeleton q 10) : Decidable (IsHead c) := by
  unfold IsHead
  infer_instance
instance decideEndpoint (p : Phase) : Decidable (Cell.endpoint p) := by
  unfold Cell.endpoint
  infer_instance

private def dataTest (d : ℕ) (c : Cell q) : Prop := match c.pos with
  | .core p => d≤p.val → c.data=0
  | _ => True
omit [NeZero q] in
private lemma dataTest_iff (d : ℕ) (c : Cell q) : dataTest d c ↔
    ∀ p, c.pos=.core p → d≤p.val → c.data=0 := by
  cases hp : c.pos <;> simp [dataTest,hp]
instance decideDataTest (d : ℕ) (c : Cell q) :
    Decidable (∀ p, c.pos=.core p → d≤p.val → c.data=0) := by
  haveI : Decidable (dataTest d c) := by unfold dataTest; cases c.pos <;> infer_instance
  exact decidable_of_iff (dataTest d c) (dataTest_iff d c)
instance decideFormat (S : Schedule q) (d : ℕ) (c : Cell q) : Decidable (c.Format S d) := by
  unfold Cell.Format
  infer_instance

def UnaryTest (S : Schedule q) (a b : Cell q) : Prop :=
  (b.skeleton.first ∧ a=b.idle b.head.side ∧ b=b.boundary b.head.side) ∨
  (b.skeleton.last ∧ a=b.boundary b.head.side ∧ b=b.full b.head.side 0 .acquisition 0) ∨
  (b.skeleton.last ∧ a=b.full b.head.side b.head.clause .acquisition b.head.reg ∧
    b=b.full b.head.side b.head.clause .readLeft b.head.reg) ∨
  (b.skeleton.first ∧ a=b.full b.head.side b.head.clause .readLeft b.head.reg ∧
    b=b.full b.head.side b.head.clause .readRight b.head.reg) ∨
  (b.skeleton.last ∧ a=b.full b.head.side b.head.clause .readRight b.head.reg ∧
    b=b.full b.head.side b.head.clause .beforeGate b.head.reg) ∨
  (b.skeleton.last ∧ a=b.full b.head.side b.head.clause .beforeGate b.head.reg ∧
    b=b.full b.head.side b.head.clause .afterGate b.head.reg ∧
    (S.clause b.metadata.task b.head.clause).truth b.head.reg=true) ∨
  (b.skeleton.last ∧ a=b.full b.head.side b.head.clause .afterGate b.head.reg ∧
    b=b.full b.head.side b.head.clause .undoLeft b.head.reg) ∨
  (b.skeleton.first ∧ a=b.full b.head.side b.head.clause .undoLeft b.head.reg ∧
    b=b.full b.head.side b.head.clause .undoRight b.head.reg) ∨
  (b.skeleton.last ∧ a=b.full b.head.side b.head.clause .undoRight b.head.reg ∧
    b=b.full b.head.side b.head.clause .finish b.head.reg) ∨
  (b.skeleton.last ∧ a=b.full b.head.side a.head.clause .finish 0 ∧
    b=b.full b.head.side b.head.clause .acquisition 0 ∧ a.head.clause.val+1=b.head.clause.val) ∨
  (b.skeleton.last ∧ a=b.full b.head.side a.head.clause .finish 0 ∧
    b=b.full b.head.side 0 .success 0 ∧ a.head.clause.val+1=(S.count b.metadata.task).val) ∨
  (b.skeleton.last ∧ a=b.full (!b.head.side) 0 .success 0 ∧
    b=b.full b.head.side 0 .success 0 ∧ b.metadata.zeroTask=false)

instance decideUnaryTest (S : Schedule q) (a b : Cell q) : Decidable (UnaryTest S a b) := by
  unfold UnaryTest
  infer_instance

lemma unary_test {S : Schedule q} {a b : Cell q} (h : Unary S a b) : UnaryTest S a b := by
  cases h <;> simp_all [UnaryTest,Cell.idle,Cell.boundary,Cell.full,Skeleton.mark,
    Skeleton.first,Skeleton.last,Cell.pos,Cell.metadata]

lemma unary_of_test {S : Schedule q} {a b : Cell q} (h : UnaryTest S a b) : Unary S a b := by
  rcases h with ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ |
    ⟨hl,ha,hb,hg⟩ | ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ | ⟨hl,ha,hb⟩ |
    ⟨hl,ha,hb,hj⟩ | ⟨hl,ha,hb,hj⟩ | ⟨hl,ha,hb,ht⟩
  · simpa only [← ha,← hb] using Unary.create (S:=S) b b.head.side hl
  · simpa only [← ha,← hb] using Unary.finish_acquisition (S:=S) b b.head.side hl
  · simpa only [← ha,← hb] using Unary.read_enter (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.read_turn (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.read_exit (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.gate (S:=S) b b.head.side b.head.clause b.head.reg hl hg
  · simpa only [← ha,← hb] using Unary.undo_enter (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.undo_turn (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.undo_exit (S:=S) b b.head.side b.head.clause b.head.reg hl
  · simpa only [← ha,← hb] using Unary.next (S:=S) b b.head.side a.head.clause b.head.clause hj hl
  · simpa only [← ha,← hb] using Unary.success (S:=S) b b.head.side a.head.clause hj hl
  · have hh := Unary.pivot (S:=S) b (!b.head.side) hl ht
    simpa only [Bool.not_not,← ha,← hb] using hh

instance decideUnary (S : Schedule q) (a b : Cell q) : Decidable (Unary S a b) :=
  decidable_of_iff (UnaryTest S a b) ⟨unary_of_test,unary_test⟩

private def headfreeTest (c : Cell q) : Prop :=
  ¬IsHead c.skeleton ∧ match c.checker with
  | .head _ => False
  | _ => True
omit [NeZero q] in
private lemma headfreeTest_iff (c : Cell q) : headfreeTest c ↔ c.HeadFree := by
  cases hc : c.checker <;> simp [headfreeTest,Cell.HeadFree,hc]
instance decideHeadFree (c : Cell q) : Decidable c.HeadFree := by
  haveI : Decidable (headfreeTest c) := by unfold headfreeTest; cases c.checker <;> infer_instance
  exact decidable_of_iff (headfreeTest c) (headfreeTest_iff c)

def AcquireTest (a b a' b' : Cell q) : Prop :=
  Skeleton.Pair (a.skeleton.mark .left) (b'.skeleton.mark .boundary) ∧
  a=a.boundary a.head.side ∧ b=b'.idle a.head.side ∧
  a'=a.wing .left ∧ b'=b'.boundary a.head.side

def ReadLeftTest (S : Schedule q) (a b a' b' : Cell q) : Prop :=
  Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right) ∧
  a=a.wing .left ∧ b=b.full b.head.side b.head.clause .readLeft b.head.reg ∧
  a'=a.full b.head.side b.head.clause .readLeft (b.head.reg+a.delta (S.clause a.metadata.task b.head.clause)) ∧
  b'=b.wing .right

def ReadRightTest (a b a' b' : Cell q) : Prop :=
  Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right) ∧
  a=a.full a.head.side a.head.clause .readRight a.head.reg ∧ b=b.wing .right ∧
  a'=a.wing .left ∧ b'=b.full a.head.side a.head.clause .readRight a.head.reg

def UndoLeftTest (a b a' b' : Cell q) : Prop :=
  Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right) ∧
  a=a.wing .left ∧ b=b.full b.head.side b.head.clause .undoLeft b.head.reg ∧
  a'=a.full b.head.side b.head.clause .undoLeft b.head.reg ∧ b'=b.wing .right

def UndoRightTest (S : Schedule q) (a b a' b' : Cell q) : Prop :=
  Skeleton.Pair (a.skeleton.mark .full) (b.skeleton.mark .right) ∧
  a=a.full a.head.side a.head.clause .undoRight a.head.reg ∧ b=b.wing .right ∧
  a'=a.wing .left ∧
  b'=b.full a.head.side a.head.clause .undoRight (a.head.reg+a.delta (S.clause a.metadata.task a.head.clause))

def CheckerCreateTest (a b a' b' : Cell q) : Prop :=
  a'=a ∧ b=b'.setChecker .idle ∧ match a.pos,b'.pos,b'.checker with
  | .core p,.palette _,.head _ => p.val+1=q
  | _,_,_ => False

def CheckerAdvanceTest (a b a' b' : Cell q) : Prop := match a.pos,b.pos,a.checker with
  | .palette v,.palette _,.head x => v≠x ∧ b.checker=.idle ∧
      a'=a.setChecker (.passed x) ∧ b'=b.setChecker (.head x)
  | _,_,_ => False

def SwapTest (a b a' b' : Cell q) : Prop := match a.pos,b.pos with
  | .palette _,.palette y => a'=b ∧ b'=a ∧ a.setColor y=b ∧ a.HeadFree ∧ b.HeadFree
  | _,_ => False

def BinaryTest (S : Schedule q) (a b a' b' : Cell q) : Prop :=
  AcquireTest a b a' b' ∨ ReadLeftTest S a b a' b' ∨ ReadRightTest a b a' b' ∨
  UndoLeftTest a b a' b' ∨ UndoRightTest S a b a' b' ∨ CheckerCreateTest a b a' b' ∨
  CheckerAdvanceTest a b a' b' ∨ SwapTest a b a' b'

instance decideAcquireTest (a b a' b' : Cell q) : Decidable (AcquireTest a b a' b') := by
  unfold AcquireTest; infer_instance
instance decideReadLeftTest (S : Schedule q) (a b a' b' : Cell q) : Decidable (ReadLeftTest S a b a' b') := by
  unfold ReadLeftTest; infer_instance
instance decideReadRightTest (a b a' b' : Cell q) : Decidable (ReadRightTest a b a' b') := by
  unfold ReadRightTest; infer_instance
instance decideUndoLeftTest (a b a' b' : Cell q) : Decidable (UndoLeftTest a b a' b') := by
  unfold UndoLeftTest; infer_instance
instance decideUndoRightTest (S : Schedule q) (a b a' b' : Cell q) : Decidable (UndoRightTest S a b a' b') := by
  unfold UndoRightTest; infer_instance
instance decideCheckerCreateTest (a b a' b' : Cell q) : Decidable (CheckerCreateTest a b a' b') := by
  unfold CheckerCreateTest; cases a.pos <;> cases b'.pos <;> cases b'.checker <;> infer_instance
instance decideCheckerAdvanceTest (a b a' b' : Cell q) : Decidable (CheckerAdvanceTest a b a' b') := by
  unfold CheckerAdvanceTest; cases a.pos <;> cases b.pos <;> cases a.checker <;> infer_instance
instance decideSwapTest (a b a' b' : Cell q) : Decidable (SwapTest a b a' b') := by
  unfold SwapTest; cases a.pos <;> cases b.pos <;> infer_instance
instance decideBinaryTest (S : Schedule q) (a b a' b' : Cell q) : Decidable (BinaryTest S a b a' b') := by
  unfold BinaryTest; infer_instance

lemma checkerCreateTest_iff (a b a' b' : Cell q) : CheckerCreateTest a b a' b' ↔
    ∃ p x, a.pos=.core p ∧ p.val+1=q ∧ b'.isPalette ∧ b'.checker=.head x ∧
      a'=a ∧ b=b'.setChecker .idle := by
  cases ha : a.pos <;> cases hb : b'.pos <;> cases hx : b'.checker <;>
    simp [CheckerCreateTest,Cell.isPalette,ha,hb,hx,and_comm,and_left_comm]
lemma checkerAdvanceTest_iff (a b a' b' : Cell q) : CheckerAdvanceTest a b a' b' ↔
    ∃ v x, a.pos=.palette v ∧ b.isPalette ∧ a.checker=.head x ∧ v≠x ∧ b.checker=.idle ∧
      a'=a.setChecker (.passed x) ∧ b'=b.setChecker (.head x) := by
  cases ha : a.pos <;> cases hb : b.pos <;> cases hx : a.checker <;>
    simp [CheckerAdvanceTest,Cell.isPalette,ha,hb,hx]
lemma swapTest_iff (a b a' b' : Cell q) : SwapTest a b a' b' ↔
    ∃ x y, a.pos=.palette x ∧ b.pos=.palette y ∧
      a'=b ∧ b'=a ∧ a.setColor y=b ∧ a.HeadFree ∧ b.HeadFree := by
  cases ha : a.pos <;> cases hb : b.pos <;> simp [SwapTest,ha,hb]

lemma binary_test {S : Schedule q} {a b a' b' : Cell q} (h : Binary S a b a' b') :
    BinaryTest S a b a' b' := by
  cases h with
  | acquire a b s hp =>
    apply Or.inl
    exact ⟨hp,rfl,rfl,rfl,rfl⟩
  | read_left a b s j r hp =>
    apply Or.inr ∘ Or.inl
    exact ⟨hp,rfl,rfl,rfl,rfl⟩
  | read_right a b s j r hp =>
    apply Or.inr ∘ Or.inr ∘ Or.inl
    exact ⟨hp,rfl,rfl,rfl,rfl⟩
  | undo_left a b s j r hp =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    exact ⟨hp,rfl,rfl,rfl,rfl⟩
  | undo_right a b s j r hp =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    exact ⟨hp,rfl,rfl,rfl,rfl⟩
  | checker_create a b p x ha hp hb =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    apply (checkerCreateTest_iff ..).mpr
    exact ⟨p,x,ha,hp,hb,rfl,rfl,rfl⟩
  | checker_advance a b v x ha hb hv =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    apply (checkerAdvanceTest_iff ..).mpr
    exact ⟨v,x,ha,hb,rfl,hv,rfl,rfl,rfl⟩
  | swap a b x y ha hb he hf hf' =>
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    exact (swapTest_iff ..).mpr ⟨x,y,ha,hb,rfl,rfl,he,hf,hf'⟩

lemma binary_of_test {S : Schedule q} {a b a' b' : Cell q} (h : BinaryTest S a b a' b') :
    Binary S a b a' b' := by
  rcases h with h | h | h | h | h | h | h | h
  · rcases h with ⟨hp,ha,hb,ha',hb'⟩
    simpa only [← ha,← hb,← ha',← hb'] using Binary.acquire (S:=S) a b' a.head.side hp
  · rcases h with ⟨hp,ha,hb,ha',hb'⟩
    simpa only [← ha,← hb,← ha',← hb'] using Binary.read_left (S:=S) a b b.head.side b.head.clause b.head.reg hp
  · rcases h with ⟨hp,ha,hb,ha',hb'⟩
    simpa only [← ha,← hb,← ha',← hb'] using Binary.read_right (S:=S) a b a.head.side a.head.clause a.head.reg hp
  · rcases h with ⟨hp,ha,hb,ha',hb'⟩
    simpa only [← ha,← hb,← ha',← hb'] using Binary.undo_left (S:=S) a b b.head.side b.head.clause b.head.reg hp
  · rcases h with ⟨hp,ha,hb,ha',hb'⟩
    simpa only [← ha,← hb,← ha',← hb'] using Binary.undo_right (S:=S) a b a.head.side a.head.clause a.head.reg hp
  · obtain ⟨p,x,hp,hq,hpal,hch,ha',hb⟩ := (checkerCreateTest_iff ..).mp h
    have hv := Binary.checker_create (S:=S) a b' p x hp hq hpal
    have he : b'.setChecker (.head x)=b' := by cases b'; simp_all [Cell.setChecker]
    simpa only [← hb,he,← ha'] using hv
  · obtain ⟨v,x,hp,hpal,hch,hne,hidle,ha',hb'⟩ := (checkerAdvanceTest_iff ..).mp h
    have hv := Binary.checker_advance (S:=S) a b v x hp hpal hne
    have he : a.setChecker (.head x)=a := by cases a; simp_all [Cell.setChecker]
    have he' : b.setChecker .idle=b := by cases b; simp_all [Cell.setChecker]
    simpa only [he,he',← ha',← hb'] using hv
  · obtain ⟨x,y,hp,hq,ha',hb',he,hf,hf'⟩ := (swapTest_iff ..).mp h
    simpa only [← ha',← hb'] using Binary.swap (S:=S) a b x y hp hq he hf hf'

instance decideBinary (S : Schedule q) (a b a' b' : Cell q) : Decidable (Binary S a b a' b') :=
  decidable_of_iff (BinaryTest S a b a' b') ⟨binary_of_test,binary_test⟩

private def palettePairTest (a b : Palette.Check (Fin q)) : Prop :=
  match a,b with
  | .idle,.idle => True
  | .passed x,.passed y => x=y
  | .passed x,.head y => x=y
  | .head _,.idle => True
  | _,_ => False
omit [NeZero q] in
private lemma palettePairTest_iff (a b : Palette.Check (Fin q)) :
    palettePairTest a b ↔ Palette.Pair a b := by
  constructor
  · cases a <;> cases b <;> simp only [palettePairTest] <;> intro h
    all_goals first | contradiction | subst_vars
    all_goals constructor
  · intro h
    cases h <;> simp [palettePairTest]
instance decidePalettePair (a b : Palette.Check (Fin q)) : Decidable (Palette.Pair a b) := by
  haveI : Decidable (palettePairTest a b) := by
    unfold palettePairTest
    cases a <;> cases b <;> infer_instance
  exact decidable_of_iff (palettePairTest a b) (palettePairTest_iff a b)
instance decideLastOK (a : Palette.Check (Fin q)) : Decidable (Palette.LastOK a) := by
  cases a <;> unfold Palette.LastOK <;> infer_instance
instance decideCheckerPair (a b : Cell q) : Decidable (CheckerPair a b) := by
  unfold CheckerPair
  infer_instance
instance decideCellPair (a b : Cell q) : Decidable (Pair a b) := by
  unfold Pair
  infer_instance
instance decideSemanticZero (S : Schedule q) (c : Cell q) : Decidable (SemanticZero S c) := by
  unfold SemanticZero
  infer_instance

private def passedOwnColorTest (c : Cell q) : Prop := match c.pos,c.checker with
  | .palette x,.passed y => x=y
  | _,_ => False
private lemma passedOwnColorTest_iff (c : Cell q) : passedOwnColorTest c ↔
    ∃ x, c.pos=.palette x ∧ c.checker=.passed x := by
  cases hp : c.pos <;> cases hc : c.checker <;> simp [passedOwnColorTest,hp,hc,eq_comm]
instance decidePassedOwnColor (c : Cell q) :
    Decidable (∃ x, c.pos=.palette x ∧ c.checker=.passed x) := by
  haveI : Decidable (passedOwnColorTest c) := by
    unfold passedOwnColorTest
    cases c.pos <;> cases c.checker <;> infer_instance
  exact decidable_of_iff (passedOwnColorTest c) (passedOwnColorTest_iff c)
instance decideUnaryZero (S : Schedule q) (d : ℕ) (c : Cell q) : Decidable (UnaryZero S d c) := by
  unfold UnaryZero
  infer_instance

private def duplicateColorTest (a b : Cell q) : Prop := match a.pos,b.pos with
  | .palette x,.palette y => x=y
  | _,_ => False
private lemma duplicateColorTest_iff (a b : Cell q) : duplicateColorTest a b ↔
    ∃ x, a.pos=.palette x ∧ b.pos=.palette x := by
  cases hp : a.pos <;> cases hq : b.pos <;> simp [duplicateColorTest,hp,hq,eq_comm]
instance decideDuplicateColor (a b : Cell q) :
    Decidable (∃ x, a.pos=.palette x ∧ b.pos=.palette x) := by
  haveI : Decidable (duplicateColorTest a b) := by
    unfold duplicateColorTest
    cases a.pos <;> cases b.pos <;> infer_instance
  exact decidable_of_iff (duplicateColorTest a b) (duplicateColorTest_iff a b)

private def missingColorTest (a b : Cell q) : Prop := match a.pos,a.checker with
  | .palette x,.head y => b.pos=.stop ∧ x≠y
  | _,_ => False
private lemma missingColorTest_iff (a b : Cell q) : missingColorTest a b ↔
    ∃ x y, a.pos=.palette x ∧ a.checker=.head y ∧ b.pos=.stop ∧ x≠y := by
  cases hp : a.pos <;> cases hc : a.checker <;> simp [missingColorTest,hp,hc]
instance decideMissingColor (a b : Cell q) :
    Decidable (∃ x y, a.pos=.palette x ∧ a.checker=.head y ∧ b.pos=.stop ∧ x≠y) := by
  haveI : Decidable (missingColorTest a b) := by
    unfold missingColorTest
    cases a.pos <;> cases a.checker <;> infer_instance
  exact decidable_of_iff (missingColorTest a b) (missingColorTest_iff a b)
instance decideBinaryZero (a b : Cell q) : Decidable (BinaryZero a b) := by
  unfold BinaryZero
  infer_instance

def ReplacementTest (S : Schedule q) (d : ℕ) (v w : List (Cell q)) : Prop :=
  match v,w with
  | [a],[b] => a.Format S d ∧ b.Format S d ∧ (Unary S a b ∨ Unary S b a)
  | [a,b],[a',b'] => a.Format S d ∧ b.Format S d ∧ a'.Format S d ∧ b'.Format S d ∧
      (Binary S a b a' b' ∨ Binary S a' b' a b)
  | _,_ => False

lemma replacementTest_iff (S : Schedule q) (d : ℕ) (v w : List (Cell q)) :
    ReplacementTest S d v w ↔ Replacement S d v w := by
  rcases v with _|⟨a,_|⟨b,_|⟨c,v⟩⟩⟩ <;>
    rcases w with _|⟨x,_|⟨y,_|⟨z,w⟩⟩⟩ <;>
    simp [ReplacementTest,Replacement,and_assoc]
instance decideReplacement (S : Schedule q) (d : ℕ) (v w : List (Cell q)) :
    Decidable (Replacement S d v w) := by
  haveI : Decidable (ReplacementTest S d v w) := by
    unfold ReplacementTest
    split <;> infer_instance
  exact decidable_of_iff (ReplacementTest S d v w) (replacementTest_iff S d v w)

def ZeroTest (S : Schedule q) (d : ℕ) (v : List (Cell q)) : Prop :=
  match v with
  | [a] => UnaryZero S d a
  | [a,b] => BinaryZero a b
  | _ => False
lemma zeroTest_iff (S : Schedule q) (d : ℕ) (v : List (Cell q)) :
    ZeroTest S d v ↔ Zero S d v := by
  match v with
  | [] => simp [ZeroTest,Zero]
  | [a] => simp [ZeroTest,Zero]
  | [a,b] => simp [ZeroTest,Zero]
  | a::b::c::v => simp [ZeroTest,Zero]
instance decideZero (S : Schedule q) (d : ℕ) (v : List (Cell q)) :
    Decidable (Zero S d v) := by
  haveI : Decidable (ZeroTest S d v) := by
    unfold ZeroTest
    split <;> infer_instance
  exact decidable_of_iff (ZeroTest S d v) (zeroTest_iff S d v)

end SourceBurnside.FiniteTable.Recognizer

namespace SourceBurnside.FiniteTable.Codec
section
open Recognizer
instance decideRawUnaryZero {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (a : Raw h) :
    Decidable (unaryZero hh S d a) := by
  unfold unaryZero
  split <;> infer_instance
instance decideRawBinaryZero {h : ℕ} (hh : 0<h) (a b : Raw h) :
    Decidable (binaryZero hh a b) := by
  unfold binaryZero
  split <;> infer_instance
instance decideRawReplacement {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ)
    (v w : List (Raw h)) : Decidable (replacement hh S d v w) := by
  unfold replacement
  split <;> infer_instance
instance decideRawZero {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (v : List (Raw h)) :
    Decidable (zero hh S d v) := by
  unfold zero
  split <;> infer_instance

def entry {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ)
    (z : Bool) (v w : List (Raw h)) : Bool :=
  if z then decide (w=[] ∧ zero hh S d v) else decide (replacement hh S d v w)
lemma entry_zero {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (v w : List (Raw h)) :
    entry hh S d true v w=true ↔ w=[] ∧ zero hh S d v := by simp [entry]
lemma entry_replacement {h : ℕ} (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (v w : List (Raw h)) :
    entry hh S d false v w=true ↔ replacement hh S d v w := by simp [entry]

end

section

def binaryValue (bs : List Bool) : ℕ := (BitVec.ofBoolListLE bs).toNat
@[simp] lemma binaryValue_bit (bs : List Bool) (i : ℕ) : (binaryValue bs).testBit i=bs.getD i false := by
  change (BitVec.ofBoolListLE bs).getLsbD i=_
  exact BitVec.getLsbD_ofBoolListLE
lemma binaryValue_lt (bs : List Bool) : binaryValue bs<2^bs.length := (BitVec.ofBoolListLE bs).isLt

def natCode {h : ℕ} (w : Raw h) : ℕ := binaryValue (List.ofFn w)
lemma natCode_lt {h : ℕ} (w : Raw h) : natCode w<2^(10000*h) := by simpa [natCode] using binaryValue_lt (List.ofFn w)
lemma natCode_bit {h : ℕ} (w : Raw h) (i : Fin (10000*h)) : (natCode w).testBit i.val=w i := by
  simp [natCode,i.isLt]
lemma natCode_injective {h : ℕ} : Function.Injective (@natCode h) := by
  intro a b h
  funext i
  rw [←natCode_bit a i,←natCode_bit b i,h]

lemma readInt_arithmetic {h : ℕ} (hh : 0<h) (w : Raw h) (s : Fin 32) :
    readInt hh w s=(natCode w/2^(s.val*(2*h)))%2^(2*h) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (binaryValue (List.ofFn (fun j => w (intPosition hh s j)))).testBit i=_
  rw [binaryValue_bit,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases hi : i<2*h
  · have hj : i+s.val*(2*h)<10000*h := by
      have hs : s.val≤31 := by omega
      have ht := Nat.mul_le_mul_right (2*h) hs
      omega
    have hb := natCode_bit w ⟨i+s.val*(2*h),hj⟩
    simp only [List.getD_eq_getElem, List.length_ofFn, hi,List.getElem_ofFn,
      decide_true,Bool.true_and]
    rw [hb]
    congr 1
    apply Fin.ext
    simp [intPosition,Nat.add_comm]
  · simp [hi]

lemma readFlag_arithmetic {h : ℕ} (hh : 0<h) (w : Raw h) (s : Fin 512) :
    readFlag hh w s=decide ((natCode w/2^(64*h+s.val))%2=1) := by
  rw [←Nat.testBit_eq_decide_div_mod_eq]
  exact (natCode_bit w (flagPosition hh s)).symm

lemma flag_as_nat {h : ℕ} (hh : 0<h) (w : Raw h) (s : Fin 512) :
    (if readFlag hh w s then 1 else 0)=(natCode w/2^(64*h+s.val))%2 := by
  rw [readFlag_arithmetic]
  have H := Nat.mod_lt (natCode w/2^(64*h+s.val)) (by omega : 0<2)
  split_ifs <;> simp_all


open LocalSyntax

lemma getFin_eq_some_iff {n i : ℕ} {j : Fin n} : getFin n i=some j ↔ i=j.val := by
  unfold getFin
  split
  · simp only [Option.some.injEq]
    constructor
    · intro h;exact congrArg Fin.val h
    · intro h;apply Fin.ext;exact h
  · simp only [reduceCtorEq, false_iff]
    have := j.isLt
    omega

lemma getPosition_eq_some_iff {q t i : ℕ} {p : Position q} :
    getPosition q t i=some p ↔ t=positionTag p ∧ i=positionIndex p := by
  cases p <;> (fun_cases getPosition q t i <;>
    simp_all [getFin_eq_some_iff,positionTag,positionIndex])

lemma getMarker_eq_some_iff {t : ℕ} {m : Marker} : getMarker t=some m ↔ t=markerTag m := by
  cases m <;> (fun_cases getMarker t <;> simp_all [markerTag])

lemma getChecker_eq_some_iff {q t i : ℕ} {c : Palette.Check (Fin q)} :
    getChecker q t i=some c ↔ t=checkerTag c ∧ i=checkerIndex c := by
  cases c <;> (fun_cases getChecker q t i <;>
    simp_all [getFin_eq_some_iff,checkerTag,checkerIndex])

lemma getPhase_eq_some_iff {t : ℕ} {p : Phase} : getPhase t=some p ↔ t=phaseTag p := by
  cases p <;> (fun_cases getPhase t <;> simp_all [phaseTag])

lemma getFin_isSome {n i : ℕ} : (getFin n i).isSome=true ↔ i<n := by simp [getFin]
lemma getPosition_isSome {q t i : ℕ} (hq : 0<q) :
    (getPosition q t i).isSome=true ↔ t<3 ∧ i<q ∧ (t=2 → i=0) := by
  fun_cases getPosition q t i <;> simp_all [getFin]
  omega
lemma getMarker_isSome {t : ℕ} : (getMarker t).isSome=true ↔ t<5 := by
  fun_cases getMarker t <;> simp_all
  omega
lemma getChecker_isSome {q t i : ℕ} (hq : 0<q) :
    (getChecker q t i).isSome=true ↔ t<3 ∧ i<q ∧ (t=0 → i=0) := by
  fun_cases getChecker q t i <;> simp_all [getFin]
  omega
lemma getPhase_isSome {t : ℕ} : (getPhase t).isSome=true ↔ t<9 := by
  fun_cases getPhase t <;> simp_all
  omega

def UsedAgree {h : ℕ} (hh : 0<h) (w : Raw h) (c : Cell (2^h)) : Prop :=
  (∀s : Fin 32,s.val<9 → integers c s=readInt hh w s) ∧
  (∀s : Fin 512,s.val<8 → flags c s=readFlag hh w s)

lemma parse_used {h : ℕ} (hh : 0<h) {w : Raw h} {c : Cell (2^h)}
    (hc : parse hh w=some c) : UsedAgree hh w c := by
  simp only [parse,bind,pure,Option.bind_eq_some_iff] at hc
  rcases hc with ⟨p,hp,m,hm,a,ha,b,hb,k,hk,z,hz,f,hf,hc⟩
  simp only [getPosition_eq_some_iff,getMarker_eq_some_iff,getFin_eq_some_iff,
    getChecker_eq_some_iff,getPhase_eq_some_iff] at hp hm ha hb hk hz hf
  cases Option.some.inj hc
  constructor
  · intro s hs
    rcases s with ⟨s,hsl⟩
    change s<9 at hs
    interval_cases s <;>
      simp_all [integers,Cell.pos,Cell.marker,Cell.metadata]

  · intro s hs
    rcases s with ⟨s,hsl⟩
    change s<8 at hs
    interval_cases s <;> simp [flags,Cell.metadata]

def InRange (q : ℕ) (v : Fin 32 → ℕ) : Prop :=
  (v 0<3 ∧ v 1<q ∧ (v 0=2 → v 1=0)) ∧ v 2<5 ∧
  v 3<10 ∧ v 4≤v 3 ∧ (v 5<3 ∧ v 6<q ∧ (v 5=0 → v 6=0)) ∧
  v 7<q ∧ v 8<9

lemma integers_inRange {q : ℕ} (hq : 0<q) (c : Cell q) : InRange q (integers c) := by
  have hp := (@getPosition_isSome q (positionTag c.pos) (positionIndex c.pos) hq).mp
    (by rw [getPosition_encode];rfl)
  have hk := (@getChecker_isSome q (checkerTag c.checker) (checkerIndex c.checker) hq).mp
    (by rw [getChecker_encode];rfl)
  refine ⟨hp,markerTag_lt c.marker,c.metadata.arity.isLt,?_,hk,c.head.clause.isLt,phaseTag_lt c.head.phase⟩
  change c.metadata.block.val≤c.metadata.arity.val
  have := c.metadata.block.isLt
  omega

lemma parse_isSome {h : ℕ} (hh : 0<h) (w : Raw h) :
    (parse hh w).isSome=true ↔ InRange (2^h) (readInt hh w) := by
  constructor
  · intro ha
    rcases Option.isSome_iff_exists.mp ha with ⟨c,hc⟩
    have H := (parse_used hh hc).1
    have H0 := integers_inRange (by positivity : 0<2^h) c
    simpa only [InRange,H 0 (by decide),H 1 (by decide),H 2 (by decide),H 3 (by decide),
      H 4 (by decide),H 5 (by decide),H 6 (by decide),H 7 (by decide),H 8 (by decide)] using H0
  · rintro ⟨hp,hm,ha,hb,hk,hz,hf⟩
    rcases Option.isSome_iff_exists.mp ((getPosition_isSome (by positivity : 0<2^h)).mpr hp) with ⟨p,hp⟩
    rcases Option.isSome_iff_exists.mp (getMarker_isSome.mpr hm) with ⟨m,hm⟩
    let a : Fin 10 := ⟨readInt hh w 3,ha⟩
    let b : Fin (a.val+1) := ⟨readInt hh w 4,by dsimp [a];omega⟩
    rcases Option.isSome_iff_exists.mp ((getChecker_isSome (by positivity : 0<2^h)).mpr hk) with ⟨k,hk⟩
    let z : Fin (2^h) := ⟨readInt hh w 7,hz⟩
    rcases Option.isSome_iff_exists.mp (getPhase_isSome.mpr hf) with ⟨f,hf⟩
    have ha' : getFin 10 (readInt hh w 3)=some a := getFin_eq_some_iff.mpr rfl
    have hb' : getFin (a.val+1) (readInt hh w 4)=some b := getFin_eq_some_iff.mpr rfl
    have hz' : getFin (2^h) (readInt hh w 7)=some z := getFin_eq_some_iff.mpr rfl
    simp [parse,hp,hm,ha',hb',hk,hz',hf]

lemma integers_unused {q : ℕ} (c : Cell q) (s : Fin 32) (hs : 9 ≤ s.val) : integers c s=0 := by
  unfold integers
  split <;> omega
lemma flags_unused {q : ℕ} (c : Cell q) (s : Fin 512) (hs : 8 ≤ s.val) : flags c s=false := by
  unfold flags
  split <;> first | omega | rfl

def usedWrite {h : ℕ} (hh : 0<h) (w : Raw h) : Raw h :=
  write (fun s => if s.val<9 then readInt hh w s else 0)
    (fun s => if s.val<8 then readFlag hh w s else false)

lemma usedWrite_of_parse {h : ℕ} (hh : 0<h) {w : Raw h} {c : Cell (2^h)}
    (hc : parse hh w=some c) : usedWrite hh w=encode c := by
  have H := parse_used hh hc
  unfold usedWrite encode
  congr 1
  · funext s
    by_cases hs : s.val<9
    · simpa [hs] using (H.1 s hs).symm
    · simp [hs,integers_unused c s (by omega)]
  · funext s
    by_cases hs : s.val<8
    · simpa [hs] using (H.2 s hs).symm
    · simp [hs,flags_unused c s (by omega)]

lemma decode_isSome_by_fields {h : ℕ} (hh : 0<h) (w : Raw h) :
    (decode hh w).isSome=true ↔ InRange (2^h) (readInt hh w) ∧ w=usedWrite hh w := by
  cases hc : parse hh w with
  | none =>
    have hr : ¬InRange (2^h) (readInt hh w) := by rw [←parse_isSome hh w,hc];simp
    simp [decode,hc,hr]
  | some c =>
    have hr : InRange (2^h) (readInt hh w) := (parse_isSome hh w).mp (by rw [hc];rfl)
    simp [decode,hc,hr,usedWrite_of_parse hh hc]

end

open LocalSyntax

lemma readInt_bit {h : ℕ} (hh : 0<h) (w : Raw h) (s : Fin 32) (i : Fin (2*h)) :
    (readInt hh w s).testBit i.val=w (intPosition hh s i) := by
  rw [readInt_arithmetic,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  simp only [i.isLt,decide_true,Bool.true_and]
  have H := natCode_bit w (intPosition hh s i)
  simpa [intPosition,Nat.add_comm] using H

def ReservedZero {h : ℕ} (w : Raw h) : Prop := ∀i : Fin (10000*h),
  (18*h ≤ i.val ∧ i.val<64*h ∨ 64*h+8 ≤ i.val) → w i=false

lemma usedWrite_reserved {h : ℕ} (hh : 0<h) (w : Raw h) : ReservedZero (usedWrite hh w) := by
  intro i hi
  unfold usedWrite write
  split
  · rename_i ht
    have hs : ¬i.val/(2*h)<9 := by
      have h18 : 18*h ≤ i.val := by omega
      have hd : 9 ≤ i.val/(2*h) := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      omega
    simp [hs]
  · split
    · rename_i ht
      have hf : ¬i.val-64*h<8 := by omega
      simp [hf]
    · rfl

lemma usedWrite_eq_of_reserved {h : ℕ} (hh : 0<h) (w : Raw h) (hw : ReservedZero w) :
    usedWrite hh w=w := by
  funext i
  unfold usedWrite write
  split
  · rename_i hi
    let s : Fin 32 := ⟨i.val/(2*h),(Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
    let j : Fin (2*h) := ⟨i.val%(2*h),Nat.mod_lt _ (by omega)⟩
    have hpos : intPosition hh s j=i := by
      apply Fin.ext
      change i.val/(2*h)*(2*h)+i.val%(2*h)=i.val
      simpa [Nat.mul_comm] using Nat.div_add_mod i.val (2*h)
    change (if s.val<9 then readInt hh w s else 0).testBit j.val=w i
    split
    · rw [readInt_bit hh w s j,hpos]
    · rename_i hs
      have h18 : 18*h ≤ i.val := by
        have H := (Nat.le_div_iff_mul_le (by omega : 0<2*h)).mp (show 9 ≤ i.val/(2*h) by exact Nat.le_of_not_gt hs)
        omega
      simp [hw i (Or.inl ⟨h18,hi⟩)]
  · rename_i hi
    split
    · rename_i hf
      dsimp only
      split
      · change readFlag hh w ⟨i.val-64*h,by omega⟩=w i
        unfold readFlag
        congr 1
        apply Fin.ext
        simp [flagPosition]
        omega
      · have hn : 64*h+8 ≤ i.val := by omega
        exact (hw i (Or.inr hn)).symm
    · have hn : 64*h+8 ≤ i.val := by omega
      exact (hw i (Or.inr hn)).symm

lemma canonical_iff_reserved {h : ℕ} (hh : 0<h) (w : Raw h) : w=usedWrite hh w ↔ ReservedZero w := by
  constructor
  · intro hw
    rw [hw]
    exact usedWrite_reserved hh w
  · exact fun H => (usedWrite_eq_of_reserved hh w H).symm

lemma zero_window (n offset width : ℕ) :
    (n/2^offset)%2^width=0 ↔ ∀i,width>i → n.testBit (i+offset)=false := by
  constructor
  · intro h i hi
    have H := congrArg (fun n : ℕ => n.testBit i) h
    simpa [Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow,hi] using H
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
    by_cases hi : i<width
    · simp [hi,h i hi]
    · simp [hi]

lemma zero_high (n offset : ℕ) : n/2^offset=0 ↔ ∀i,n.testBit (i+offset)=false := by
  constructor
  · intro h i
    have H := congrArg (fun n : ℕ => n.testBit i) h
    simpa [Nat.testBit_div_two_pow] using H
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simpa [Nat.testBit_div_two_pow] using h i

lemma reserved_arithmetic {h : ℕ} (_hh : 0<h) (w : Raw h) : ReservedZero w ↔
    (natCode w/2^(18*h))%2^(46*h)=0 ∧ natCode w/2^(64*h+8)=0 := by
  rw [zero_window,zero_high]
  constructor
  · intro H
    constructor
    · intro i hi
      have hp : i+18*h<10000*h := by omega
      rw [natCode_bit w ⟨i+18*h,hp⟩]
      exact H _ (Or.inl (by simp;omega))
    · intro i
      by_cases hi : i+(64*h+8)<10000*h
      · rw [natCode_bit w ⟨i+(64*h+8),hi⟩]
        exact H _ (Or.inr (by simp))
      · apply Nat.testBit_lt_two_pow
        exact (natCode_lt w).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  · rintro ⟨H,J⟩ i (hi|hi)
    · have he : i.val-18*h+18*h=i.val := by omega
      have hj : i.val-18*h<46*h := by omega
      have hx := H (i.val-18*h) hj
      rw [he,natCode_bit] at hx
      exact hx
    · have he : i.val-(64*h+8)+(64*h+8)=i.val := by omega
      have hx := J (i.val-(64*h+8))
      rw [he,natCode_bit] at hx
      exact hx

lemma decode_isSome_arithmetic {h : ℕ} (hh : 0<h) (w : Raw h) :
    (decode hh w).isSome=true ↔
      InRange (2^h) (fun s : Fin 32 => (natCode w/2^(s.val*(2*h)))%2^(2*h)) ∧
      ((natCode w/2^(18*h))%2^(46*h)=0 ∧ natCode w/2^(64*h+8)=0) := by
  rw [decode_isSome_by_fields,canonical_iff_reserved,reserved_arithmetic hh]
  have he : readInt hh w=(fun s : Fin 32 => (natCode w/2^(s.val*(2*h)))%2^(2*h)) := funext (readInt_arithmetic hh w)
  rw [he]

end SourceBurnside.FiniteTable.Codec

end OAI
