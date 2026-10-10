import OAI.Computability.SpaceSimulation.Stack.Views
import OAI.Computability.SpaceSimulation.Stack.Edit

namespace OAI

/-!
Calls to fixed accessor programs can be used in binary stack computations.
The arguments are small (the conversion charges space for them too). Do
not simulate the public input head with a counter: pass it straight
through, and rewind when done.
-/
namespace Fifths

namespace WorkSplit
variable {A : Type}

noncomputable def bit (a x : A) : Bool :=
  @decide (x = a) (Classical.propDecidable _)

noncomputable def buf (z : WorkSplit A) (a : A) (d : Bool) : List Bool :=
  (if d then z.hi else z.lo).map (bit a)

noncomputable def read (b : A) (t : A → Option Bool) : A := by
  classical exact if h : ∃ a, t a = some true then Classical.choose h else b
theorem read_eq (b : A) (l : List A) :
    read b (fun a => (l.map (bit a)).head?) = l.head?.getD b := by
  classical
  cases l with
  | nil => simp [read]
  | cons x l =>
    unfold read
    dsimp
    split
    · rename_i h
      simp [bit]
    · rename_i h
      exfalso; apply h; exact ⟨x, by simp [bit]⟩

noncomputable def stepCenter (b _c : A) (t : A → Bool → Option Bool) (m : WriteMove A) :
    A := match m.dir with
  | .N => m.sym
  | .L => read b (fun a => t a false)
  | .R => read b (fun a => t a true)

noncomputable def stepOp (m : WriteMove A) (a : A) (d : Bool) : StOp :=
  match m.dir, d with
  | .N, _ => .keep
  | .L, false | .R, true => .pop
  | .L, true | .R, false => .push (bit a m.sym)
theorem stepCenter_eq (b : A) (z : WorkSplit A) (m : WriteMove A) :
    stepCenter b z.center (fun a d => (z.buf a d).head?) m =
      (z.slide m b).center := by
  obtain ⟨s, d⟩ := m
  cases d
  · exact read_eq b z.lo
  · rfl
  · exact read_eq b z.hi
theorem stepOp_eq (b : A) (z : WorkSplit A) (m : WriteMove A) (a : A) (d : Bool) :
    (stepOp m a d).apply (z.buf a d) = (z.slide m b).buf a d := by
  obtain ⟨s,f⟩ := m
  cases f <;> cases d <;> simp [stepOp,StOp.apply,buf,slide]
end WorkSplit

namespace ArgSplit
def buf (z : ArgSplit) (d : Bool) : List Bool := if d then z.hi else z.lo

def stepCenter (c : Mark Bool) (t : Bool → Option Bool) (f : Dir) : Mark Bool :=
  match f,c with
  | .N, c | .L, .left | .R, .right => c
  | .L, _ => ((t false).map Mark.sym).getD .left
  | .R, _ => ((t true).map Mark.sym).getD .right

def stepOp (c : Mark Bool) (f : Dir) (d : Bool) : StOp :=
  match f,c with
  | .N, _ | .L, .left | .R, .right => .keep
  | .L, c => if d then match c with | .sym b => .push b | _ => .keep
    else .pop
  | .R, c => if d then .pop
    else match c with | .sym b => .push b | _ => .keep

theorem stepCenter_eq (z : ArgSplit) (f : Dir) :
    stepCenter z.center (fun d => (z.buf d).head?) f = (z.slide f).center := by
  obtain ⟨c,l,h⟩ := z
  cases f <;> cases c <;> rfl

theorem stepOp_eq (z : ArgSplit) (f : Dir) (d : Bool) :
    (stepOp z.center f d).apply (z.buf d) = (z.slide f).buf d := by
  obtain ⟨c,l,h⟩ := z
  cases d <;> cases f <;> cases c <;> rfl
end ArgSplit

namespace TM
variable {X J Y : Type} (M : TM X J Y)

abbrev stkIdx := (((k : M.K) × M.W k) × Bool) ⊕ (J × Bool)
abbrev stkQ := M.Q × ((∀ k : M.K, M.W k) × (J → Mark Bool))

namespace SRep
-- Encoding of a represented configuration in stacks
end SRep

section
variable [Finite J]
noncomputable def asSM : SM X Empty M.stkIdx Y where
  Q := M.stkQ
  start := (M.start, M.blank, fun _ => .left)
  table := fun q r top =>
    match M.table q.1 ⟨r.sx,q.2.2⟩ q.2.1 with
    | .inl y => .inl y
    | .inr a =>
      .inr (.withState
        ⟨{dx := a.advance.dx},
         fun k => match k with
         | .inl (⟨k,w⟩,d) => WorkSplit.stepOp (a.moves k) w d
         | .inr (j,d) => ArgSplit.stepOp (q.2.2 j) (a.advance.darg j) d⟩
        (a.next,
         fun k => WorkSplit.stepCenter (M.blank k) (q.2.1 k)
           (fun w d => top (.inl (⟨k,w⟩, d))) (a.moves k),
         fun j => ArgSplit.stepCenter (q.2.2 j)
           (fun d => top (.inr (j,d))) (a.advance.darg j)))

structure SRep (s : M.Cfg) (i : Inputs X J) (w : M.Window) where
  ws : ∀ k, WorkSplit (M.W k)
  aspl : J → ArgSplit
  wg : ∀ k, (ws k).Good (s.work k) (M.blank k) (w.l k) (w.h k)
  ag : ∀ j, (aspl j).Good (i.arg j) (s.ro.parg j)

namespace SRep
variable {M} {s : M.Cfg} {i : Inputs X J} {w : M.Window}

noncomputable def cfg (z : M.SRep s i w) : M.asSM.Cfg :=
  ((s.state, (fun k => (z.ws k).center), fun j => (z.aspl j).center),
   ⟨{px := s.ro.px}, fun k => match k with
     | .inl (⟨k,a⟩,d) => (z.ws k).buf a d
     | .inr (j,d) => (z.aspl j).buf d⟩)

def after (z : M.SRep s i w)
    (a : TAction M.Q J M.K M.W)
    (q : ∀ k : M.K, -(w.l k : ℤ) ≤ ((s.work k).perform (a.moves k)).pos ∧
      ((s.work k).perform (a.moves k)).pos ≤ w.h k) :
    M.SRep ⟨a.next, s.ro.walk i a.advance, fun k => (s.work k).perform (a.moves k)⟩ i w :=
  ⟨fun k => (z.ws k).slide (a.moves k) (M.blank k),
   fun j => (z.aspl j).slide (a.advance.darg j),
   fun k => WorkSplit.good_slide _ (z.wg k) (q k).1 (q k).2,
   fun j => ArgSplit.good_slide (z.ag j) _⟩

theorem cfg_ok (z : M.SRep s i w) {B} (h : w.bits ≤ B)
    (g : ∀ j, (i.arg j).length ≤ B) : z.cfg.2.ok B := by
  rintro (⟨⟨k,a⟩,d⟩|⟨j,d⟩)
  · have e := WorkSplit.good_lengths (z.wg k)
    have := le_trans (w.span_le k) h
    cases d <;> simp [cfg,WorkSplit.buf] <;> omega
  · have e := ArgSplit.good_lengths (z.ag j)
    specialize g j
    cases d <;> simp [cfg,ArgSplit.buf] <;> omega

-- step uses represented centers; rewrite the original table facts only.
omit [Finite J] in
theorem sees (z : M.SRep s i w) :
    Reads.mk (Mark.see i.publicWord s.ro.px) (fun j => (z.aspl j).center) =
      s.ro.see i := by
  dsimp only [Readers.see]
  congr
  ext j
  exact (ArgSplit.good_see (z.ag j)).symm

omit [Finite J] in
theorem centers (z : M.SRep s i w) :
    (fun k => (z.ws k).center) = fun k => (s.work k).see := by
  funext k; exact (z.wg k).see.symm

theorem halt (z : M.SRep s i w) {y}
    (e : M.table s.state (s.ro.see i) (fun k => (s.work k).see) = Sum.inl y) :
    M.asSM.step ⟨i.publicWord, Empty.elim⟩ z.cfg = Sum.inl y := by
  dsimp only [SM.step, asSM,cfg,Readers.see]
  rw [z.sees,z.centers,e]

theorem continue_step (z : M.SRep s i w) {a}
    (q : ∀ k : M.K, -(w.l k : ℤ) ≤ ((s.work k).perform (a.moves k)).pos ∧
      ((s.work k).perform (a.moves k)).pos ≤ w.h k)
    (e : M.table s.state (s.ro.see i) (fun k => (s.work k).see) = Sum.inr a) :
    M.asSM.step ⟨i.publicWord, Empty.elim⟩ z.cfg = Sum.inr (z.after a q).cfg := by
  dsimp only [SM.step, asSM,cfg,Readers.see]
  -- rewrite only table call (centers elsewhere needed)
  have f : M.table s.state
      ⟨Mark.see i.publicWord s.ro.px, fun j => (z.aspl j).center⟩
      (fun k => (z.ws k).center) = Sum.inr a := by rw [z.sees,z.centers,e]
  rw [f]
  simp only [Sum.inr.injEq, Prod.mk.injEq, true_and, SAction.withState, after,
    Store.see, ArgSplit.stepCenter_eq, WorkSplit.stepCenter_eq]
  refine Store.ext' rfl ?_
  rintro (⟨⟨k,m⟩,d⟩ | ⟨j,d⟩)
  · exact WorkSplit.stepOp_eq _ _ _ _ _
  · exact ArgSplit.stepOp_eq _ _ _

theorem emulate {B} (bw : w.bits ≤ B) (g : ∀ j, (i.arg j).length ≤ B)
    {t y} (r : Runs (M.step i) w.ok s t y) (z : M.SRep s i w) :
    ∃ u, M.asSM.Run ⟨i.publicWord, Empty.elim⟩ B z.cfg u y := by
  induction r with
  | @stop s y _ e =>
    refine ⟨_, Runs.stop (z.cfg_ok bw g) ?_⟩
    unfold TM.step at e
    cases h : M.table s.state (s.ro.see i) (fun k => (s.work k).see) with
    | inl v => apply halt; rw [h]; simp_all only [Sum.inl.injEq]
    | inr v => rw [h] at e; contradiction
  | @step s s' t y _ e tail ih =>
    unfold TM.step at e
    cases h : M.table s.state (s.ro.see i) (fun k => (s.work k).see) with
    | inl v => rw [h] at e; contradiction
    | inr a =>
      simp only [h,Sum.inr.injEq] at e
      subst s'
      obtain ⟨u,r⟩ := ih (z.after a tail.startOk)
      exact ⟨u,.step (z.cfg_ok bw g) (z.continue_step tail.startOk h) r⟩
end SRep

/-- Work stacks empty. Argument j on its right stack. -/
def loaded (x : J → List Bool) : M.stkIdx → List Bool :=
  Sum.elim (fun _ => []) (fun p => if p.2 then x p.1 else [])

theorem asSM_exec {i : Inputs X J} {B y}
    (r : M.Within i y B) (g : ∀ j, (i.arg j).length ≤ B) :
    ∃ s, M.asSM.Exec ⟨i.publicWord, Empty.elim⟩ B
      (.init (M.loaded i.arg)) s y := by
  obtain ⟨w,h,t,r⟩ := r
  let z : M.SRep M.initial i w :=
    { ws := fun k => WorkSplit.init (M.blank k)
      aspl := fun j => ArgSplit.init (i.arg j)
      wg := fun k => WorkSplit.init_good _ _ _
      ag := fun j => .left _ }
  have e : z.cfg = (M.asSM.start, .init (M.loaded i.arg)) := by
    apply Prod.ext
    · rfl
    · refine Store.ext' rfl ?_
      rintro (⟨⟨k,a⟩,d⟩ | ⟨j,d⟩)
      · cases d <;> rfl
      · cases d <;> rfl
  obtain ⟨⟨q,u⟩,r⟩ := z.emulate h g r
  rw [e] at r
  exact ⟨u,q,r⟩
end

end TM
namespace SM
variable {X Y J K : Type}

section
variable [DecidableEq K]

def clears : List K → SM X J K Unit
  | [] => pure ()
  | k :: l => (clear k).seq (clears l)

def wiped (l : List K) (s : Store J K) : Store J K :=
  ⟨s.ro, fun k => if k ∈ l then [] else s.st k⟩

theorem clears_exec {s : Store J K} (l : List K)
    {B} {i : Inputs X J} (o : s.ok B) :
    (clears l).Exec i B s (wiped l s) () := by
  induction l generalizing s with
  | nil =>
    have e : wiped [] s = s := by
      refine Store.ext' rfl ?_; simp [wiped]
    rw [e]
    exact exec_pure o
  | cons k l ih =>
    have e : wiped l (s.set k []) = wiped (k::l) s := by
      refine Store.ext' rfl ?_
      intro y
      by_cases h : y = k <;> simp [wiped,h]
    rw [← e]
    exact exec_seq (exec_clear k o) (ih (Store.set_ok o (by simp)))
end

/-- Wipe stacks and rewind public input, yielding the initial empty
stack configuration (no arg tapes). -/
noncomputable def cleanup [Fintype K] : SM X Empty K Unit := by
  classical exact (clears Finset.univ.toList).seq rewind

theorem cleanup_exec [Fintype K] {s : Store Empty K} {B}
    {i : Inputs X Empty} (o : s.ok B) :
    cleanup.Exec i B s (Store.init (fun _ => [])) () := by
  classical
  have r := clears_exec (i := i) Finset.univ.toList o
  have e : (wiped Finset.univ.toList s).atX 0 = (Store.init (fun _ => [])) := by
    refine Store.ext' ?_ ?_
    · dsimp only [Store.atX, Store.init, wiped, Readers.home]
      congr
      exact Subsingleton.elim _ _
    · simp [Store.atX, Store.init, wiped]
  have v := exec_seq r (exec_rewind r.endOk)
  rw [e] at v
  exact v
end SM
namespace TM
variable {X J Y : Type} [Fintype J] [Finite Y] (M : TM X J Y)

/-- Any ordinary space-bounded TM with small arguments can be used as a
subroutine. The result is a binary stack machine seeing just the public
input, expecting the (small) arguments from the caller on designated
stacks. No length counter for x. -/
noncomputable def subroutine : SM X Empty M.stkIdx Y :=
  M.asSM.bind (fun y => SM.cleanup.seq (SM.pure y))
theorem subroutine_exec {i : Inputs X J} {B y}
    (r : M.Within i y B) (g : ∀ j, (i.arg j).length ≤ B) :
    M.subroutine.Exec ⟨i.publicWord, Empty.elim⟩ B (.init (M.loaded i.arg))
      (Store.init (fun _ => [])) y := by
  obtain ⟨s,r⟩ := M.asSM_exec r g
  have e := SM.cleanup_exec (i := Inputs.mk i.publicWord Empty.elim) r.endOk
  exact SM.exec_bind M.asSM (fun y => SM.cleanup.seq (SM.pure y))
    r (SM.exec_seq e (SM.exec_pure e.endOk))
end TM
end Fifths

end OAI
