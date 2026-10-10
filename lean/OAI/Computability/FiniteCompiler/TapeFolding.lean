import OAI.Computability.FiniteCompiler.Machines

namespace OAI

/-!
Safe tapes, literal folding, and uniform code-machine realization.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.OneSided
open Compiler.Simulator Turing Relation
variable {Γ Q : Type*}

structure Cfg (Γ Q : Type*) where
  state : Q
  pos : ℕ
  cell : ℕ → Γ

def step (M : Machine Q Γ) (c : Cfg Γ Q) : Option (Cfg Γ Q) :=
  (M.transition c.state (c.cell c.pos)).map fun cmd =>
    ⟨cmd.state,(match cmd.move with | .stay => c.pos | .left => c.pos-1 | .right => c.pos+1),
      Function.update c.cell c.pos cmd.write⟩

def view (c : SemanticTape Γ Q) : Cfg Γ Q := ⟨c.state,c.left.length,semanticContent c⟩

 theorem append_at (l : List Γ) (s : Stream' Γ) (n : ℕ) :
   Stream'.appendStream' l s (l.length+n) = s n := by
  induction l with
  | nil => simp only [List.length_nil,Nat.zero_add,Stream'.appendStream']
  | cons a l ih => simpa only [List.length_cons,Nat.succ_add,Stream'.appendStream',Stream'.cons] using ih

 theorem replace_at (l : List Γ) (s : Stream' Γ) (a : Γ) :
   Stream'.appendStream' l (Stream'.cons a s.tail) =
     Function.update (Stream'.appendStream' l s) l.length a := by
  unfold Stream' at *
  funext n
  induction l generalizing n with
  | nil => cases n <;> simp [Stream'.appendStream',Stream'.cons,Stream'.tail,Stream'.get]
  | cons b l ih =>
    cases n with
    | zero => simp [Stream'.appendStream',Stream'.cons,Function.update]
    | succ n =>
      by_cases hn : n = l.length
      · subst n
        simpa [Stream'.appendStream',Stream'.cons,Function.update] using ih l.length
      · simpa [Stream'.appendStream',Stream'.cons,Function.update,hn] using ih n

 theorem view_step (M : Machine Q Γ) (c : SemanticTape Γ Q) :
   (semanticStep M c).map view = step M (view c) := by
  rcases c with ⟨q,l,r⟩
  have hh : Stream'.appendStream' l.reverse r l.length = r.head := by
    simpa only [List.length_reverse,Nat.add_zero,Stream'.head,Stream'.get] using append_at l.reverse r 0
  simp only [semanticStep,step,view,semanticContent,hh,Option.map_map]
  congr 1
  funext cmd
  rcases cmd with ⟨q',a,mv⟩
  cases mv with
  | stay =>
      dsimp only [Function.comp_apply,view,semanticContent]
      congr 1
      simpa only [List.length_reverse,Stream'] using replace_at l.reverse r a
  | right =>
      dsimp only [Function.comp_apply,view,semanticContent,List.length_cons]
      congr 1
      simpa only [semanticContent,List.reverse_cons,Stream'.append_append_stream,List.length_cons,
        Stream'.appendStream',List.length_reverse,Stream'] using replace_at l.reverse r a
  | left =>
      cases l with
      | nil =>
          dsimp only [Function.comp_apply,view,semanticContent,List.length_nil,Nat.zero_sub]
          congr 1
          exact replace_at [] r a
      | cons b l =>
          dsimp only [Function.comp_apply,view,semanticContent,List.length_cons]
          simp only [Nat.add_sub_cancel]
          congr 1
          simpa only [semanticContent,List.reverse_cons,Stream'.append_append_stream,List.length_cons,
            Nat.add_sub_cancel,Stream'.appendStream',List.length_reverse,List.length_append,List.length_singleton,List.length_nil,Nat.zero_add,Stream'] using replace_at (l.reverse ++ [b]) r a

 theorem respects (M : Machine Q Γ) : StateTransition.Respects (step M) (semanticStep M)
   (fun a b => view b = a) := by
  intro c s hs
  rw [←hs,←view_step M s]
  cases hc : semanticStep M s with
  | none => rfl
  | some t => exact ⟨t,rfl,TransGen.single hc⟩

end FiniteAlgebraicEnvelopes.MachineRealization.OneSided

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeFold
open Turing Relation Compiler.Simulator
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

inductive Side | pos | neg deriving DecidableEq
instance : Fintype Side := ⟨{.pos,.neg},by intro x; cases x <;> simp⟩
structure Cell (Γ : Type*) where
  origin : Bool
  pos : Γ
  neg : Γ
  deriving DecidableEq, Fintype

def position : Side → ℕ → ℤ
  | .pos,n => n
  | .neg,n => -(n+1 : ℤ)

def read (d : Side) (a : Cell Γ) : Γ := match d with | .pos => a.pos | .neg => a.neg

def command (d : Side) (q : Λ) (a : Cell Γ) : TM0.Stmt Γ → Command (Side × Λ) (Cell Γ)
  | .write b => ⟨(d,q),(match d with | .pos => {a with pos := b} | .neg => {a with neg := b}),.stay⟩
  | .move dr => match d,dr with
    | .pos,.right => ⟨(.pos,q),a,.right⟩
    | .pos,.left => if a.origin then ⟨(.neg,q),a,.stay⟩ else ⟨(.pos,q),a,.left⟩
    | .neg,.left => ⟨(.neg,q),a,.right⟩
    | .neg,.right => if a.origin then ⟨(.pos,q),a,.stay⟩ else ⟨(.neg,q),a,.left⟩

def machine (M : TM0.Machine Γ Λ) (start : Λ) : Machine (Side × Λ) (Cell Γ) :=
  ⟨(.pos,start),fun q a => (M q.2 (read q.1 a)).map fun cmd => command q.1 cmd.1 a cmd.2⟩

/-- The two halves of the integer tape share one physical cell. The immutable
origin flag makes crossing the fold a finite-control, zero-movement operation. -/
def Rel (c : TM0.Cfg Γ Λ) (s : OneSided.Cfg (Cell Γ) (Side × Λ)) : Prop :=
  s.state.2 = c.q ∧ ∀ n,
    (s.cell n).origin = decide (n = 0) ∧
    (s.cell n).pos = c.Tape.nth ((n:ℤ) - position s.state.1 s.pos) ∧
    (s.cell n).neg = c.Tape.nth (-(n+1:ℤ) - position s.state.1 s.pos)

omit [Inhabited Λ] in
theorem read_head {c : TM0.Cfg Γ Λ} {s : OneSided.Cfg (Cell Γ) (Side × Λ)} (h : Rel c s) :
    read s.state.1 (s.cell s.pos) = c.Tape.head := by
  obtain ⟨_,hs⟩ := h
  obtain ⟨_,hp,hn⟩ := hs s.pos
  cases hd : s.state.1 <;> simp only [read,hd,position,sub_self,Tape.nth_zero] at * <;> assumption

omit [Inhabited Γ] [Inhabited Λ] in
 theorem move_position (d : Side) (dr : Dir) (q : Λ) (a : Cell Γ) (p : ℕ)
    (ha : a.origin = decide (p = 0)) :
    let cmd := command d q a (.move dr)
    position cmd.state.1 (match cmd.move with | .stay => p | .left => p-1 | .right => p+1) =
      position d p + (match dr with | .left => -1 | .right => 1) := by
  cases d <;> cases dr <;> simp only [command,ha] <;>
    (try split_ifs) <;> simp_all [position] <;> omega

omit [Inhabited Γ] [Inhabited Λ] in
 theorem move_write (d : Side) (dr : Dir) (q : Λ) (a : Cell Γ) :
    (command d q a (.move dr)).write = a := by
  cases d <;> cases dr <;> simp only [command] <;> (try split_ifs) <;> rfl

omit [Inhabited Γ] [Inhabited Λ] in
 theorem command_state (d : Side) (q : Λ) (a : Cell Γ) (stmt : TM0.Stmt Γ) :
    (command d q a stmt).state.2 = q := by
  cases stmt with
  | write b => cases d <;> rfl
  | move dr => cases d <;> cases dr <;> simp only [command] <;> (try split_ifs) <;> rfl

 theorem step_rel (M : TM0.Machine Γ Λ) (start : Λ)
    {c : TM0.Cfg Γ Λ} {s : OneSided.Cfg (Cell Γ) (Side × Λ)} (hs : Rel c s)
    {cmd : Λ × TM0.Stmt Γ} (hc : M c.q c.Tape.head = some cmd) :
    ∃ t, Rel (⟨cmd.1,match cmd.2 with | .move d => c.Tape.move d | .write b => c.Tape.write b⟩) t ∧
      OneSided.step (machine M start) s = some t := by
  let ins := command s.state.1 cmd.1 (s.cell s.pos) cmd.2
  let t : OneSided.Cfg (Cell Γ) (Side × Λ) :=
    ⟨ins.state,(match ins.move with | .stay => s.pos | .left => s.pos-1 | .right => s.pos+1),
      Function.update s.cell s.pos ins.write⟩
  refine ⟨t,?_,?_⟩
  · refine ⟨command_state _ _ _ _,fun n => ?_⟩
    obtain ⟨hor,hpo,hne⟩ := hs.2 n
    obtain ⟨hop,_,_⟩ := hs.2 s.pos
    cases hcmd : cmd.2 with
    | move d =>
      have hw : ins.write = s.cell s.pos := by dsimp [ins]; rw [hcmd,move_write]
      have hp := move_position s.state.1 d cmd.1 (s.cell s.pos) s.pos hop
      change _ = _ at hp
      have hcelt : t.cell = s.cell := by dsimp [t]; rw [hw,Function.update_eq_self]
      have hpos : position t.state.1 t.pos = position s.state.1 s.pos +
          (match d with | .left => -1 | .right => 1) := by cases d <;> simpa only [t,ins,hcmd] using hp
      change (t.cell n).origin = _ ∧ (t.cell n).pos = _ ∧ (t.cell n).neg = _
      rw [hcelt]
      refine ⟨hor,?_,?_⟩
      · rw [hpos]
        cases d <;> simp only [Tape.move_left_nth,Tape.move_right_nth] <;>
          convert hpo using 1 <;> congr 1 <;> omega
      · rw [hpos]
        cases d <;> simp only [Tape.move_left_nth,Tape.move_right_nth] <;>
          convert hne using 1 <;> congr 1 <;> omega
    | write b =>
      cases hd : s.state.1 <;>
        simp only [t,ins,hcmd,command,hd,position]
      · by_cases hn : n = s.pos
        · subst n
          simp only [Function.update_self]
          refine ⟨hop,?_,?_⟩
          · simp [Tape.write]
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
        · rw [Function.update_of_ne hn]
          refine ⟨hor,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
      · by_cases hn : n = s.pos
        · subst n
          simp only [Function.update_self]
          refine ⟨hop,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · simp [Tape.write]
        · rw [Function.update_of_ne hn]
          refine ⟨hor,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
  · simp only [OneSided.step,machine,hs.1,read_head hs,hc,Option.map_some]
    rfl

 theorem respects (M : TM0.Machine Γ Λ) (start : Λ) :
    StateTransition.Respects (TM0.step M) (OneSided.step (machine M start)) Rel := by
  intro c s hs
  cases hc : M c.q c.Tape.head with
  | none => simp only [TM0.step,hc,Option.map_none,OneSided.step,machine,hs.1,read_head hs]
  | some cmd =>
    simp only [TM0.step,hc,Option.map_some]
    obtain ⟨t,ht,hst⟩ := step_rel M start hs hc
    exact ⟨t,ht,TransGen.single hst⟩

end FiniteAlgebraicEnvelopes.MachineRealization.TapeFold

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeSafety
open Turing
variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Every writing subinstruction preserves the bottom track. -/
def Safe : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ → Prop
  | .move _ q => Safe q
  | .write f q => (∀ a v, (f a v).1 = a.1) ∧ Safe q
  | .load _ q => Safe q
  | .branch _ q r => Safe q ∧ Safe r
  | .goto _ => True
  | .halt => True

theorem safe_stAct [DecidableEq K] {k : K}
    {q : TM1.Stmt (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ} (hq : Safe q)
    (a : TM2to1.StAct K Γ σ k) : Safe (TM2to1.trStAct q a) := by
  cases a <;> simp [TM2to1.trStAct,Safe,hq]

theorem safe_normal (q : TM2.Stmt Γ Λ σ) : Safe (TM2to1.trNormal q) := by
  induction q <;> simp_all [TM2to1.trNormal,Safe]

theorem safe_tr [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2to1.Λ' K Γ Λ σ) :
    Safe (TM2to1.tr M q) := by
  cases q with
  | normal q => exact safe_normal _
  | go k a q =>
      change Safe (TM2to1.trStAct (.goto fun _ _ => .ret q) a) ∧ True
      exact ⟨safe_stAct (q := .goto fun _ _ => .ret q) trivial a,trivial⟩
  | ret q => simp [TM2to1.tr,Safe,safe_normal]

theorem safe_sub {q r : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ}
    (h : q ∈ TM1.stmts₁ r) (hr : Safe r) : Safe q := by
  classical
  induction r with
    simp only [TM1.stmts₁,Safe,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at h hr
  | move d r ih => rcases h with rfl | h; exact hr; exact ih h hr
  | write f r ih => rcases h with rfl | h; exact hr; exact ih h hr.2
  | load f r ih => rcases h with rfl | h; exact hr; exact ih h hr
  | branch p r s ihr ihs => rcases h with rfl | h | h; exact hr; exact ihr h hr.1; exact ihs h hr.2
  | goto l => subst q; trivial
  | halt => subst q; trivial

theorem safe_stmts (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (B : Finset Λ)
    (hm : ∀ q, Safe (M q)) {q : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ}
    (hq : some q ∈ TM1.stmts M B) : Safe q := by
  classical
  simp only [TM1.stmts,Finset.mem_insertNone,Option.mem_def,Option.some.injEq,forall_eq',Finset.mem_biUnion] at hq
  obtain ⟨l,_,hl⟩ := hq
  exact safe_sub hl (hm l)

theorem trAux_write (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ)
    (a : TM2to1.Γ' K Γ) (q : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (v : σ)
    (hq : Safe q) (b : TM2to1.Γ' K Γ)
    (he : (TM1to0.trAux M a q v).2 = .write b) : b.1 = a.1 := by
  induction q generalizing v with
  | move d q ih => cases he
  | write f q ih => cases he; exact hq.1 a v
  | load f q ih => exact ih _ hq he
  | branch p q r ihq ihr =>
      cases hp : p a v <;> simp only [TM1to0.trAux,hp,Bool.cond_false,Bool.cond_true] at he
      · exact ihr _ hq.2 he
      · exact ihq _ hq.1 he
  | goto l => cases he; rfl
  | halt => cases he; rfl

/-- A machine preserves the distinguished bottom marker on every write. -/
def Preserves {L : Type*} [Inhabited L] (M : TM0.Machine (TM2to1.Γ' K Γ) L) : Prop :=
  ∀ q a q' b, M q a = some (q',.write b) → b.1 = a.1

theorem finite_preserves [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (B : Finset Λ)
    (hB : TM1.Supports M B) (hm : ∀ q, Safe (M q))
    [Inhabited {l // l ∈ TM1to0.trStmts M B}] :
    Preserves (FiniteTM0.machine (TM1to0.tr M) (TM1to0.trStmts M B) (TM1to0.tr_supports M hB)) := by
  classical
  intro q a q' b he
  have hq := q.property
  rcases q with ⟨⟨q,v⟩,hq'⟩
  cases q with
  | none => simp [FiniteTM0.machine,TM1to0.tr] at he
  | some q =>
    have hqm : some q ∈ TM1.stmts M B := (Finset.mem_product.mp hq').1
    have hs := safe_stmts M B hm hqm
    have hx : (TM1to0.trAux M a q v).2 = .write b := by
      have := congrArg (Option.map (fun (x : {l // l ∈ TM1to0.trStmts M B} × TM0.Stmt _) => x.2)) he
      simpa [FiniteTM0.machine,TM1to0.tr] using this
    exact trAux_write M a q v hs b hx

end FiniteAlgebraicEnvelopes.MachineRealization.TapeSafety

namespace FiniteAlgebraicEnvelopes.MachineRealization
open Turing
namespace WordEvaluator
open Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S : Type} [Fintype S] [Primcodable S]
 theorem exists_safe_tape {f : List S →. List S} (hf : Partrec f) :
   ∃ (Λ : Type) (_ : Fintype Λ) (_ : Inhabited Λ)
     (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start stop : Λ),
     TapeSafety.Preserves M ∧ ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
       (f w).map (fun out => ⟨stop,tape out⟩) := by
  classical
  obtain ⟨Λ,hΛ,M,start,hM⟩ := exists_raw hf
  let : Fintype Λ := hΛ
  let : Inhabited Λ := ⟨start⟩
  let N := TM2to1.tr M
  let P := TM1to0.tr N
  let B := TM2to1.trSupp M Finset.univ
  have hU : TM2.Supports M Finset.univ := by
    refine ⟨Finset.mem_univ _,fun q _ => ?_⟩
    induction M q <;> simp_all [TM2.SupportsStmt]
  have hB : TM1.Supports N B := TM2to1.tr_supports M hU
  let C := TM1to0.trStmts N B
  have hC : TM0.Supports P (C : Set _) := TM1to0.tr_supports N hB
  let : Inhabited {l // l ∈ C} := ⟨⟨default,hC.1⟩⟩
  have hs : (none,none) ∈ C := by
    change (none,none) ∈ (TM1.stmts N B) ×ˢ (Finset.univ : Finset (Store S))
    exact Finset.mem_product.mpr ⟨Finset.none_mem_insertNone,Finset.mem_univ _⟩
  refine ⟨{l // l ∈ C},inferInstance,inferInstance,FiniteTM0.machine P C hC,default,⟨(none,none),hs⟩,TapeSafety.finite_preserves N B hB (TapeSafety.safe_tr M),fun w => ?_⟩
  apply part_map_injective (FiniteTM0.embed_injective C)
  rw [←FiniteTM0.eval_embed P C hC]
  change StateTransition.eval (TM0.step P) (TM1to0.trCfg N ⟨some (.normal start),none,tape w⟩) = _
  rw [eval_post M start hM]
  simp only [Part.map_map]
  rfl

end WordEvaluator
end FiniteAlgebraicEnvelopes.MachineRealization

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeFold
open Turing Relation Compiler.Simulator
variable {K : Type} {Γ : K → Type} {Λ : Type} [Inhabited Λ]

 def Marked (s : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)) : Prop :=
  ∀ n, (s.cell n).pos.1 = decide (n=0) ∧ (s.cell n).neg.1 = false

 theorem marked_step (M : TM0.Machine (TM2to1.Γ' K Γ) Λ) (start : Λ)
    (hM : TapeSafety.Preserves M) {s t : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)}
    (hs : Marked s) (hst : OneSided.step (machine M start) s = some t) : Marked t := by
  unfold OneSided.step machine at hst
  cases hc : M s.state.2 (read s.state.1 (s.cell s.pos)) with
  | none => simp only [hc,Option.map_none] at hst; cases hst
  | some cmd =>
    simp only [hc,Option.map_some,Option.some.injEq] at hst
    subst t
    intro n
    dsimp only [OneSided.Cfg.cell]
    by_cases hn : n = s.pos
    · subst n
      rw [Function.update_self]
      cases hd : cmd.2 with
      | move d => simpa only [move_write] using hs s.pos
      | write b =>
        have hp := hM s.state.2 (read s.state.1 (s.cell s.pos)) cmd.1 b (by rw [←hd]; exact hc)
        cases he : s.state.1 <;> simp only [he,read] at hp
        · exact ⟨hp.trans (hs s.pos).1,(hs s.pos).2⟩
        · exact ⟨(hs s.pos).1,hp.trans (hs s.pos).2⟩
    · rw [Function.update_of_ne hn]
      exact hs n

 theorem marked_run (M : TM0.Machine (TM2to1.Γ' K Γ) Λ) (start : Λ)
    (hM : TapeSafety.Preserves M) {s t : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)}
    (hs : Marked s) (hst : ReflTransGen (fun a b => OneSided.step (machine M start) a = some b) s t) : Marked t := by
  induction hst with
  | refl => exact hs
  | tail _ h ih => exact marked_step M start hM ih h

end FiniteAlgebraicEnvelopes.MachineRealization.TapeFold

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

section
open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S : Type} {Λ : Type} [Inhabited Λ]
abbrev Gamma (S : Type) := Cell (TM2to1.Γ' K' (fun _ => Symbol S))

theorem cell_ext (a b : Cell (TM2to1.Γ' K' (fun _ => Symbol S)))
    (ho : a.origin=b.origin) (hp : a.pos=b.pos) (hn : a.neg=b.neg) : a=b := by
  cases a; cases b; cases ho; cases hp; cases hn; rfl

def blank : Gamma S := ⟨false,default,default⟩
def input (a : S) : Gamma S := ⟨false,(false,slice a),default⟩
def raw (w : List S) : ℕ → Gamma S := Stream'.appendStream' (w.map input) (Stream'.const blank)
def canon (q : Λ) (w : List S) : OneSided.Cfg (Gamma S) (Side × Λ) :=
  ⟨(.pos,q),0,fun n => ⟨decide (n=0),(tape w).nth n,(tape w).nth (-(n+1:ℤ))⟩⟩

omit [Inhabited Λ] in
theorem canon_rel (q : Λ) (w : List S) : Rel (⟨q,tape w⟩ : TM0.Cfg _ _) (canon q w) := by
  refine ⟨rfl,fun n => ?_⟩
  simp [canon,position]

theorem tape_neg (w : List S) (n : ℕ) : (tape w).nth (-(n+1:ℤ)) = default := by
  change ListBlank.nth (∅ : ListBlank _) n = default
  rfl

theorem tape_fst (w : List S) (n : ℕ) : ((tape w).nth n).1 = decide (n=0) := by
  rw [tape,Tape.mk'_nth_nat]
  cases n with
  | zero => simpa only [ListBlank.nth_zero,decide_true] using TM2to1.addBottom_head_fst (stackList w)
  | succ n => exact TM2to1.addBottom_nth_succ_fst _ n

omit [Inhabited Λ] in
theorem canon_marked (q : Λ) (w : List S) : Marked (canon q w) := by
  intro n
  exact ⟨tape_fst w n,congrArg Prod.fst (tape_neg w n)⟩

theorem raw_cell (w : List S) (n : ℕ) : raw w n = ⟨false,(false,(stackList w).nth n),default⟩ := by
  induction w generalizing n with
  | nil => simp [raw,blank,stackList,ListBlank.nth_mk]; rfl
  | cons a w ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [raw,List.map_cons,Stream'.appendStream',Stream'.cons,stackList,ListBlank.nth_mk,List.getI_cons_succ] using ih n

def mark (c : Gamma S) : Gamma S := ⟨true,(true,c.pos.2),c.neg⟩
def clear (c : Gamma S) : Gamma S := ⟨false,(false,c.pos.2),c.neg⟩

omit [Inhabited Λ] in
theorem canon_cells (q : Λ) (w : List S) : (canon q w).cell = Function.update (raw w) 0 (mark (raw w 0)) := by
  funext n
  have hh : (canon q w).cell n = ⟨decide (n=0),(decide (n=0),(stackList w).nth n),default⟩ := by
    apply cell_ext
    · rfl
    · exact Prod.ext (tape_fst w n) (by
        change ((tape w).nth (n:ℤ)).2 = _
        rw [tape,Tape.mk'_nth_nat]
        exact TM2to1.addBottom_nth_snd (stackList w) n)
    · exact tape_neg w n
  rw [hh]
  by_cases hn : n=0
  · subst n
    rw [Function.update_self,raw_cell]
    rfl
  · rw [Function.update_of_ne hn,raw_cell]
    simp only [hn,decide_false]

omit [Inhabited Λ] in
theorem canon_clear (q : Λ) (w : List S) :
    Function.update (canon q w).cell 0 (clear ((canon q w).cell 0)) = raw w := by
  rw [canon_cells]
  simp only [Function.update_self]
  have hh : clear (mark (raw w 0)) = raw w 0 := by rw [raw_cell]; rfl
  rw [hh,Function.update_idem,Function.update_eq_self]

omit [Inhabited Λ] in
theorem rel_canon_unique {s : OneSided.Cfg (Gamma S) (Side × Λ)}
    (q : Λ) (w : List S) (hr : Rel (⟨q,tape w⟩ : TM0.Cfg _ _) s) (hm : Marked s) : s = canon q w := by
  have hh := congrArg Prod.fst (read_head hr)
  have hb : (tape w).head.1 = true := TM2to1.addBottom_head_fst _
  rw [hb] at hh
  have hp : s.state.1 = .pos ∧ s.pos = 0 := by
    cases hd : s.state.1 with
    | pos =>
      simp only [hd,TapeFold.read] at hh
      rw [(hm s.pos).1] at hh
      exact ⟨rfl,of_decide_eq_true hh⟩
    | neg => simp only [hd,TapeFold.read,(hm s.pos).2] at hh; cases hh
  rcases s with ⟨⟨d,l⟩,p,c⟩
  obtain ⟨rfl,rfl⟩ := hp
  obtain ⟨rfl,hc⟩ := hr
  congr 1
  funext n
  obtain ⟨ho,hp,hn⟩ := hc n
  apply cell_ext
  · exact ho
  · simpa only [canon,position,Int.natCast_zero,sub_zero] using hp
  · simpa only [canon,position,Int.natCast_zero,sub_zero] using hn

end

open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [Inhabited Λ]

theorem folded_eval (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ)
    (start stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) (w : List S) :
    StateTransition.eval (OneSided.step (TapeFold.machine M start)) (canon start w) =
      (f w).map (canon stop) := by
  apply Part.ext
  intro s
  constructor
  · intro hs
    obtain ⟨c,hc,hce⟩ := StateTransition.tr_eval_rev (TapeFold.respects M start) (canon_rel start w) hs
    rw [hM] at hce
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hce
    have hmarked := marked_run M start hm (canon_marked start w) (StateTransition.mem_eval.mp hs).1
    rw [rel_canon_unique stop out hc hmarked]
    exact Part.mem_map _ hout
  · intro hs
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hs
    have hb : (⟨stop,tape out⟩ : TM0.Cfg _ _) ∈ StateTransition.eval (TM0.step M) ⟨start,tape w⟩ := by
      rw [hM]; exact Part.mem_map _ hout
    obtain ⟨s,hs,hse⟩ := StateTransition.tr_eval (TapeFold.respects M start) (canon_rel start w) hb
    have hmarked := marked_run M start hm (canon_marked start w) (StateTransition.mem_eval.mp hse).1
    exact rel_canon_unique stop out hs hmarked ▸ hse

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.MachineRealization.After
open Relation StateTransition
variable {α β : Type*} (f : α → Option α) (g : β → Option β) (lift finish : α → β)
variable (hs : ∀ a, g (lift a) = (f a).elim (some (finish a)) (fun b => some (lift b)))
variable (hf : ∀ a, g (finish a) = none)
include hs hf

theorem path_cases {a : α} {z : β} (h : Reaches g (lift a) z) :
    (∃ b, Reaches f a b ∧ z=lift b) ∨ (∃ b, b ∈ eval f a ∧ z=finish b) := by
  induction h with
  | refl => exact Or.inl ⟨a,.refl,rfl⟩
  | @tail z z' _ hz ih =>
    change g z = some z' at hz
    rcases ih with ⟨b,hb,rfl⟩ | ⟨b,hb,rfl⟩
    · rw [hs] at hz
      cases hc : f b with
      | none =>
        simp only [hc,Option.elim_none,Option.some.injEq] at hz
        exact Or.inr ⟨b,mem_eval.mpr ⟨hb,hc⟩,hz.symm⟩
      | some c =>
        simp only [hc,Option.elim_some,Option.some.injEq] at hz
        exact Or.inl ⟨c,hb.tail hc,hz.symm⟩
    · rw [hf] at hz; cases hz

omit hf in
theorem lift_reaches {a b : α} (h : Reaches f a b) : Reaches g (lift a) (lift b) := by
  induction h with
  | refl => exact .refl
  | tail _ hc ih => exact ih.tail (by rw [hs,hc]; rfl)

theorem eval_lift (a : α) : eval g (lift a) = (eval f a).map finish := by
  apply Part.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hp,hz⟩ := mem_eval.mp hz
    rcases path_cases f g lift finish hs hf hp with ⟨b,_,rfl⟩ | ⟨b,hb,rfl⟩
    · rw [hs] at hz
      cases hc : f b <;> simp [hc] at hz
    · exact Part.mem_map _ hb
  · intro hz
    obtain ⟨b,hb,rfl⟩ := (Part.mem_map_iff _).mp hz
    obtain ⟨hr,hb⟩ := mem_eval.mp hb
    apply mem_eval.mpr
    exact ⟨(lift_reaches f g lift finish hs hr).tail (by rw [hs,hb]; rfl),hf b⟩

end FiniteAlgebraicEnvelopes.MachineRealization.After

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

section
open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [Inhabited Λ]
abbrev State (Λ : Type) := Option (Option (Side × Λ))

def wrapper (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ) :
    Machine (State Λ) (Gamma S) :=
  ⟨none,fun q a => match q with
    | none => some ⟨some (some (.pos,start)),mark a,.stay⟩
    | some none => none
    | some (some q) => match (TapeFold.machine M start).transition q a with
      | none => some ⟨some none,clear a,.stay⟩
      | some c => some ⟨some (some c.state),c.write,c.move⟩⟩

def lift (s : OneSided.Cfg (Gamma S) (Side × Λ)) : OneSided.Cfg (Gamma S) (State Λ) :=
  ⟨some (some s.state),s.pos,s.cell⟩
def finish (s : OneSided.Cfg (Gamma S) (Side × Λ)) : OneSided.Cfg (Gamma S) (State Λ) :=
  ⟨some none,s.pos,Function.update s.cell s.pos (clear (s.cell s.pos))⟩
def initial (w : List S) : OneSided.Cfg (Gamma S) (State Λ) := ⟨none,0,raw w⟩
def final (w : List S) : OneSided.Cfg (Gamma S) (State Λ) := ⟨some none,0,raw w⟩

variable (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ)
theorem wrapper_lift (s : OneSided.Cfg (Gamma S) (Side × Λ)) :
    OneSided.step (wrapper M start) (lift s) =
      (OneSided.step (TapeFold.machine M start) s).elim (some (finish s)) (fun t => some (lift t)) := by
  simp only [OneSided.step,lift,wrapper]
  cases hc : (TapeFold.machine M start).transition s.state (s.cell s.pos) with
  | none => rfl
  | some cmd => cases cmd.move <;> rfl

theorem wrapper_finish (s : OneSided.Cfg (Gamma S) (Side × Λ)) :
    OneSided.step (wrapper M start) (finish s) = none := rfl

theorem wrapper_initial (w : List S) : OneSided.step (wrapper M start) (initial w) = some (lift (canon start w)) := by
  simp only [OneSided.step,wrapper,initial,Option.map_some,lift,canon]
  congr 2
  exact (canon_cells start w).symm

omit [Inhabited Λ] in
theorem finish_canon (q : Λ) (w : List S) : finish (canon q w) = final (Λ := Λ) w := by
  simp only [finish,canon,final]
  congr 1
  exact canon_clear q w

theorem wrapper_eval (stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) (w : List S) :
    StateTransition.eval (OneSided.step (wrapper M start)) (initial w) = (f w).map (final (Λ := Λ)) := by
  rw [StateTransition.reaches_eval (ReflTransGen.single (wrapper_initial M start w)),
    After.eval_lift (OneSided.step (TapeFold.machine M start)) (OneSided.step (wrapper M start)) lift finish
      (wrapper_lift M start) (wrapper_finish M start),folded_eval M start stop hm hM]
  simp only [Part.map_map,Function.comp_def,finish_canon]

end

open Turing Compiler.Simulator Turing.PartrecToTM2 StackLift StackTape
variable {S : Type} [DecidableEq S]

instance : Fintype K' := ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩

instance : DecidableEq (TM2to1.Γ' K' (fun _ => Symbol S)) := by
  unfold TM2to1.Γ'; infer_instance

def output (c : Gamma S) : Option S := match c.pos.2 .main with
  | some (.inr a) => if c = input a then some a else none
  | _ => none

def alphabet : Alphabet S (Gamma S) where
  blank := blank
  input := input
  output := output
  output_input a := by simp [output,input,slice]
  output_blank := rfl

theorem output_decode (c : Gamma S) (a : S) (he : output c = some a) : c = input a := by
  unfold output at he
  cases hc : c.pos.2 .main with
  | none => simp [hc] at he
  | some s =>
    cases s with
    | inl b => simp [hc] at he
    | inr b =>
      simp only [hc] at he
      split_ifs at he with h
      · cases he; exact h

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator
open Relation
variable {S Γ Q : Type*} (A : Alphabet S Γ)

theorem take_constant (a : Γ) (n : ℕ) : Stream'.take n (Stream'.const a) = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Stream'.take_succ,Stream'.tail_const,ih,List.replicate_succ]; rfl

theorem interpret_content (c : Tape (S := S) (Γ := Γ) (Q := Q)) :
    semanticContent (interpret A c) = Stream'.appendStream' ((c.left.reverse ++ c.right).map Tag.work) (Stream'.const A.blank) := by
  simp [semanticContent,interpret,List.map_append,List.map_reverse,Stream'.append_append_stream]

theorem semanticReturns_iff {c : Tape (S := S) (Γ := Γ) (Q := Q)} {w : List S} :
    SemanticReturns A (interpret A c) w ↔ Returns A c w := by
  refine ⟨?_,returns_interpret A⟩
  rintro ⟨tail,hh⟩
  let L := (c.left.reverse ++ c.right).map Tag.work
  let W := w.map A.input ++ [A.blank]
  have ht : semanticContent (interpret A c) = Stream'.appendStream' W tail := by
    simpa only [W,Stream'.append_append_stream,Stream'.appendStream'] using hh
  have hsmall : Stream'.take W.length (semanticContent (interpret A c)) = W := by
    rw [ht,Stream'.take_append_of_le_length _ _ _ (le_refl _),List.take_length]
  have hlarge : Stream'.take (L.length+W.length) (semanticContent (interpret A c)) = L++List.replicate W.length A.blank := by
    rw [interpret_content A,←Stream'.append_take,take_constant]
  have hp := Stream'.take_prefix_take_left W.length (L.length+W.length)
    (semanticContent (interpret A c)) (by omega)
  rw [hsmall,hlarge] at hp
  obtain ⟨rest,he⟩ := hp
  exact ⟨W.length,rest,by simpa only [W,List.append_assoc,List.singleton_append] using he.symm⟩

end FiniteAlgebraicEnvelopes.Compiler.Simulator

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral
open Turing Relation Compiler Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [DecidableEq S] [Inhabited Λ]
variable (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ)

theorem view_initial (w : List S) : OneSided.view (interpret alphabet (initialTape alphabet (wrapper M start) w)) = initial (Λ := Λ) w := by
  simp [OneSided.view,initialTape,interpret,semanticContent,filledWork,Function.comp_def,initial,wrapper,raw,alphabet,List.map_map]

omit [Inhabited Λ] in
theorem returns_final {s : SemanticTape (Gamma S) (State Λ)} {out : List S}
    (hs : OneSided.view s = final out) : SemanticReturns alphabet s out := by
  have hc := congrArg OneSided.Cfg.cell hs
  change semanticContent s = raw out at hc
  refine ⟨Stream'.const blank,?_⟩
  rw [hc]
  change Stream'.appendStream' (out.map input) (Stream'.const blank) =
    Stream'.appendStream' (out.map input) (Stream'.cons blank (Stream'.const blank))
  congr 1
  funext n
  cases n <;> rfl

 theorem realizes (stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) : Word.Realizes alphabet (wrapper M start) f := by
  intro w out
  constructor
  · intro ho
    have hfold : final (Λ := Λ) out ∈ StateTransition.eval (OneSided.step (wrapper M start)) (initial w) := by
      rw [wrapper_eval M start stop hm hM]
      exact Part.mem_map _ ho
    obtain ⟨s,hs,he⟩ := StateTransition.tr_eval (OneSided.respects (wrapper M start)) (view_initial M start w) hfold
    obtain ⟨hr,hhalt⟩ := StateTransition.mem_eval.mp he
    obtain ⟨c,hc,hcs⟩ := semanticRun_lift alphabet (wrapper M start) hr
    refine ⟨c,hc,?_,?_⟩
    · apply (semantic_halted_iff alphabet (wrapper M start) c).mp
      rw [hcs]; exact hhalt
    · apply (semanticReturns_iff alphabet).mp
      rw [hcs]
      exact returns_final hs
  · rintro ⟨c,hc,hh,ho⟩
    have he : interpret alphabet c ∈ StateTransition.eval (semanticStep (wrapper M start))
        (interpret alphabet (initialTape alphabet (wrapper M start) w)) :=
      StateTransition.mem_eval.mpr ⟨unboundedRun_interpret alphabet (wrapper M start) hc,
        (semantic_halted_iff alphabet (wrapper M start) c).mpr hh⟩
    obtain ⟨s,hs,he⟩ := StateTransition.tr_eval_rev (OneSided.respects (wrapper M start)) (view_initial M start w) he
    rw [wrapper_eval M start stop hm hM] at he
    obtain ⟨out',ho',rfl⟩ := (Part.mem_map_iff _).mp he
    have hu : out' = out := semanticReturns_unique alphabet (returns_final hs) (returns_interpret alphabet ho)
    exact hu ▸ ho'

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.MachineRealization.WordEvaluator
open Turing Compiler Compiler.Simulator FoldLiteral
variable {S : Type} [Fintype S] [Primcodable S]
/-- Every algorithmic partial word function has an actual one-sided finite
    machine with the literal first-blank readout used by the finite compiler. -/
theorem exists_machine {f : List S →. List S} (hf : Partrec f) :
    ∃ (Γ Q : Type) (_ : Fintype Γ) (_ : Fintype Q)
      (A : Alphabet S Γ) (M : Machine Q Γ),
      (∀ g a, A.output g = some a → g = A.input a) ∧ Word.Realizes A M f := by
  classical
  obtain ⟨Λ,hΛ,iΛ,M,start,stop,hm,hM⟩ := exists_safe_tape hf
  let : Fintype Λ := hΛ
  let : Inhabited Λ := iΛ
  exact ⟨Gamma S,State Λ,inferInstance,inferInstance,alphabet,wrapper M start,
    output_decode,realizes M start stop hm hM⟩

end FiniteAlgebraicEnvelopes.MachineRealization.WordEvaluator

namespace FiniteAlgebraicEnvelopes.MachineRealization.UniformCode
open Turing.ToPartrec

private theorem eval_comp (f g : Code) (v : List ℕ) :
    (Code.comp f g).eval v = (g.eval v).bind (fun w => f.eval w) := rfl

attribute [local simp] eval_comp

/-- A faithful syntactic encoding, not a choice of an evaluator for each index. -/
def quote : Code → Nat.Partrec.Code
  | .zero' => .zero
  | .succ => .succ
  | .tail => .left
  | .cons a b => .pair (quote a) (quote b)
  | .comp a b => .comp (quote a) (quote b)
  | .case a b => .prec (quote a) (quote b)
  | .fix a => .rfind' (quote a)

def unquote : Nat.Partrec.Code → Code
  | .zero => .zero'
  | .succ => .succ
  | .left => .tail
  | .right => .zero'
  | .pair a b => .cons (unquote a) (unquote b)
  | .comp a b => .comp (unquote a) (unquote b)
  | .prec a b => .case (unquote a) (unquote b)
  | .rfind' a => .fix (unquote a)

@[simp] theorem unquote_quote (c : Code) : unquote (quote c) = c := by
  induction c <;> simp_all [quote,unquote]

theorem quote_injective : Function.Injective quote :=
  Function.LeftInverse.injective unquote_quote

def numeral : ℕ → Code
  | 0 => .zero
  | n+1 => .comp .succ (numeral n)

@[simp] theorem numeral_eval (n : ℕ) (w : List ℕ) :
    (numeral n).eval w = Part.some [n] := by
  induction n with
  | zero => simp [numeral]
  | succ n ih => simp [numeral,ih]

def specialize (c : Code) (n : ℕ) : Code := .comp c (.cons (numeral n) .id)

@[simp] theorem specialize_eval (c : Code) (n : ℕ) (w : List ℕ) :
    (specialize c n).eval w = c.eval (n::w) := by
  simp [specialize]

theorem primrec_quote_numeral : Primrec (fun n => quote (numeral n)) := by
  have h : Primrec (fun n : ℕ => Nat.rec (motive := fun _ => Nat.Partrec.Code) (quote (.zero : Code))
      (fun _ c => Nat.Partrec.Code.comp .succ c) n) := by
    exact Primrec.nat_rec₁ _ (Nat.Partrec.Code.primrec₂_comp.comp
      (Primrec.const _) Primrec.snd).to₂
  apply h.of_eq
  intro n
  induction n <;> simp_all [numeral,quote]

theorem primrec_quote_specialize (c : Code) : Primrec (fun n => quote (specialize c n)) := by
  exact Nat.Partrec.Code.primrec₂_comp.comp (Primrec.const _) <|
    Nat.Partrec.Code.primrec₂_pair.comp primrec_quote_numeral (Primrec.const _)

open Encodable ListCode

/-- Parameter specialization is uniform at the literal code level. Only the
    *single* code implementing the two-variable function is selected. -/
theorem exists_parameterized {f : ℕ → List ℕ →. List ℕ} (hf : Partrec₂ f) :
    ∃ C : ℕ → Code, Primrec (fun n => quote (C n)) ∧
      ∀ n w, (C n).eval (w.map Nat.succ) = (f n w).map (List.map Nat.succ) := by
  obtain ⟨ce,hce⟩ := binary_code
    ((Computable.succ.comp (Primrec₂.natPair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const 1)) Computable.fst)).to₂)
  obtain ⟨ch,hch⟩ := unary_code
    (Computable.succ.comp (Computable.fst.comp (Primrec.unpair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1)))))
  obtain ⟨ct,hct⟩ := unary_code
    (Computable.snd.comp (Primrec.unpair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1))))
  let g : ℕ → ℕ →. ℕ := fun i n => (f i (Denumerable.ofNat (List ℕ) n).reverse).map
    (fun l => encode l.reverse)
  have hg : Partrec₂ g :=
    ((hf.comp Computable.fst
      (Computable.list_reverse.comp ((Computable.ofNat (List ℕ)).comp Computable.snd))).map
      ((Computable.encode.comp Computable.list_reverse).comp Computable.snd).to₂).to₂
  obtain ⟨cf,hcf⟩ := Code.exists_code (Nat.Partrec'.part_iff₂.mpr hg)
  refine ⟨fun n => .comp (decoder ch ct) (.comp (specialize cf n) (encoder ce)),?_,?_⟩
  · exact Nat.Partrec.Code.primrec₂_comp.comp (Primrec.const _) <|
      Nat.Partrec.Code.primrec₂_comp.comp (primrec_quote_specialize cf) (Primrec.const _)
  · intro n w
    simp only [eval_comp,encoder_eval ce hce,Part.bind_some]
    rw [specialize_eval,hcf ⟨[n,encode w.reverse],rfl⟩]
    change ((g n (encode w.reverse)).map (fun n => [n])).bind (fun v => (decoder ch ct).eval v) = _
    simp only [g,Denumerable.ofNat_encode,List.reverse_reverse]
    apply Part.ext
    intro out
    simp only [Part.mem_bind_iff,Part.mem_map_iff]
    constructor
    · rintro ⟨_,⟨m,⟨l,hl,rfl⟩,rfl⟩,hd⟩
      have he := decoder_eval ch ct hch hct l.reverse []
      simp only [List.reverse_reverse,List.append_nil] at he
      rw [he,Part.mem_some_iff] at hd
      exact ⟨l,hl,hd.symm⟩
    · rintro ⟨l,hl,rfl⟩
      refine ⟨[encode l.reverse],⟨encode l.reverse,⟨l,hl,rfl⟩,rfl⟩,?_⟩
      rw [decoder_eval ch ct hch hct l.reverse []]
      simp

 theorem exists_word_parameterized {S : Type} [Primcodable S]
    {f : ℕ → List S →. List S} (hf : Partrec₂ f) :
    ∃ C : ℕ → Code, Primrec (fun n => quote (C n)) ∧ ∀ n w,
      (C n).eval (w.map (fun s => encode s + 1)) =
        (f n w).map (List.map (fun s => encode s + 1)) := by
  let g : ℕ → List ℕ →. List ℕ := fun n ns =>
    (f n (ns.filterMap Encodable.decode)).map (List.map Encodable.encode)
  have hg : Partrec₂ g :=
    ((hf.comp Computable.fst
      ((Primrec.listFilterMap Primrec.id (Primrec.decode.comp Primrec.snd).to₂).to_comp.comp Computable.snd)).map
      ((Primrec.list_map Primrec.id (Primrec.encode.comp Primrec.snd).to₂).to_comp.comp Computable.snd).to₂).to₂
  obtain ⟨C,hC,h⟩ := exists_parameterized hg
  refine ⟨C,hC,fun n w => ?_⟩
  have hh := h n (w.map encode)
  have hlist : (w.map encode).filterMap decode = w := by
    induction w <;> simp_all
  simpa only [g,hlist,Part.map_map,List.map_map,Function.comp_def,Nat.succ_eq_add_one] using hh

end FiniteAlgebraicEnvelopes.MachineRealization.UniformCode

namespace FiniteAlgebraicEnvelopes.WordProgramming
open Encodable
variable {S : Type} [Primcodable S]

/-- An acceptable word-program numbering obtained from the pinned universal
    partial-recursive evaluator. Invalid decoded results remain undefined. -/
def eval (c : Nat.Partrec.Code) (w : List S) : Part (List S) :=
  (c.eval (encode w)).bind (fun n => Part.ofOption (decode n))

theorem partrec_eval : Partrec₂ (eval (S := S)) :=
  ((Nat.Partrec.Code.eval_part.comp Computable.fst
    (Computable.encode.comp Computable.snd)).bind
      ((Computable.decode.comp Computable.snd).ofOption).to₂).to₂

/-- The source fixed-point equation for word algorithms, as literal equality of
    partial functions, including their domains. -/
theorem fixed_point {F : Nat.Partrec.Code → List S →. List S}
    (hF : Partrec₂ F) : ∃ c, eval c = F c := by
  let G : Nat.Partrec.Code → ℕ →. ℕ := fun c n =>
    (F c ((decode n).getD [])).map encode
  have hG : Partrec₂ G := by
    exact ((hF.comp Computable.fst
      ((Computable.option_getD (Computable.decode.comp Computable.snd)
        (Computable.const [])))).map (Computable.encode.comp Computable.snd).to₂).to₂
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.fixed_point₂ hG
  refine ⟨c,?_⟩
  funext w
  simp only [eval,hc,G,encodek,Option.getD_some]
  apply Part.ext
  intro out
  simp [encodek]

end FiniteAlgebraicEnvelopes.WordProgramming

namespace FiniteAlgebraicEnvelopes.MachineRealization.CodeMachine
open Turing Turing.ToPartrec Turing.PartrecToTM2 StackLift RawTM StackTape

variable (S : Type) [Fintype S] [Primcodable S] [DecidableEq S]

/-- A literal raw-letter stack program, with its finite control part. -/
structure Raw where
  Q : Type
  finiteQ : Fintype Q
  start : Q
  code : Q → TM2.Stmt (fun _ : K' => Symbol S) Q (Store S)

attribute [instance] Raw.finiteQ

noncomputable def raw (c : Code) : Raw S := by
  classical
  let A := codeSupp c Cont'.halt
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hs : TM2.Supports tr A := tr_supports c Cont'.halt
  let start : {l // l ∈ A} := ⟨trNormal c Cont'.halt,hs.1⟩
  let M := FiniteTM2.machine tr A hs
  exact ⟨StackLift.Label S {l // l ∈ A},inferInstance,.pre,
    RawTM.machine (WordEvaluator.bound (S := S)) M start⟩

omit [DecidableEq S] in
theorem raw_correct (c : Code) {f : List S →. List S}
    (hc : ∀ w, c.eval (numbers w) = (f w).map numbers) (w : List S) :
    StateTransition.eval (TM2.step (raw S c).code)
      ⟨some (raw S c).start,none,tracks w.reverse []⟩ =
        (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩) := by
  classical
  let : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  unfold raw
  apply eval_pre (WordEvaluator.bound (S := S)) _ _ WordEvaluator.le_bound
  apply part_map_injective (FiniteTM2.embedCfg_injective (codeSupp c Cont'.halt))
  refine (FiniteTM2.eval_embed (Γ := fun _ : K' => Γ') tr
    (codeSupp c Cont'.halt) (tr_supports c Cont'.halt) _).symm.trans ?_
  change StateTransition.eval (TM2.step tr) (init c (numbers w)) = _
  rw [tr_eval,hc]
  simp only [Part.map_eq_map,Part.map_map]
  rfl

/-- A finite tape machine with distinguished literal input/output states. -/
structure TapeProgram where
  Q : Type
  finiteQ : Fintype Q
  [inhabitedQ : Inhabited Q]
  start : Q
  stop : Q
  code : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Q
  safe : TapeSafety.Preserves code

attribute [instance] TapeProgram.finiteQ TapeProgram.inhabitedQ

noncomputable def tapeProgram (R : Raw S) : TapeProgram S := by
  classical
  letI : Inhabited R.Q := ⟨R.start⟩
  let N := TM2to1.tr R.code
  let P := TM1to0.tr N
  let B := TM2to1.trSupp R.code Finset.univ
  have hU : TM2.Supports R.code Finset.univ := by
    refine ⟨Finset.mem_univ _,fun q _ => ?_⟩
    induction R.code q <;> simp_all [TM2.SupportsStmt]
  have hB : TM1.Supports N B := TM2to1.tr_supports R.code hU
  let C := TM1to0.trStmts N B
  have hC : TM0.Supports P (C : Set _) := TM1to0.tr_supports N hB
  have hs : (none,none) ∈ C := by
    change (none,none) ∈ (TM1.stmts N B) ×ˢ (Finset.univ : Finset (Store S))
    exact Finset.mem_product.mpr ⟨Finset.none_mem_insertNone,Finset.mem_univ _⟩
  letI : Inhabited {l // l ∈ C} := ⟨⟨default,hC.1⟩⟩
  exact ⟨{l // l ∈ C},inferInstance,⟨default,hC.1⟩,⟨(none,none),hs⟩,
    FiniteTM0.machine P C hC,
    TapeSafety.finite_preserves N B hB (TapeSafety.safe_tr R.code)⟩

omit [Primcodable S] [DecidableEq S] in
theorem tapeProgram_correct (R : Raw S) {f : List S →. List S}
    (hR : ∀ w, StateTransition.eval (TM2.step R.code)
      ⟨some R.start,none,tracks w.reverse []⟩ =
        (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩)) (w : List S) :
    StateTransition.eval (TM0.step (tapeProgram S R).code)
      ⟨(tapeProgram S R).start,tape w⟩ =
        (f w).map (fun out => ⟨(tapeProgram S R).stop,tape out⟩) := by
  classical
  let : Inhabited R.Q := ⟨R.start⟩
  let tI := (tapeProgram S R).inhabitedQ
  change Inhabited {l // l ∈ TM1to0.trStmts (TM2to1.tr R.code) (TM2to1.trSupp R.code Finset.univ)} at tI
  unfold tapeProgram
  apply part_map_injective (FiniteTM0.embed_injective _)
  rw [←FiniteTM0.eval_embed]
  change StateTransition.eval (TM0.step (TM1to0.tr (TM2to1.tr R.code)))
    (TM1to0.trCfg (TM2to1.tr R.code) ⟨some (.normal R.start),none,tape w⟩) = _
  rw [eval_post R.code R.start hR]
  simp only [Part.map_map]
  rfl

noncomputable def compile (c : Code) :
    Compiler.Simulator.Machine (FoldLiteral.State (tapeProgram S (raw S c)).Q)
      (FoldLiteral.Gamma S) := by
  let T := tapeProgram S (raw S c)
  exact FoldLiteral.wrapper T.code T.start

theorem compile_correct (c : Code) {f : List S →. List S}
    (hc : ∀ w, c.eval (numbers w) = (f w).map numbers) :
    Compiler.Word.Realizes FoldLiteral.alphabet (compile S c) f := by
  let T := tapeProgram S (raw S c)
  exact FoldLiteral.realizes T.code T.start T.stop T.safe
    (tapeProgram_correct S (raw S c) (raw_correct S c hc))

/-- One uniform syntactic program transformation feeds the *specified* model
    compiler. No evaluator is selected separately at each parameter. -/
theorem exists_family {f : ℕ → List S →. List S} (hf : Partrec₂ f) :
    ∃ C : ℕ → Code, Primrec (fun n => UniformCode.quote (C n)) ∧
      ∀ n, Compiler.Word.Realizes FoldLiteral.alphabet (compile S (C n)) (f n) := by
  obtain ⟨C,hC,h⟩ := UniformCode.exists_word_parameterized hf
  exact ⟨C,hC,fun n => compile_correct S (C n) (h n)⟩

end FiniteAlgebraicEnvelopes.MachineRealization.CodeMachine

end OAI
