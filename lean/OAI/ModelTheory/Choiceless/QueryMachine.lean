import OAI.ModelTheory.Choiceless.Matrix

namespace OAI

namespace CPTSeparation.TableMachine

open CounterLang

variable {V : Type}

local infixr:60 " ;; " => CounterLang.Program.seq

def headerConsume : Prog V := .atom (.consume (fun c a => (a == some none,c.2)))

def headerBody : Prog V :=
 .atom (.inc .size) ;; .atom (.inc .width) ;; .atom (.inc .width) ;; headerConsume

def headerLoop : Prog V := .loop (fun c => c.1) headerBody

def header : Prog V := headerConsume ;; headerLoop

def headerNums (k : ℕ) : Reg → ℕ := fun r => match r with
 | .size => k
 | .width => k+k
 | _ => 0

def headerState (v : V) (k n : ℕ) (w out : List Letter) : CState V :=
 ⟨(n != 0,v),headerNums k, if n = 0 then w else List.replicate (n-1) none ++ some 0 :: w,out⟩

lemma headerNums_inc (k : ℕ) :
 Function.update (Function.update (Function.update (headerNums k) .size (k+1)) .width (k+k+1)) .width (k+k+1+1) =
 headerNums (k+1) := by
 funext r
 cases r <;> simp [headerNums,Function.update] ; omega

lemma headerBody_runs (v : V) (k n : ℕ) (w out : List Letter) :
 Runs (headerBody (V := V)) (headerState v k (n+1) w out) (headerState v (k+1) n w out) 7 := by
 let s := headerState v k (n+1) w out
 have h := (Runs.atom (.inc .size) s).seq
   ((Runs.atom (.inc .width) ((Atom.inc .size).eval s)).seq
   ((Runs.atom (.inc .width) ((Atom.inc .width).eval ((Atom.inc .size).eval s))).seq
    (Runs.atom (.consume (fun c a => (a == some none,c.2)))
      ((Atom.inc .width).eval ((Atom.inc .width).eval ((Atom.inc .size).eval s))))))
 have he : (Atom.consume (fun c a => (a == some none,c.2))).eval
     ((Atom.inc .width).eval ((Atom.inc .width).eval ((Atom.inc .size).eval s))) =
     headerState v (k+1) n w out := by
   cases n <;> simp [s,headerState,Atom.eval,headerNums,Function.update,List.replicate_succ,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
   all_goals funext r; cases r <;> simp [headerNums,Function.update] ; omega
 simpa only [headerBody,headerConsume,Atom.cost,he] using h

lemma headerLoop_runs (v : V) (k n : ℕ) (w out : List Letter) :
 Runs headerLoop (headerState v k n w out)
   (⟨(false,v),headerNums (k+n),w,out⟩ : CState V) (8*n+1) := by
 induction n generalizing k with
 | zero =>
   simpa [headerState,headerLoop] using (Runs.loop_false (a := headerBody) (f := fun c : Bool × V => c.1)
      (s := headerState v k 0 w out) rfl)
 | succ n ih =>
   have h := Runs.loop_true (f := fun c : Bool × V => c.1)
     (s := headerState v k (n+1) w out) (by simp [headerState])
     (headerBody_runs v k n w out) (ih (k+1))
   simpa only [headerLoop, show k+1+n = k+(n+1) by omega,
     show 1+(7+(8*n+1)) = 8*(n+1)+1 by omega] using h

lemma header_runs (v : V) (n : ℕ) (w out : List Letter) :
 Runs header (⟨(false,v),headerNums 0,List.replicate n none ++ some 0::w,out⟩ : CState V)
   (⟨(false,v),headerNums n,w,out⟩ : CState V) (8*n+3) := by
 let s : CState V := ⟨(false,v),headerNums 0,List.replicate n none ++ some 0::w,out⟩
 have he : (Atom.consume (fun c a => (a == some none,c.2))).eval s = headerState v 0 n w out := by
   cases n <;> simp [s,headerState,Atom.eval,List.replicate_succ]
 have hc : Runs headerConsume s (headerState v 0 n w out) 1 := by
   simpa only [headerConsume,he,Atom.cost] using Runs.atom (.consume (fun c a => (a == some none,c.2))) s
 have h := hc.seq (headerLoop_runs v 0 n w out)
 simpa only [header,s,Nat.zero_add,show 1+(1+(8*n+1)) = 8*n+3 by omega] using h

end CPTSeparation.TableMachine

namespace CPTSeparation.StackLang

open Macros

variable {K L α σ τ : Type} [DecidableEq K] [DecidableEq L]

@[simp] lemma update_sum_left (f : K → List α) (g : L → List α) (k : K) (xs : List α) :
 Function.update (Sum.elim f g) (.inl k) xs = Sum.elim (Function.update f k xs) g := by
 funext j; cases j <;> simp [Function.update]

@[simp] lemma update_sum_right (f : K → List α) (g : L → List α) (k : L) (xs : List α) :
 Function.update (Sum.elim f g) (.inr k) xs = Sum.elim f (Function.update g k xs) := by
 funext j; cases j <;> simp [Function.update]

def leftStore (s : SStore K α σ) (v : τ) (g : L → List α) : SStore (K ⊕ L) α (σ × τ) :=
 ⟨(s.control.1,(s.control.2,v)),Sum.elim s.stk g⟩

def Action.frameLeft : Action (fun _ : K => α) (Option α × σ) →
 Action (fun _ : K ⊕ L => α) (Option α × (σ × τ))
 | .done => .done
 | .push k f a => .push (.inl k) (fun c => f (c.1,c.2.1)) a.frameLeft
 | .peek k f a => .peek (.inl k) (fun c b => let r := f (c.1,c.2.1) b; (r.1,(r.2,c.2.2))) a.frameLeft
 | .pop k f a => .pop (.inl k) (fun c b => let r := f (c.1,c.2.1) b; (r.1,(r.2,c.2.2))) a.frameLeft
 | .load f a => .load (fun c => let r := f (c.1,c.2.1); (r.1,(r.2,c.2.2))) a.frameLeft
 | .branch f a b => .branch (fun c => f (c.1,c.2.1)) a.frameLeft b.frameLeft

lemma Action.run_frameLeft (a : Action (fun _ : K => α) (Option α × σ))
 (s : SStore K α σ) (v : τ) (g : L → List α) :
 a.frameLeft.run (leftStore s v g) = leftStore (a.run s) v g := by
 induction a generalizing s with
 | done => rfl
 | push k f a ih => simpa only [frameLeft,run,leftStore,Sum.elim_inl,update_sum_left,Prod.mk.eta] using ih ⟨s.control,Function.update s.stk k (f s.control::s.stk k)⟩
 | peek k f a ih => simpa only [frameLeft,run,leftStore,Sum.elim_inl,update_sum_left,Prod.mk.eta] using ih ⟨f s.control (s.stk k).head?,s.stk⟩
 | pop k f a ih => simpa only [frameLeft,run,leftStore,Sum.elim_inl,update_sum_left,Prod.mk.eta] using ih ⟨f s.control (s.stk k).head?,Function.update s.stk k (s.stk k).tail⟩
 | load f a ih => simpa only [frameLeft,run,leftStore,Sum.elim_inl,update_sum_left,Prod.mk.eta] using ih ⟨f s.control,s.stk⟩
 | branch f a b iha ihb =>
   cases h : f s.control
   · simpa only [frameLeft,run,leftStore,Prod.mk.eta,h,Bool.false_eq_true,ite_false] using ihb s
   · simpa only [frameLeft,run,leftStore,Prod.mk.eta,h,ite_true] using iha s

def Program.frameLeft : SProgram K α σ → SProgram (K ⊕ L) α (σ × τ)
 | .atom a => .atom a.frameLeft
 | .seq a b => .seq a.frameLeft b.frameLeft
 | .cond f a b => .cond (fun c => f (c.1,c.2.1)) a.frameLeft b.frameLeft
 | .loop f a => .loop (fun c => f (c.1,c.2.1)) a.frameLeft

noncomputable def Exec.frameLeft {p : SProgram K α σ} {s t} {n} (h : Exec p s n t)
 (v : τ) (g : L → List α) : Exec p.frameLeft (leftStore s v g) n (leftStore t v g) := by
 induction h with
 | atom a s => simpa only [Program.frameLeft,Action.run_frameLeft] using Exec.atom a.frameLeft (leftStore s v g)
 | seq ha hb iha ihb => exact .seq iha ihb
 | cond_true hf ha ih => exact .cond_true hf ih
 | cond_false hf ha ih => exact .cond_false hf ih
 | loop_false hf => exact .loop_false hf
 | loop_true hf ha hb iha ihb => exact .loop_true hf iha ihb

lemma Runs.frameLeft {p : SProgram K α σ} {s t} {n} (h : Runs p s t n)
 (v : τ) (g : L → List α) : Runs p.frameLeft (leftStore s v g) (leftStore t v g) n := by
 obtain ⟨m,hm,⟨h⟩⟩ := h
 exact ⟨m,hm,⟨h.frameLeft v g⟩⟩

def rightStore (s : SStore K α σ) (v : τ) (g : L → List α) : SStore (L ⊕ K) α (τ × σ) :=
 ⟨(s.control.1,(v,s.control.2)),Sum.elim g s.stk⟩

def Action.frameRight : Action (fun _ : K => α) (Option α × σ) →
 Action (fun _ : L ⊕ K => α) (Option α × (τ × σ))
 | .done => .done
 | .push k f a => .push (.inr k) (fun c => f (c.1,c.2.2)) a.frameRight
 | .peek k f a => .peek (.inr k) (fun c b => let r := f (c.1,c.2.2) b; (r.1,(c.2.1,r.2))) a.frameRight
 | .pop k f a => .pop (.inr k) (fun c b => let r := f (c.1,c.2.2) b; (r.1,(c.2.1,r.2))) a.frameRight
 | .load f a => .load (fun c => let r := f (c.1,c.2.2); (r.1,(c.2.1,r.2))) a.frameRight
 | .branch f a b => .branch (fun c => f (c.1,c.2.2)) a.frameRight b.frameRight

lemma Action.run_frameRight (a : Action (fun _ : K => α) (Option α × σ))
 (s : SStore K α σ) (v : τ) (g : L → List α) :
 a.frameRight.run (rightStore s v g) = rightStore (a.run s) v g := by
 induction a generalizing s with
 | done => rfl
 | push k f a ih => simpa only [frameRight,run,rightStore,Sum.elim_inr,update_sum_right,Prod.mk.eta] using ih ⟨s.control,Function.update s.stk k (f s.control::s.stk k)⟩
 | peek k f a ih => simpa only [frameRight,run,rightStore,Sum.elim_inr,update_sum_right,Prod.mk.eta] using ih ⟨f s.control (s.stk k).head?,s.stk⟩
 | pop k f a ih => simpa only [frameRight,run,rightStore,Sum.elim_inr,update_sum_right,Prod.mk.eta] using ih ⟨f s.control (s.stk k).head?,Function.update s.stk k (s.stk k).tail⟩
 | load f a ih => simpa only [frameRight,run,rightStore,Sum.elim_inr,update_sum_right,Prod.mk.eta] using ih ⟨f s.control,s.stk⟩
 | branch f a b iha ihb =>
   cases h : f s.control
   · simpa only [frameRight,run,rightStore,Prod.mk.eta,h,Bool.false_eq_true,ite_false] using ihb s
   · simpa only [frameRight,run,rightStore,Prod.mk.eta,h,ite_true] using iha s

def Program.frameRight : SProgram K α σ → SProgram (L ⊕ K) α (τ × σ)
 | .atom a => .atom a.frameRight
 | .seq a b => .seq a.frameRight b.frameRight
 | .cond f a b => .cond (fun c => f (c.1,c.2.2)) a.frameRight b.frameRight
 | .loop f a => .loop (fun c => f (c.1,c.2.2)) a.frameRight

noncomputable def Exec.frameRight {p : SProgram K α σ} {s t} {n} (h : Exec p s n t)
 (v : τ) (g : L → List α) : Exec p.frameRight (rightStore s v g) n (rightStore t v g) := by
 induction h with
 | atom a s => simpa only [Program.frameRight,Action.run_frameRight] using Exec.atom a.frameRight (rightStore s v g)
 | seq ha hb iha ihb => exact .seq iha ihb
 | cond_true hf ha ih => exact .cond_true hf ih
 | cond_false hf ha ih => exact .cond_false hf ih
 | loop_false hf => exact .loop_false hf
 | loop_true hf ha hb iha ihb => exact .loop_true hf iha ihb

lemma Runs.frameRight {p : SProgram K α σ} {s t} {n} (h : Runs p s t n)
 (v : τ) (g : L → List α) : Runs p.frameRight (rightStore s v g) (rightStore t v g) n := by
 obtain ⟨m,hm,⟨h⟩⟩ := h
 exact ⟨m,hm,⟨h.frameRight v g⟩⟩

end CPTSeparation.StackLang

namespace CPTSeparation.QueryMachine

open StackLang StackLang.Macros

abbrev Letter := CounterLang.Letter

abbrev LeftReg := CounterLang.Reg TableMachine.Reg

abbrev Reg := LeftReg ⊕ GaussMachine.Reg

abbrev Local := (Bool × MatrixProgram.Control) × GaussMachine.Local

abbrev Prog := SProgram Reg Letter Local

def initialLocal : Local := ((false,MatrixProgram.ctrl false),(none,GaussMachine.ctrl 0 true))

def cs (n : ℕ) (input output : List Letter) : TableMachine.CState MatrixProgram.Control :=
 ⟨(false,MatrixProgram.ctrl false),TableMachine.headerNums n,input,output⟩

def combined (s : TableMachine.CState MatrixProgram.Control) (c : GaussMachine.Control)
 (d : GaussMachine.Data) : SStore Reg Letter Local := leftStore s.encode (none,c) d.tapes

def build : TableMachine.Prog MatrixProgram.Control :=
 .seq TableMachine.header MatrixProgram.program.compile

def transfers : Prog :=
 .seq (moveRev (.inl .output) (.inr .mat) (fun _ a => a))
   (moveRev (.inl (.reg .width)) (.inr .width) (fun _ a => a))

def finish : Prog :=
 .seq (clear (.inl .input))
 (.seq (clear (.inl (.reg .size)))
 (.atom (.load (fun _ => (none,initialLocal)) .done)))

def program : Prog :=
 .seq build.compile.frameLeft
 (.seq transfers (.seq GaussMachine.solver.frameRight finish))

def finalStore (b : Bool) : SStore Reg Letter Local :=
 state initialLocal none (Function.update (fun _ => []) (.inr .output) (GaussMachine.boolCode b))

lemma cs_ready (n : ℕ) (input output : List Letter) :
 Bounded.Ready ∅ n (cs n input output) := by
 simp [Bounded.Ready,cs,TableMachine.headerNums]

lemma build_runs {N} (S : OrderedQuery.Data N) :
 CounterLang.Runs build (cs 0 (TableMachine.code ⟨N,S⟩) [])
   (cs N (TableMachine.tableInput S) (SerialGaussian.payload (SerialGaussian.queryRows S)).reverse)
   (8*N+4+MatrixProgram.program.time N (TableMachine.tableInput S).length) := by
 have hh := TableMachine.header_runs (MatrixProgram.ctrl false) N (TableMachine.tableInput S) []
 have hb := Bounded.compile_runs MatrixProgram.program ∅ MatrixProgram.program_wf N
   (cs N (TableMachine.tableInput S) []) (cs_ready _ _ _)
 rw [Bounded.Program.eval_interpret,MatrixProgram.program_spec] at hb
 simp only [cs, MatrixProgram.matrix_input, List.append_nil] at hb
 have h := hh.seq hb
 convert h using 1 <;> first | rfl | omega

lemma transfers_runs (s : TableMachine.CState MatrixProgram.Control) (n : ℕ) (xs : List Letter)
 (hs : s.output = xs.reverse) (hw : s.nums .width=n) :
 Runs transfers (combined s (GaussMachine.ctrl 0 true) {})
   (combined {s with output := [], nums := Function.update s.nums .width 0}
     (GaussMachine.ctrl 0 true) {mat := xs,width := List.replicate n none})
   (2*xs.length+2*n+7) := by
 let d : GaussMachine.Data := {}
 let w := Sum.elim s.data.tapes d.tapes
 have h₁ := moveRev_runs (.inl CounterLang.Reg.output : Reg) (.inr .mat) (by simp)
   (fun (_ : Local) a => a) (s.ctl,(none,GaussMachine.ctrl 0 true)) none w xs.reverse []
 have h₂ := moveRev_runs (.inl (CounterLang.Reg.reg TableMachine.Reg.width) : Reg) (.inr .width)
   (by simp) (fun (_ : Local) a => a) (s.ctl,(none,GaussMachine.ctrl 0 true)) none
   (Sum.elim ({s.data with output := []}).tapes ({mat := xs} : GaussMachine.Data).tapes)
   (List.replicate n none) []
 have h₁' : Runs (moveRev (.inl .output : Reg) (.inr .mat) (fun (_ : Local) a => a))
   (combined s (GaussMachine.ctrl 0 true) {})
   (combined {s with output := []} (GaussMachine.ctrl 0 true) {mat := xs})
   (2*xs.length+3) := by
   simpa [w,d,combined,leftStore,CounterLang.State.encode,CounterLang.State.data,state,
     hs] using h₁
 have h₂' : Runs (moveRev (.inl (.reg .width) : Reg) (.inr .width) (fun (_ : Local) a => a))
   (combined {s with output := []} (GaussMachine.ctrl 0 true) {mat := xs})
   (combined {s with output := [],nums := Function.update s.nums .width 0}
     (GaussMachine.ctrl 0 true) {mat := xs,width := List.replicate n none}) (2*n+3) := by
   simpa [combined,leftStore,CounterLang.State.encode,CounterLang.State.data,state,
    CounterLang.unary_update,←hw,CounterLang.unary] using h₂
 convert h₁'.seq h₂' using 1 <;> first | rfl | omega

lemma solver_framed {n} (s : TableMachine.CState MatrixProgram.Control)
 (rs : List (SerialGaussian.Row n)) :
 Runs GaussMachine.solver.frameRight
   (combined s (GaussMachine.ctrl 0 true) {mat := SerialGaussian.payload rs,width := List.replicate n none})
   (combined s (GaussMachine.ctrl 0 (SerialGaussian.solve rs)) {output := GaussMachine.boolCode (SerialGaussian.solve rs)})
   (300*(rs.length+1)*(n+3)^2) := by
 exact (GaussMachine.solver_runs {} rs).frameRight s.ctl s.data.tapes

lemma finish_runs (n : ℕ) (input : List Letter) (b : Bool) :
 Runs finish
   (combined {cs n input [] with nums := Function.update (TableMachine.headerNums n) .width 0}
     (GaussMachine.ctrl 0 b) {output := GaussMachine.boolCode b})
   (finalStore b) (2*input.length+2*n+9) := by
 let s := {cs n input [] with nums := Function.update (TableMachine.headerNums n) .width 0}
 let d : GaussMachine.Data := {output := GaussMachine.boolCode b}
 let w := Sum.elim s.data.tapes d.tapes
 let v : Local := (s.ctl,(none,GaussMachine.ctrl 0 b))
 have h₁ := clear_runs (.inl CounterLang.Reg.input : Reg) v none w input
 have h₂ := clear_runs (.inl (CounterLang.Reg.reg TableMachine.Reg.size) : Reg) v none
   (Function.update w (.inl .input) []) (List.replicate n none)
 have h₁' : Runs (clear (.inl CounterLang.Reg.input : Reg)) (combined s (GaussMachine.ctrl 0 b) d)
   (state v none (Function.update w (.inl .input) [])) (2*input.length+3) := by
   simpa [w,v,combined,leftStore,CounterLang.State.encode,CounterLang.State.data,state,s,cs] using h₁
 have h₂' : Runs (clear (.inl (CounterLang.Reg.reg TableMachine.Reg.size) : Reg))
   (state v none (Function.update w (.inl .input) []))
   (state v none (Function.update (fun _ => []) (.inr .output) (GaussMachine.boolCode b))) (2*n+3) := by
   convert h₂ using 1
   · refine Store.ext' (by rfl) ?_
     funext k; cases k with
     | inl k => cases k with
       | reg r => cases r <;> simp [state,w,s,CounterLang.State.data,CounterLang.Data.tapes,CounterLang.unary,cs,TableMachine.headerNums,Function.update]
       | _ => simp [state,w,s,CounterLang.State.data,CounterLang.Data.tapes,cs]
     | inr k => simp [state,w]
   · refine Store.ext' (by rfl) ?_
     funext k; cases k with
     | inl k => cases k with
       | reg r => cases r <;> simp [state,w,s,CounterLang.State.data,CounterLang.Data.tapes,CounterLang.unary,cs,TableMachine.headerNums,Function.update]
       | _ => simp [state,w,s,CounterLang.State.data,CounterLang.Data.tapes,cs,Function.update]
     | inr k => cases k <;> simp [state,w,d,GaussMachine.Data.tapes,Function.update]
   · simp
 have h₃ : Runs (.atom (.load (fun _ : Option Letter × Local => (none,initialLocal)) .done))
   (state v none (Function.update (fun _ => []) (.inr .output) (GaussMachine.boolCode b)))
   (finalStore b) 1 := Runs.atom_of _ _ _ rfl
 convert h₁'.seq (h₂'.seq h₃) using 1 <;> first | rfl | omega

def time (N : ℕ) : ℕ :=
 MatrixProgram.program.time N (8*(N*N)) + 2*(N+N*N)*(N+N+2) +
 300*(N+N*N+1)*(N+N+3)^2 + 14*N+16*(N*N)+23

lemma program_runs {N} (S : OrderedQuery.Data N) :
 Runs program (combined (cs 0 (TableMachine.code ⟨N,S⟩) []) (GaussMachine.ctrl 0 true) {})
   (finalStore (SerialGaussian.solve (SerialGaussian.queryRows S))) (time N) := by
 have h₁ := (build_runs S).compiles.frameLeft ((none,GaussMachine.ctrl 0 true) : GaussMachine.Local)
   ({} : GaussMachine.Data).tapes
 have h₂ := transfers_runs
   (cs N (TableMachine.tableInput S) (SerialGaussian.payload (SerialGaussian.queryRows S)).reverse)
   (N+N) (SerialGaussian.payload (SerialGaussian.queryRows S)) rfl rfl
 have h₃ := solver_framed
   ({cs N (TableMachine.tableInput S) [] with nums := Function.update (TableMachine.headerNums N) .width 0})
   (SerialGaussian.queryRows S)
 have h₄ := finish_runs N (TableMachine.tableInput S) (SerialGaussian.solve (SerialGaussian.queryRows S))
 have h := h₁.seq (h₂.seq (h₃.seq h₄))
 convert h using 1
 · rfl
 · rfl
 · simp only [time,TableMachine.tableInput_length,SerialGaussian.payload_length,
     SerialGaussian.queryRows,List.length_map,OrderedQuery.rows_length]
   ring

lemma time_polynomial : ∃ p : Polynomial ℕ, ∀ N, time N = p.eval N := by
 obtain ⟨p,hp⟩ := Bounded.Program.time_polynomial MatrixProgram.program
 refine ⟨p + 2*(Polynomial.X+Polynomial.X^2)*(2*Polynomial.X+2) +
  300*(Polynomial.X+Polynomial.X^2+1)*(2*Polynomial.X+3)^2 +
  14*Polynomial.X+16*Polynomial.X^2+23, ?_⟩
 intro N
 simp [time,hp]
 ring

open StackLang StackLang.Macros

open Turing StateTransition

def includeLetter : OrderedQuery.Alphabet → Letter
 | none => none
 | some b => TableMachine.bitLetter b

def projectLetter : Letter → OrderedQuery.Alphabet
 | none => none
 | some a => some (a == 1)

@[simp] lemma project_include (a : OrderedQuery.Alphabet) : projectLetter (includeLetter a) = a := by
 cases a with
 | none => rfl
 | some b => cases b <;> decide

lemma code_map (S : OrderedQuery.OrderedInput) :
 TableMachine.code S = (OrderedQuery.encode S).map includeLetter := by
 simp [TableMachine.code,OrderedQuery.encode,TableMachine.tableInput,List.map_map,includeLetter,
   TableMachine.bitLetter,Function.comp_def]

@[simp] lemma code_length (S : OrderedQuery.OrderedInput) :
 (TableMachine.code S).length = S.1+1+8*(S.1*S.1) := by
 rw [code_map,List.length_map,OrderedQuery.encode_length]

lemma code_decode (S : OrderedQuery.OrderedInput) :
 OrderedQuery.decode ((TableMachine.code S).map projectLetter) = S := by
 rw [code_map,List.map_map]
 rw [show projectLetter ∘ includeLetter = id from funext project_include,List.map_id]
 exact OrderedQuery.decode_encode S

lemma code_injective : Function.Injective TableMachine.code := by
 intro S T h
 simpa only [code_decode] using congrArg (fun w => OrderedQuery.decode (w.map projectLetter)) h

def encoding : Computability.Encoding OrderedQuery.OrderedInput Letter :=
 ⟨TableMachine.code,fun w => some (OrderedQuery.decode (w.map projectLetter)),fun S => by simp [code_decode]⟩

def answer (S : OrderedQuery.OrderedInput) : Bool := SerialGaussian.solve (SerialGaussian.queryRows S.2)

lemma answer_correct (S : OrderedQuery.OrderedInput) : answer S = true ↔ S.2.query :=
 SerialGaussian.queryRows_correct S.2

noncomputable def machine : FinTM2 :=
 program.machine (.inl .input) (.inr .output) (none,initialLocal)

lemma initial_configuration (S : OrderedQuery.OrderedInput) :
 configuration (some program.start)
   (combined (cs 0 (TableMachine.code S) []) (GaussMachine.ctrl 0 true) {}) =
 initList machine (TableMachine.code S) := by
 suffices h : (configuration (some program.start)
   (combined (cs 0 (TableMachine.code S) []) (GaussMachine.ctrl 0 true) {})).stk =
   (initList machine (TableMachine.code S)).stk by
   exact congrArg (Turing.TM2.Cfg.mk (some program.start) (none,initialLocal)) h
 funext k
 cases k with
 | inl k => cases k with
     | reg r => cases r <;> simp [configuration,combined,leftStore,CounterLang.State.encode,
       state,CounterLang.State.data,CounterLang.Data.tapes,CounterLang.unary,cs,TableMachine.headerNums,
       initList,machine,Program.machine]
     | _ => simp [configuration,combined,leftStore,CounterLang.State.encode,
       state,CounterLang.State.data,CounterLang.Data.tapes,cs,initList,machine,Program.machine] <;> rfl
 | inr k => cases k <;> simp [configuration,combined,leftStore,GaussMachine.Data.tapes,
       initList,machine,Program.machine]

lemma final_configuration (b : Bool) : configuration (Λ := program.Labels) none (finalStore b) =
 haltList machine (GaussMachine.boolCode b) := by
 suffices h : (finalStore b).stk = (haltList machine (GaussMachine.boolCode b)).stk by
   exact congrArg (Turing.TM2.Cfg.mk none (none,initialLocal)) h
 funext k
 simp only [finalStore,state,haltList,machine,Program.machine]
 by_cases h : k = Sum.inr GaussMachine.Reg.output
 · subst k; simp [Function.update]; rfl
 · simp [h,Function.update]

lemma polynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq => simpa only [Polynomial.eval_add] using add_le_add hp hq
 | monomial n c => simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

noncomputable def polynomialAlgorithm :
 TM2ComputableInPolyTime TableMachine.code GaussMachine.boolCode answer := by
 let p := Classical.choose time_polynomial
 have hp := Classical.choose_spec time_polynomial
 refine ⟨⟨machine,Equiv.refl _,Equiv.refl _⟩,p,?_⟩
 rintro ⟨N,S⟩
 let m := Classical.choose (program_runs S)
 have hm := (Classical.choose_spec (program_runs S)).1
 let h := Classical.choice (Classical.choose_spec (program_runs S)).2
 have hc := StackLang.Program.compiles h (.inl CounterLang.Reg.input) (.inr GaussMachine.Reg.output) (none,initialLocal)
 dsimp only [StackLang.Program.machine] at hc
 rw [initial_configuration ⟨N,S⟩,final_configuration] at hc
 change TM2OutputsInTime machine ((TableMachine.code ⟨N,S⟩).map id)
   (some ((GaussMachine.boolCode (answer ⟨N,S⟩)).map id)) (p.eval (TableMachine.code ⟨N,S⟩).length)
 dsimp only [machine, StackLang.Program.machine, TM2OutputsInTime]
 simp only [List.map_id, Option.map_some]
 refine ⟨hc.toEvalsTo,?_⟩
 have hn : N ≤ (TableMachine.code ⟨N,S⟩).length := by rw [code_length]; dsimp only; omega
 exact hc.steps_le_m.trans (hm.trans ((hp N).le.trans (polynomial_eval_mono p hn)))

end CPTSeparation.QueryMachine

end OAI
