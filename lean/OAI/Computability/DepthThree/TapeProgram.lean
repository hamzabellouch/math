import OAI.Computability.DepthThree.TapeEncoding
import Mathlib.Computability.TuringMachine.PostTuringMachine

namespace OAI

namespace DepthThreeLowerBound

abbrev TapeFlags := (Fin 8 → Bool) × TapeSymbol

namespace TapeFlags

def get (v : TapeFlags) (i : Fin 8) : Bool := v.1 i

def set (v : TapeFlags) (i : Fin 8) (b : Bool) : TapeFlags :=
  (Function.update v.1 i b, v.2)

def save (v : TapeFlags) (a : TapeSymbol) : TapeFlags := (v.1, a)

@[simp] theorem get_set_self (v : TapeFlags) (i : Fin 8) (b : Bool) :
    (v.set i b).get i = b := by
  simp only [get, set, Function.update_self]

@[simp] theorem get_set_of_ne (v : TapeFlags) {i j : Fin 8} (h : j ≠ i) (b : Bool) :
    (v.set i b).get j = v.get j := by
  simp only [get, set, Function.update_of_ne h]

@[simp] theorem save_symbol (v : TapeFlags) (a : TapeSymbol) : (v.save a).2 = a := rfl

@[simp] theorem save_flags (v : TapeFlags) (a : TapeSymbol) : (v.save a).1 = v.1 := rfl

end TapeFlags

inductive TapeInstr (Q : Type)
  | move (direction : Turing.Dir) (next : Q)
  | write (symbol : TapeSymbol → TapeFlags → TapeSymbol) (next : Q)
  | load (flags : TapeSymbol → TapeFlags → TapeFlags) (next : Q)
  | branch (test : TapeSymbol → TapeFlags → Bool) (yes no : Q)
  | scan (direction : Turing.Dir) (stop : TapeSymbol → TapeFlags → Bool) (next : Q)
  | halt

namespace TapeInstr

variable {Q : Type}

def toStmt (self : Q) : TapeInstr Q → Turing.TM1.Stmt TapeSymbol Q TapeFlags
  | .move d q => .move d (.goto fun _ _ => q)
  | .write f q => .write f (.goto fun _ _ => q)
  | .load f q => .load f (.goto fun _ _ => q)
  | .branch p q r => .branch p (.goto fun _ _ => q) (.goto fun _ _ => r)
  | .scan d p q => .branch p (.goto fun _ _ => q) (.move d (.goto fun _ _ => self))
  | .halt => .halt

end TapeInstr

abbrev TapeProgram (Q : Type) := Q → TapeInstr Q

namespace TapeProgram

variable {Q : Type}

def code (P : TapeProgram Q) : Q → Turing.TM1.Stmt TapeSymbol Q TapeFlags :=
  fun q => (P q).toStmt q

def cfg (q : Q) (v : TapeFlags) (T : Turing.Tape TapeSymbol) :
    Turing.TM1.Cfg TapeSymbol Q TapeFlags := ⟨some q, v, T⟩

theorem step_move (P : TapeProgram Q) {q q' : Q} {d : Turing.Dir}
    (h : P q = .move d q') (v : TapeFlags) (T : Turing.Tape TapeSymbol) :
    Turing.TM1.step P.code (cfg q v T) = some (cfg q' v (T.move d)) := by
  simp only [Turing.TM1.step, cfg, code, h, TapeInstr.toStmt, Turing.TM1.stepAux]

theorem step_write (P : TapeProgram Q) {q q' : Q}
    {f : TapeSymbol → TapeFlags → TapeSymbol} (h : P q = .write f q')
    (v : TapeFlags) (T : Turing.Tape TapeSymbol) :
    Turing.TM1.step P.code (cfg q v T) = some (cfg q' v (T.write (f T.head v))) := by
  simp only [Turing.TM1.step, cfg, code, h, TapeInstr.toStmt, Turing.TM1.stepAux]

theorem step_load (P : TapeProgram Q) {q q' : Q}
    {f : TapeSymbol → TapeFlags → TapeFlags} (h : P q = .load f q')
    (v : TapeFlags) (T : Turing.Tape TapeSymbol) :
    Turing.TM1.step P.code (cfg q v T) = some (cfg q' (f T.head v) T) := by
  simp only [Turing.TM1.step, cfg, code, h, TapeInstr.toStmt, Turing.TM1.stepAux]

theorem step_branch (P : TapeProgram Q) {q qyes qno : Q}
    {p : TapeSymbol → TapeFlags → Bool} (h : P q = .branch p qyes qno)
    (v : TapeFlags) (T : Turing.Tape TapeSymbol) :
    Turing.TM1.step P.code (cfg q v T) =
      some (cfg (if p T.head v then qyes else qno) v T) := by
  cases hp : p T.head v <;>
    simp only [Turing.TM1.step, cfg, code, h, TapeInstr.toStmt,
      Turing.TM1.stepAux, hp, Bool.false_eq_true, ite_false, ite_true, Bool.cond_false, Bool.cond_true]

theorem step_scan_stop (P : TapeProgram Q) {q q' : Q} {d : Turing.Dir}
    {p : TapeSymbol → TapeFlags → Bool} (h : P q = .scan d p q')
    (v : TapeFlags) (T : Turing.Tape TapeSymbol) (hp : p T.head v = true) :
    Turing.TM1.step P.code (cfg q v T) = some (cfg q' v T) := by
  simp only [Turing.TM1.step, cfg, code, h, TapeInstr.toStmt,
    Turing.TM1.stepAux, hp, Bool.cond_true]

theorem step_scan_move (P : TapeProgram Q) {q q' : Q} {d : Turing.Dir}
    {p : TapeSymbol → TapeFlags → Bool} (h : P q = .scan d p q')
    (v : TapeFlags) (T : Turing.Tape TapeSymbol) (hp : p T.head v = false) :
    Turing.TM1.step P.code (cfg q v T) = some (cfg q v (T.move d)) := by
  simp only [Turing.TM1.step, cfg, code, h, TapeInstr.toStmt,
    Turing.TM1.stepAux, hp, Bool.cond_false]

theorem step_halt (P : TapeProgram Q) {q : Q} (h : P q = .halt)
    (v : TapeFlags) (T : Turing.Tape TapeSymbol) :
    Turing.TM1.step P.code (cfg q v T) = some ⟨none, v, T⟩ := by
  simp only [Turing.TM1.step, cfg, code, h, TapeInstr.toStmt, Turing.TM1.stepAux]

end TapeProgram

end DepthThreeLowerBound

end OAI
