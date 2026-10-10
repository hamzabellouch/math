import Mathlib
import OAI.Analysis.MatrixSigning.Realization.Realization
import OAI.Analysis.MatrixSigning.Realization.ArithmeticRoutine
import OAI.Analysis.MatrixSigning.Realization.CompareRoutine
import OAI.Analysis.MatrixSigning.Realization.FloorCleanRoutine
import OAI.Analysis.MatrixSigning.Realization.ConditionalRoutine

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

abbrev ratCode : ℚ → Word := KS.W01.encodeRat
def boolCode (b : Bool) : Word := [b]

def ratOp (op : KS.W13.ExpressionMachine.BinaryOp) :
    Realizes (prodCode ratCode ratCode) ratCode (fun p => op.eval p.1 p.2) where
  cost := fun p => ArithmeticRoutine.ticks op p.1 p.2
  routine := ArithmeticRoutine.routine op

def ratLE : Realizes (prodCode ratCode ratCode) boolCode (fun p => decide (p.1≤p.2)) where
  cost := fun p => CompareRoutine.ticks p.1 p.2
  routine := CompareRoutine.routine

def ratFloor : Realizes ratCode ratCode (fun q => (⌊q⌋ : ℚ)) where
  cost := FloorCleanRoutine.ticks
  routine := FloorCleanRoutine.routine

variable {α β : Type*} {encA : α → Word} {encB : β → Word}

def conditional {f g : α → β} (r : Realizes encA encB f) (s : Realizes encA encB g) :
    Realizes (prodCode boolCode encA) encB (fun p => if p.1 then f p.2 else g p.2) where
  cost := fun p => 5+(if p.1 then r.cost p.2 else s.cost p.2)+1
  routine := by
    have h := ConditionalRoutine.routine r.routine s.routine
    refine { scratch := h.scratch,program := h.program,spec := ?_ }
    intro p
    have hp := h.spec p
    simp only [apply_ite] at hp ⊢
    exact hp

def Realizes.ite {p : α → Bool} {f g : α → β}
    (b : Realizes encA boolCode p) (r : Realizes encA encB f) (s : Realizes encA encB g) :
    Realizes encA encB (fun x => if p x then f x else g x) :=
  (b.both (identity encA)).then (conditional r s)

def Realizes.add {f g : α → ℚ} (r : Realizes encA ratCode f) (s : Realizes encA ratCode g) :
    Realizes encA ratCode (fun x => f x+g x) := (r.both s).then (ratOp .add)
def Realizes.sub {f g : α → ℚ} (r : Realizes encA ratCode f) (s : Realizes encA ratCode g) :
    Realizes encA ratCode (fun x => f x-g x) := (r.both s).then (ratOp .sub)
def Realizes.mul {f g : α → ℚ} (r : Realizes encA ratCode f) (s : Realizes encA ratCode g) :
    Realizes encA ratCode (fun x => f x*g x) := (r.both s).then (ratOp .mul)

def Realizes.pow {function : α → ℚ} (realization : Realizes encA ratCode function) :
    (exponent : ℕ) → Realizes encA ratCode (fun input => function input ^ exponent)
  | 0 => (constant encA ratCode 1).congr (fun _ => (pow_zero _).symm)
  | exponent + 1 => ((realization.pow exponent).mul realization).congr
      (fun input => (pow_succ (function input) exponent).symm)

def Realizes.div {f g : α → ℚ} (r : Realizes encA ratCode f) (s : Realizes encA ratCode g) :
    Realizes encA ratCode (fun x => f x/g x) := (r.both s).then (ratOp .div)
def Realizes.le {f g : α → ℚ} (r : Realizes encA ratCode f) (s : Realizes encA ratCode g) :
    Realizes encA boolCode (fun x => decide (f x≤g x)) := (r.both s).then ratLE

def Realizes.lt {function other : α → ℚ}
    (realization : Realizes encA ratCode function) (comparison : Realizes encA ratCode other) :
    Realizes encA boolCode (fun input => decide (function input < other input)) :=
  ((comparison.le realization).ite
    (constant encA boolCode false) (constant encA boolCode true)).congr (by
      intro input
      by_cases bound : other input ≤ function input <;>
        simp [bound, not_lt_of_ge, lt_of_not_ge])

def Realizes.neg {f : α → ℚ} (r : Realizes encA ratCode f) :
    Realizes encA ratCode (fun x => -f x) :=
  ((constant encA ratCode 0).sub r).congr (fun x => zero_sub (f x))

def Realizes.abs {f : α → ℚ} (r : Realizes encA ratCode f) :
    Realizes encA ratCode (fun x => |f x|) :=
  ((r.le (constant encA ratCode 0)).ite r.neg r).congr (by
    intro x
    by_cases h : f x≤0
    · simp [h,abs_of_nonpos h]
    · simp [h,abs_of_pos (lt_of_not_ge h)])

def roundScalar : Realizes (prodCode ratCode ratCode) ratCode
    (fun p => p.1*(⌊p.2/p.1⌋ : ℚ)) :=
  let rho := first ratCode ratCode
  let x := second ratCode ratCode
  rho.mul ((x.div rho).then ratFloor)

lemma fold_add_zero (xs : List ℚ) : xs.foldl (fun a b => a+b) 0=xs.sum := by
  have h : ∀ z : ℚ,xs.foldl (fun a b => a+b) z=z+xs.sum := by
    induction xs with
    | nil => intro z;simp
    | cons x xs ih => intro z;simp [ih,add_assoc]
  simpa using h 0

def sumRationals : Realizes (listCode ratCode) ratCode List.sum :=
  (((constant (listCode ratCode) ratCode 0).both (identity (listCode ratCode))).then
    (ratOp .add).fold).congr fold_add_zero

def l1Rationals : Realizes (listCode ratCode) ratCode (fun xs => (xs.map abs).sum) :=
  (identity ratCode).abs.map.then sumRationals

end CurrentKS.Realization

end OAI
