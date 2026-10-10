import Mathlib.Data.Nat.Size
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace OAI

namespace NCHitting.BitModel

def width (n : ℕ) : ℕ := n.size + 1

def addCost (a b : ℕ) : ℕ := 4 * (width a + width b)
def mulCost (a b : ℕ) : ℕ := 8 * width a * width b
def compareCost (a b : ℕ) : ℕ := 2 * (width a + width b)

def listBits (xs : List ℕ) : ℕ := (xs.map width).sum

structure NatResult where
  value : ℕ
  cost : ℕ
  deriving DecidableEq, Repr

def powerRun (base : ℕ) : ℕ → NatResult
  | 0 => ⟨1, width 1⟩
  | k + 1 =>
      let previous := powerRun base k
      ⟨previous.value * base,
        previous.cost + mulCost previous.value base + addCost k 1 + 1⟩

@[simp] theorem powerRun_value (base k : ℕ) : (powerRun base k).value = base ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [powerRun, ih, pow_succ]

inductive Expr where
  | literal : ℕ → Expr
  | read : ℕ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | power : Expr → Expr → Expr
  | less : Expr → Expr → Expr
  | equal : Expr → Expr → Expr
  | odd : Expr → Expr
  deriving DecidableEq, Repr

def Expr.run (environment : List ℕ) : Expr → NatResult
  | .literal n => ⟨n, width n + 1⟩
  | .read index =>
      ⟨environment[index]?.getD 0,
        width index + listBits (environment.take (index + 1)) + 1⟩
  | .add a b =>
      let x := a.run environment
      let y := b.run environment
      ⟨x.value + y.value, x.cost + y.cost + addCost x.value y.value + 1⟩
  | .sub a b =>
      let x := a.run environment
      let y := b.run environment
      ⟨x.value - y.value, x.cost + y.cost + addCost x.value y.value + 1⟩
  | .mul a b =>
      let x := a.run environment
      let y := b.run environment
      ⟨x.value * y.value, x.cost + y.cost + mulCost x.value y.value + 1⟩
  | .power a b =>
      let x := a.run environment
      let y := b.run environment
      let z := powerRun x.value y.value
      ⟨z.value, x.cost + y.cost + z.cost + 1⟩
  | .less a b =>
      let x := a.run environment
      let y := b.run environment
      ⟨if x.value < y.value then 1 else 0,
        x.cost + y.cost + compareCost x.value y.value + 1⟩
  | .equal a b =>
      let x := a.run environment
      let y := b.run environment
      ⟨if x.value = y.value then 1 else 0,
        x.cost + y.cost + compareCost x.value y.value + 1⟩
  | .odd a =>
      let x := a.run environment
      ⟨x.value % 2, x.cost + 2⟩

structure RationalCode where
  negative : Bool
  numerator : ℕ
  denominator : ℕ
  deriving DecidableEq, Repr

def RationalCode.bits (entry : RationalCode) : ℕ :=
  1 + width entry.numerator + width entry.denominator

def outputBits (entries : List RationalCode) : ℕ := (entries.map RationalCode.bits).sum

inductive Program where
  | skip : Program
  | emit : Expr → Expr → Expr → Program
  | sequence : Program → Program → Program
  | branch : Expr → Program → Program → Program
  | loop : Expr → Program → Program
  deriving DecidableEq, Repr

structure ProgramResult where
  output : List RationalCode
  cost : ℕ
  deriving DecidableEq, Repr

def Program.run (environment : List ℕ) : Program → ProgramResult
  | .skip => ⟨[], 1⟩
  | .emit sign numerator denominator =>
      let s := sign.run environment
      let a := numerator.run environment
      let b := denominator.run environment
      let entry : RationalCode := ⟨decide (s.value % 2 = 1), a.value, b.value⟩
      ⟨[entry], s.cost + a.cost + b.cost + entry.bits + 2⟩
  | .sequence p q =>
      let x := p.run environment
      let y := q.run environment
      ⟨x.output ++ y.output, x.cost + y.cost + outputBits x.output + 1⟩
  | .branch test yes no =>
      let t := test.run environment
      let result := if t.value = 0 then no.run environment else yes.run environment
      ⟨result.output, t.cost + result.cost + 1⟩
  | .loop bound body =>
      let b := bound.run environment
      let iterations := (List.range b.value).map fun index =>
        let result := body.run (index :: environment)
        (result, width index + addCost index 1 + 1)
      ⟨iterations.flatMap (fun result => result.1.output),
        b.cost + 1 + (iterations.map fun result =>
          result.1.cost + result.2 + outputBits result.1.output).sum⟩

def execute (program : Program) (inputs : List ℕ) : ProgramResult :=
  let result := program.run inputs
  ⟨result.output, listBits inputs + result.cost⟩

end NCHitting.BitModel

end OAI
