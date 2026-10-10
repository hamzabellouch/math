import Mathlib
import OAI.MathematicalPhysics.RecorderFlows.Observation

namespace OAI

/-! Finite oracle programs and effective mixed-derivative evaluation. -/

namespace Solenoidal
namespace Effective
inductive OracleCode
  | zero | succ | left | right | query
  | pair (f g : OracleCode)
  | comp (f g : OracleCode)
  | prec (f g : OracleCode)
  | rfind (f : OracleCode)

 
noncomputable def OracleCode.eval (o : ℕ → ℕ) : OracleCode → ℕ → Part ℕ
  | .zero => fun _ => .some 0
  | .succ => fun n => .some (n + 1)
  | .left => fun n => .some n.unpair.1
  | .right => fun n => .some n.unpair.2
  | .query => fun n => .some (o n)
  | .pair f g => fun n => Nat.pair <$> f.eval o n <*> g.eval o n
  | .comp f g => fun n => g.eval o n >>= f.eval o
  | .prec f g => fun n =>
      let (a, k) := n.unpair
      k.rec (f.eval o a) fun j ih => do
        let b ← ih
        g.eval o (Nat.pair a (Nat.pair j b))
  | .rfind f => fun a => Nat.rfind fun n => (fun k => k = 0) <$> f.eval o (Nat.pair a n)

 
def decodeRat (n : ℕ) : ℚ := (Encodable.decode (α := ℚ) n).getD 0

noncomputable def tolerance (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

def Names (x : ℝ) (o : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, |(decodeRat (o n) : ℝ) - x| ≤ tolerance n

def ComputableReal (x : ℝ) : Prop :=
  ∃ c : Nat.Partrec.Code, ∀ n : ℕ, ∃ a : ℕ,
    a ∈ c.eval n ∧ |(decodeRat a : ℝ) - x| ≤ tolerance n

 

def NamesArguments (ν : ℝ) (p : Fluid.SpaceTime) (o : ℕ → ℕ) : Prop :=
  Names ν (fun n => o (Nat.pair 0 n)) ∧
    ∀ i : Fin 4, Names (p i) (fun n => o (Nat.pair (i.val + 1) n))

 
def machineCode (M : Machine) : ℕ :=
  let qs := List.finRange (M.states + 1)
  let as := List.finRange (M.symbols + 1)
  let moves : Move → ℕ := fun | .left => 0 | .stay => 1 | .right => 2
  let table := qs.flatMap fun q => as.map fun a =>
    let r := M.table q a
    (r.1.val, r.2.1.val, moves r.2.2)
  Encodable.encode (M.states, M.symbols, M.initial.val, M.blank.val, qs.map M.halt, table)

def wordCode {M : Machine} (w : List M.Symbol) : ℕ :=
  Encodable.encode (w.map Fin.val)

def request (M : Machine) (w : List M.Symbol) (a : List (Fin 4)) (j : Fin 3) (n : ℕ) : ℕ :=
  Encodable.encode (machineCode M, wordCode w, a.map Fin.val, j.val, n)

def boundRequest (M : Machine) (w : List M.Symbol) (a : List (Fin 4)) (R : ℕ) : ℕ :=
  Encodable.encode (machineCode M, wordCode w, a.map Fin.val, R)

abbrev ForceFamily := (ν : ℝ) → (M : Machine) → List M.Symbol → Fluid.Field

 

def RelativeEffective (F : ForceFamily) (eval bounds : OracleCode) : Prop :=
  (∀ (ν : ℝ), 0 < ν → ∀ (M : Machine) (w : List M.Symbol) (p : Fluid.SpaceTime),
    0 ≤ p 0 → ∀ o : ℕ → ℕ, NamesArguments ν p o →
    ∀ (a : List (Fin 4)) (j : Fin 3) (n : ℕ), ∃ r : ℕ,
      r ∈ eval.eval o (request M w a j n) ∧
        |(decodeRat r : ℝ) - Fluid.mixedD a (F ν M w) p j| ≤ tolerance n) ∧
  (∀ (ν : ℝ), 0 < ν → ∀ o : ℕ → ℕ, Names ν o →
    ∀ (M : Machine) (w : List M.Symbol) (a : List (Fin 4)) (R : ℕ), ∃ C : ℕ,
      C ∈ bounds.eval o (boundRequest M w a R) ∧
        ∀ p : Fluid.SpaceTime, 0 ≤ p 0 → (∀ i, |p i| ≤ (R : ℝ)) →
          ‖Fluid.mixedD a (F ν M w) p‖ ≤ (C : ℝ))

 

def SuppliesArgument (c : Nat.Partrec.Code) (p : Fluid.SpaceTime) : Prop :=
  ∀ (i : Fin 4) (n : ℕ), ∃ r : ℕ, r ∈ c.eval (Nat.pair i.val n) ∧
    |(decodeRat r : ℝ) - p i| ≤ tolerance n

 

def EffectiveAt (F : ForceFamily) (ν : ℝ) : Prop :=
  ∃ eval bounds : Nat.Partrec.Code,
    (∀ (M : Machine) (w : List M.Symbol) (p : Fluid.SpaceTime), 0 ≤ p 0 →
      ∀ c : Nat.Partrec.Code, SuppliesArgument c p →
      ∀ (a : List (Fin 4)) (j : Fin 3) (n : ℕ), ∃ r : ℕ,
        r ∈ eval.eval (Nat.pair (request M w a j n) (Encodable.encode c)) ∧
          |(decodeRat r : ℝ) - Fluid.mixedD a (F ν M w) p j| ≤ tolerance n) ∧
    (∀ (M : Machine) (w : List M.Symbol) (a : List (Fin 4)) (R : ℕ), ∃ C : ℕ,
      C ∈ bounds.eval (boundRequest M w a R) ∧
        ∀ p : Fluid.SpaceTime, 0 ≤ p 0 → (∀ i, |p i| ≤ (R : ℝ)) →
          ‖Fluid.mixedD a (F ν M w) p‖ ≤ (C : ℝ))
end Effective
end Solenoidal

end OAI
