import Mathlib.Data.Finset.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Adaptive transactions with explicit success declarations

Unlike `QueryProgram`, this syntax distinguishes ending a transaction from
claiming that it succeeded. A declaration is made at the reached tree node,
so it can depend on the entire queried transcript. `SoundAt` requires only
that each actually declared success has a positive certificate. It imposes
no restriction on branches that are not reached by the given bit vector.
-/

namespace MatroidProphet

/-- A finite adaptive program with optional success declarations. -/
inductive MarkedQueryProgram (α : Type*) where
  | stop
  | query (e : α) (no yes : MarkedQueryProgram α)
  | finish (success : Bool) (rest : MarkedQueryProgram α)

namespace MarkedQueryProgram

variable {α : Type*} [DecidableEq α]

/-- No coordinate is queried twice along any branch. -/
def Fresh : MarkedQueryProgram α → Finset α → Prop
  | .stop, _ => True
  | .query e no yes, V => e ∈ V ∧ no.Fresh (V.erase e) ∧ yes.Fresh (V.erase e)
  | .finish _ rest, V => rest.Fresh V

/-- The actual declared-success count on a fully sampled vector. -/
def run (S : Finset α) : MarkedQueryProgram α → ℝ
  | .stop => 0
  | .query e no yes => if e ∈ S then yes.run S else no.run S
  | .finish success rest => (if success then 1 else 0) + rest.run S

/-- Every success declared along this execution is certified by positives
queried within that transaction alone. -/
def SoundAt (cert : Finset α → Prop) (S : Finset α) :
    MarkedQueryProgram α → Finset α → Prop
  | .stop, _ => True
  | .query e no yes, I =>
      if e ∈ S then yes.SoundAt cert S (insert e I) else no.SoundAt cert S I
  | .finish success rest, I =>
      (success = true → cert I) ∧ rest.SoundAt cert S ∅

/-- A deterministic bound on the number of completed transactions. -/
def transactionBound : MarkedQueryProgram α → ℕ
  | .stop => 0
  | .query _ no yes => max no.transactionBound yes.transactionBound
  | .finish _ rest => rest.transactionBound + 1

end MarkedQueryProgram
end MatroidProphet

end OAI
