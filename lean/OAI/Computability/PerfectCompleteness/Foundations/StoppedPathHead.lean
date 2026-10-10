import Lean.Elab.Tactic.Omega
import OAI.Computability.PerfectCompleteness.Foundations.StoppedProjectedExperiment

namespace OAI

section

namespace PerfectCompleteness.StoppedPathHead

open DescendantSpaces

variable {branch : Nat → Nat} {i j : Nat}

def headTail (hij : i < j) (p : Path branch (j + 1) (i + 1)) :
    Fin (branch j) × Path branch j (i + 1) := by
  cases p with
  | refl => omega
  | step a q => exact (a, q)

def child (hij : i < j) (p : Path branch (j + 1) (i + 1)) : Fin (branch j) :=
  (headTail hij p).1

def tail (hij : i < j) (p : Path branch (j + 1) (i + 1)) : Path branch j (i + 1) :=
  (headTail hij p).2

theorem step_eq (hij : i < j) (p : Path branch (j + 1) (i + 1)) :
    p = Path.step (child hij p) (tail hij p) := by
  cases p with
  | refl => omega
  | step a q => rfl

@[simp] theorem child_step (hij : i < j) (a : Fin (branch j))
    (q : Path branch j (i + 1)) : child hij (Path.step a q) = a := rfl

@[simp] theorem tail_step (hij : i < j) (a : Fin (branch j))
    (q : Path branch j (i + 1)) : tail hij (Path.step a q) = q := rfl

theorem prefixPath_step_eq (hij : i < j)
    (pref : GeometricCutSplit.Prefix branch (j + 1) (i + 1)) :
    GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) pref =
      Path.step
        (child hij (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) pref))
        (tail hij (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) pref)) :=
  step_eq hij _

theorem lowerPath_step_eq {n t : Nat} (rows : Nat → Nat) (hij : i < j)
    (k : StoppedProjectedExperiment.Inner
      (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    StoppedProjectedExperiment.lowerPath rows hij k =
      Path.step (child hij (StoppedProjectedExperiment.lowerPath rows hij k))
        (tail hij (StoppedProjectedExperiment.lowerPath rows hij k)) :=
  step_eq hij _

end PerfectCompleteness.StoppedPathHead

end

end OAI
