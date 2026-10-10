import Mathlib
import OAI.Computability.MaxCut.Machines.PoweringMachineVertex

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget

open PCP

/-- Initial setup, the actual vertex loop, and the bridge to cleanup. -/
def preBudget (d n vertices inputLength : Nat) : Nat :=
  (3 * vertices + 5) +
    (vertices * (PoweringMachineVertex.budget d n inputLength + 2) + 1)

/-- Cleanup after a preceding run bounded by `prior`, with fixed stack count
and fixed maximum number of pushes per machine transition. -/
def finishBudget (d n pushBound tapeCount vertices inputLength prior : Nat) : Nat :=
  2 * (vertices + PoweringTableLayout.blockSize d n * vertices) + 6 +
    tapeCount * (inputLength + prior * pushBound + vertices +
      PoweringTableLayout.blockSize d n * vertices + 3)

def totalBudget (d n pushBound tapeCount vertices inputLength : Nat) : Nat :=
  preBudget d n vertices inputLength +
    finishBudget d n pushBound tapeCount vertices inputLength
      (preBudget d n vertices inputLength)

theorem preBudget_mono_vertices (d n inputLength : Nat) {v w : Nat} (h : v ≤ w) :
    preBudget d n v inputLength ≤ preBudget d n w inputLength := by
  have hthree := Nat.mul_le_mul_left 3 h
  have hloop := Nat.mul_le_mul_right (PoweringMachineVertex.budget d n inputLength + 2) h
  unfold preBudget
  omega

theorem finishBudget_mono (d n pushBound tapeCount inputLength : Nat)
    {v w prior later : Nat} (hvertices : v ≤ w) (hprior : prior ≤ later) :
    finishBudget d n pushBound tapeCount v inputLength prior ≤
      finishBudget d n pushBound tapeCount w inputLength later := by
  have hdarts := Nat.mul_le_mul_left (PoweringTableLayout.blockSize d n) hvertices
  have hheader := Nat.mul_le_mul_left 2 (Nat.add_le_add hvertices hdarts)
  have hgrowth := Nat.mul_le_mul_right pushBound hprior
  have hinside : inputLength + prior * pushBound + v +
      PoweringTableLayout.blockSize d n * v + 3 ≤
      inputLength + later * pushBound + w + PoweringTableLayout.blockSize d n * w + 3 := by
    omega
  have hclear := Nat.mul_le_mul_left tapeCount hinside
  unfold finishBudget
  omega

theorem totalBudget_mono_vertices (d n pushBound tapeCount inputLength : Nat)
    {v w : Nat} (hvertices : v ≤ w) :
    totalBudget d n pushBound tapeCount v inputLength ≤
      totalBudget d n pushBound tapeCount w inputLength := by
  have hpre := preBudget_mono_vertices d n inputLength hvertices
  unfold totalBudget
  exact Nat.add_le_add hpre
    (finishBudget_mono d n pushBound tapeCount inputLength hvertices hpre)

/-- The exact affine polynomial of one concrete row body. -/
noncomputable def rowTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringMachineRowBody.bufferSize d n) *
      (Polynomial.C (28 * (2 * (n + 1)) + 10) * Polynomial.X +
        Polynomial.C (24 * (2 * (n + 1)) + 15)) + Polynomial.C 1 +
    (Polynomial.C (14 * (n + 1) + 4) * Polynomial.X +
      Polynomial.C (12 * (n + 1)) + Polynomial.C 6)

@[simp] theorem rowTime_eval (d n inputLength : Nat) :
    (rowTime d n).eval inputLength = PoweringMachineRowBody.budget d n inputLength := by
  simp only [rowTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, PoweringMachineRowBody.budget, PoweringPlanBudget.rowBudget,
    PoweringPlanBudget.fieldBudget, PoweringMachineRowBody.bufferSize, Nat.add_assoc]

/-- The actual fixed number of row commands multiplies the row polynomial. -/
noncomputable def vertexTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringTableLayout.blockSize d n) * rowTime d n

@[simp] theorem vertexTime_eval (d n inputLength : Nat) :
    (vertexTime d n).eval inputLength = PoweringMachineVertex.budget d n inputLength := by
  simp only [vertexTime, Polynomial.eval_mul, Polynomial.eval_C, rowTime_eval,
    PoweringMachineVertex.budget]

/-- Replace the vertex count by the input length in the actual setup/loop bound. -/
noncomputable def preTime (d n : Nat) : Polynomial Nat :=
  (Polynomial.C 3 * Polynomial.X + Polynomial.C 5) +
    (Polynomial.X * (vertexTime d n + Polynomial.C 2) + Polynomial.C 1)

@[simp] theorem preTime_eval (d n inputLength : Nat) :
    (preTime d n).eval inputLength = preBudget d n inputLength inputLength := by
  simp only [preTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, vertexTime_eval, preBudget]

/-- The explicit final polynomial. All coefficients depend only on the fixed
degree/radius and the chosen finite machine's push bound and tape count. -/
noncomputable def time (d n pushBound tapeCount : Nat) : Polynomial Nat :=
  preTime d n +
    (Polynomial.C 2 *
        (Polynomial.X + Polynomial.C (PoweringTableLayout.blockSize d n) * Polynomial.X) +
      Polynomial.C 6 + Polynomial.C tapeCount *
        (Polynomial.X + preTime d n * Polynomial.C pushBound + Polynomial.X +
          Polynomial.C (PoweringTableLayout.blockSize d n) * Polynomial.X + Polynomial.C 3))

@[simp] theorem time_eval (d n pushBound tapeCount inputLength : Nat) :
    (time d n pushBound tapeCount).eval inputLength =
      totalBudget d n pushBound tapeCount inputLength inputLength := by
  simp only [time, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, preTime_eval, totalBudget, finishBudget]

/-- The actual vertex count may be strictly smaller than the input length. -/
theorem totalBudget_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) :
    totalBudget d n pushBound tapeCount vertices inputLength ≤
      (time d n pushBound tapeCount).eval inputLength := by
  rw [time_eval]
  exact totalBudget_mono_vertices d n pushBound tapeCount inputLength hvertices

/-- Direct arithmetic interface for the global setup/loop and cleanup bounds. -/
theorem setup_loop_finish_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) :
    ((3 * vertices + 5) +
        (vertices * (PoweringMachineVertex.budget d n inputLength + 2) + 1)) +
      (2 * (vertices + (2 * d ^ (n + 1)) * vertices) + 6 +
        tapeCount * (inputLength +
          ((3 * vertices + 5) +
            (vertices * (PoweringMachineVertex.budget d n inputLength + 2) + 1)) * pushBound +
          vertices + (2 * d ^ (n + 1)) * vertices + 3)) ≤
      (time d n pushBound tapeCount).eval inputLength := by
  simpa only [totalBudget, preBudget, finishBudget, PoweringTableLayout.blockSize] using
    totalBudget_le_time d n pushBound tapeCount vertices inputLength hvertices

/-- Numerical bounds on two actual phases can use the same fixed polynomial. -/
theorem execution_budget_le_time (d n pushBound tapeCount vertices inputLength : Nat)
    (hvertices : vertices ≤ inputLength) {preSteps finishSteps : Nat}
    (hpre : preSteps ≤ preBudget d n vertices inputLength)
    (hfinish : finishSteps ≤ finishBudget d n pushBound tapeCount vertices inputLength
      (preBudget d n vertices inputLength)) :
    preSteps + finishSteps ≤ (time d n pushBound tapeCount).eval inputLength := by
  calc
    preSteps + finishSteps ≤ totalBudget d n pushBound tapeCount vertices inputLength := by
      unfold totalBudget
      exact Nat.add_le_add hpre hfinish
    _ ≤ (time d n pushBound tapeCount).eval inputLength :=
      totalBudget_le_time d n pushBound tapeCount vertices inputLength hvertices

/-- Typed graph input supplies the required vertex-count bound itself. -/
theorem graph_totalBudget_le_time {vertices d : Nat} (graph : PortTables.Table vertices d)
    (n pushBound tapeCount : Nat) :
    totalBudget d n pushBound tapeCount vertices (PortTables.tableBits graph).length ≤
      (time d n pushBound tapeCount).eval (PortTables.tableBits graph).length :=
  totalBudget_le_time d n pushBound tapeCount vertices (PortTables.tableBits graph).length
    (PortTables.vertices_le_tableBits_length graph)

end MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget

end OAI
