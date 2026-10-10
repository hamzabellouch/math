import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.FinalTableFormula
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineBudget
import OAI.Combinatorics.IndependentSets.Machines.MachineComposition

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def run (H : BaseTable) : Nat → Input → Input := AmplificationIteration.run (step H)

def runTables (H : BaseTable) : Nat → GraphTables.Table → GraphTables.Table :=
  AmplificationIteration.run (build H)

theorem run_val (H : BaseTable) (n : Nat) (input : Input) :
    (run H n input).val = runTables H n input.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change build H (run H n input).val = build H (runTables H n input.val)
      rw [ih]

def iterationCount (F : Formula) : Nat := AmplificationIteration.rounds (size (initial F))

def output (H : BaseTable) (F : Formula) : Input := run H (iterationCount F) (initial F)

def outputTable (H : BaseTable) (F : Formula) : GraphTables.Table :=
  runTables H (iterationCount F) (RawInitialTables.table F)

theorem output_val (H : BaseTable) (F : Formula) : (output H F).val = outputTable H F :=
  run_val H (iterationCount F) (initial F)

def gapMap (H : BaseTable) (F : Formula) : Formula := FinalTableFormula.output (outputTable H F)

opaque degreeData : {n : Nat // sizeFactor ≤ 2 ^ n} :=
  ⟨AmplificationIteration.rounds sizeFactor, (AmplificationIteration.rounds_large sizeFactor).le⟩

def polynomialDegree : Nat := degreeData.val

theorem sizeFactor_le_power : sizeFactor ≤ 2 ^ polynomialDegree :=
  degreeData.property

theorem run_completeness (H : BaseTable) (n : Nat) (input : Input)
    (sat : Satisfiable input) : Satisfiable (run H n input) :=
  AmplificationIteration.run_preserves (step H) Satisfiable (step_completeness H) n input sat

theorem output_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    Satisfiable (output H F) :=
  run_completeness H _ _ ((initial_satisfiable_iff F).mpr sat)

theorem gapMap_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    (gapMap H F).Satisfiable := by
  apply (FinalTableFormula.satisfiable_iff (outputTable H F)).mpr
  rw [← output_val]
  exact output_completeness H F sat

theorem output_darts_positive (H : BaseTable) (F : Formula) : 0 < (outputTable H F).darts := by
  rw [← output_val]
  exact (output H F).property

theorem gapMap_nonempty (H : BaseTable) (F : Formula) : (gapMap H F).clauses ≠ [] :=
  FinalTableFormula.nonempty (outputTable H F) (output_darts_positive H F)

theorem run_size (H : BaseTable) (n : Nat) (input : Input) :
    size (run H n input) ≤ sizeFactor ^ n * size input :=
  AmplificationIteration.run_size (step H) size sizeFactor (step_size H) n input

theorem output_size (H : BaseTable) (F : Formula) :
    size (output H F) ≤ (2 * size (initial F)) ^ polynomialDegree * size (initial F) :=
  AmplificationIteration.run_size_polynomial (step H) size (size_positive (initial F))
    sizeFactor_le_power (step_size H) (initial F)

theorem initial_size_le (F : Formula) : size (initial F) ≤ 7 * (formulaBits F).length :=
  RawInitialMachineBudget.graph_size_bound F

theorem output_size_le_input (H : BaseTable) (F : Formula) :
    (outputTable H F).vertices + (outputTable H F).darts ≤
      (14 * (formulaBits F).length) ^ polynomialDegree * (7 * (formulaBits F).length) := by
  rw [← output_val]
  have h := initial_size_le F
  exact (output_size H F).trans
    (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) h)

noncomputable def tableSizePolynomial : Polynomial Nat :=
  (Polynomial.C 14 * Polynomial.X) ^ polynomialDegree * (Polynomial.C 7 * Polynomial.X)

theorem tableSizePolynomial_eval (N : Nat) :
    tableSizePolynomial.eval N = (14 * N) ^ polynomialDegree * (7 * N) := by
  simp only [tableSizePolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

noncomputable def tableBitsPolynomial : Polynomial Nat :=
  (GraphTableComplexity.encodingPolynomial 64).comp tableSizePolynomial

theorem output_bits_le (H : BaseTable) (F : Formula) :
    (GraphTables.tableBits (outputTable H F)).length ≤ tableBitsPolynomial.eval (formulaBits F).length := by
  rw [tableBitsPolynomial, Polynomial.eval_comp, tableSizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ (output_size_le_input H F)

noncomputable def formulaBitsPolynomial : Polynomial Nat :=
  FinalTableFormula.sizePolynomial.comp tableBitsPolynomial

theorem gapMap_bits_le (H : BaseTable) (F : Formula) :
    (formulaBits (gapMap H F)).length ≤ formulaBitsPolynomial.eval (formulaBits F).length := by
  rw [formulaBitsPolynomial, Polynomial.eval_comp]
  exact (FinalTableFormula.formulaBits_length_le_polynomial (outputTable H F)).trans
    (MachineComposition.natPolynomial_eval_mono _ (output_bits_le H F))

end IndependentSetsGames.Foundations.PCP.TableIteration

end OAI
