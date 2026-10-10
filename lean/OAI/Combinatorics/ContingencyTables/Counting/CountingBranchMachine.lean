import OAI.Combinatorics.ContingencyTables.Counting.CountingBranchSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CountingMachineEvents

namespace OAI

/-! # Public-machine output guarantees for the counting dispatcher -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open scoped Classical
noncomputable section

variable (positive : Input→TreeFraction.Fraction) (F : Realizer positive)
variable (width : Request→ℕ) (N : Realizer width)

noncomputable def machine : RandomMachine :=
  FiniteWordExecution.machine (publicBudgetRealizer width N) (publicOutputRealizer positive F)
noncomputable def machineTime (as : List Symbol) : ℕ :=
  FiniteWordExecution.machineTime (publicBudgetRealizer width N) (publicOutputRealizer positive F) as

def sourceValue (as : List Symbol) (bits : Bits (publicBudget width as)) : ℚ :=
  TreeFraction.val (output positive (parsedInput (as,List.ofFn bits)))

lemma sourceValue_nonnegative (as : List Symbol) (bits : Bits (publicBudget width as)) :
    0 ≤ sourceValue positive width as bits := TreeFraction.val_nonneg _

lemma sourceValue_output (as : List Symbol) (bits : Bits (publicBudget width as)) :
    publicOutput positive (as,List.ofFn bits)=encodeRat (sourceValue positive width as bits) :=
  publicOutput_eq positive _

variable {m n : ℕ}

/-- Every random tape halts with a nonnegative rational, including on
statistically unsuccessful histories of the positive-label branch. -/
theorem outputs_nonnegative (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (t : ℕ)
    (ht : machineTime positive F width N (Algorithms.encodeCountingInput r c b epsilon delta) ≤ t) :
    ∀ bits : Bits t, ∃ q : ℚ, 0 ≤ q ∧
      Outputs (machine positive F width N) (Algorithms.encodeCountingInput r c b epsilon delta) bits q := by
  have hh := FiniteWordExecution.machine_rational_all
    (publicBudgetRealizer width N) (publicOutputRealizer positive F)
    (Algorithms.encodeCountingInput r c b epsilon delta)
    (CountingInputSymbols.counting_nonzero r c b epsilon delta)
    (fun bs a ha => (publicOutput_symbols positive _ a ha).2)
    (sourceValue positive width _) (sourceValue_output positive width _)
    (fun q => 0 ≤ q) (sourceValue_nonnegative positive width _) t ht
  intro bits
  obtain ⟨q,hq,hp⟩ := hh bits
  exact ⟨q,hp,hq⟩

lemma sourceValue_zero (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ)
    (hz : Algorithms.count r c b=0)
    (bits : Bits (publicBudget width (Algorithms.encodeCountingInput r c b epsilon delta))) :
    sourceValue positive width (Algorithms.encodeCountingInput r c b epsilon delta) bits=0 := by
  have hf := (count_zero_iff_rejected hEK r c b epsilon delta).mp hz
  unfold sourceValue
  rw [parsedInput_public,output_rejected positive _ hf]
  norm_num [TreeFraction.val]

/-- Exact zero output follows from the executed feasibility test. -/
theorem outputs_zero (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ)
    (hz : Algorithms.count r c b=0) (t : ℕ)
    (ht : machineTime positive F width N (Algorithms.encodeCountingInput r c b epsilon delta) ≤ t) :
    ∀ bits : Bits t,
      Outputs (machine positive F width N) (Algorithms.encodeCountingInput r c b epsilon delta) bits 0 := by
  have hh := FiniteWordExecution.machine_rational_all
    (publicBudgetRealizer width N) (publicOutputRealizer positive F)
    (Algorithms.encodeCountingInput r c b epsilon delta)
    (CountingInputSymbols.counting_nonzero r c b epsilon delta)
    (fun bs a ha => (publicOutput_symbols positive _ a ha).2)
    (sourceValue positive width _) (sourceValue_output positive width _)
    (fun q => q=0) (sourceValue_zero positive width hEK r c b epsilon delta hz) t ht
  intro bits
  obtain ⟨q,hq,rfl⟩ := hh bits
  exact hq

end
end ContingencyTables.CountingBranchProgram

end OAI
