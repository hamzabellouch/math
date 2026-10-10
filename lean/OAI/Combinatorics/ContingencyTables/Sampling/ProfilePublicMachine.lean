import OAI.Combinatorics.ContingencyTables.Sampling.ProfilePublicSemantics
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordOutput
import OAI.Combinatorics.ContingencyTables.Sampling.GreedyPublicMachine

namespace OAI

/-! # Physical execution of the computed public profile sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.LiteralCodec Turing

lemma printMatrix_alphabet (rows : DensePrograms.MatrixCode) :
    ∀ a∈GreedyFeasibleTable.printMatrix rows,a≠6 ∧ a≠7 := by
  intro a ha
  obtain ⟨row,_,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨n,_,ha⟩ := List.mem_flatMap.mp ha
  simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide

lemma publicSampling_alphabet (as : List Symbol) (bits : List Bool) :
    ∀ a∈publicSampling (as,bits),a≠6 ∧ a≠7 := printMatrix_alphabet _

lemma samplingInput_nonzero {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (k : ℕ) :
    ∀ a∈Algorithms.encodeSamplingInput r c k,a≠0 := by
  intro a ha
  rcases List.mem_append.mp ha with hm|hk
  · exact GreedyFeasibleTable.encodeMargins_nonzero r c a hm
  · simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at hk
    rcases hk with ⟨b,_,rfl⟩|rfl
    · cases b <;> decide
    · decide

noncomputable def samplingMachine : RandomMachine :=
  FiniteWordExecution.machine publicWordCountRealizer publicSamplingRealizer

noncomputable def samplingMachineTime (as : List Symbol) : ℕ :=
  FiniteWordExecution.machineTime publicWordCountRealizer publicSamplingRealizer as

/-- A single fixed transition table implements the public program,
with cost controlled by its computed word schedule. -/
theorem samplingMachineTime_polynomial :
    ∃ p : Polynomial ℕ,∀ as,samplingMachineTime as≤p.eval
      (FiniteWordExecution.wordMeasure publicWordCount as) :=
  FiniteWordExecution.machineTime_polynomial polynomial_publicWordCount polynomial_publicSampling

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open MatchingFPRAS MatchingFPRAS.PhysicalStream Turing
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

/-- Every actual machine execution in the nonempty large-rectangle branch
halts and outputs a feasible original table. -/
theorem samplingMachine_large_outputs
    (hr : 0<(largeIndices (d^20,List.ofFn r)).length)
    (hc : 0<(largeIndices (d^20,List.ofFn c)).length)
    (htotal : (∑ i,r i)=∑ j,c j) (k t : ℕ)
    (ht : samplingMachineTime (Algorithms.encodeSamplingInput r c k)≤t) :
    ∀ bits : Bits t,∃ X : Table r c,
      Algorithms.OutputsTable samplingMachine (Algorithms.encodeSamplingInput r c k) bits X.val := by
  let as := Algorithms.encodeSamplingInput r c k
  let P : Tape Symbol → Prop := fun tape => ∃ X : Table r c,
    tape.right₀=ListBlank.mk (Algorithms.encodeMatrix X.val)
  have hf : ∀ bits : Bits (publicWordCount as),P (Tape.mk₁ (publicSampling (as,List.ofFn bits))) := by
    dsimp only [as]
    rw [publicWordCount_spec]
    intro bits
    refine ⟨listedOuterDraw r c (computedCellEquiv r c) hr hc b (outerAccuracy d b k)
      (smallBinaryLength_parameters r c).1 (tableState r c (GreedyFeasibleTable.table r c htotal))
      (outerSteps d b k) (outerTrials d k) (GreedyFeasibleTable.table r c htotal) bits,?_⟩
    rw [publicSampling_spec r c hr hc htotal]
    simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]
  have hP := FiniteWordExecution.machine_all publicWordCountRealizer publicSamplingRealizer as
    (samplingInput_nonzero r c k) (publicSampling_alphabet as) P hf t ht
  have hhalt := (FiniteWordExecution.machine_law publicWordCountRealizer publicSamplingRealizer as
    (samplingInput_nonzero r c k) (publicSampling_alphabet as) t ht).1
  intro bits
  obtain ⟨X,hX⟩ := hP bits
  exact ⟨X,hhalt bits,hX⟩

end
end ContingencyTables.SmallGraphProfiles

end OAI
