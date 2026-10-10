import OAI.Combinatorics.ContingencyTables.Sampling.AllSamplingAccuracy
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileRuntimeBound
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordTableLaw

namespace OAI

/-! # The bounded public sampler on every margin pair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

noncomputable def allSamplingMachine : RandomMachine :=
  FiniteWordExecution.machine publicWordCountRealizer publicSamplingAllRealizer
noncomputable def allSamplingMachineTime (as : List MatchingFPRAS.Symbol) : ℕ :=
  FiniteWordExecution.machineTime publicWordCountRealizer publicSamplingAllRealizer as

lemma publicSamplingAll_alphabet (as : List MatchingFPRAS.Symbol) (bits : List Bool) :
    ∀ a∈publicSamplingAll (as,bits),a≠6 ∧ a≠7 := printMatrix_alphabet _

lemma allSamplingMachineTime_polynomial :
    ∃ p : Polynomial ℕ,∀ as,allSamplingMachineTime as≤p.eval
      (FiniteWordExecution.wordMeasure publicWordCount as) :=
  FiniteWordExecution.machineTime_polynomial polynomial_publicWordCount polynomial_publicSamplingAll

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.TreeTyped Turing Algorithms Polynomial
open ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section

lemma allSamplingMachineTime_public_bound :
    ∃ C d : ℕ,0<C ∧ ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → ∀ k,
      allSamplingMachineTime (encodeSamplingInput r c k)≤C*(samplingSize n r k)^d := by
  obtain ⟨p,hp⟩ := allSamplingMachineTime_polynomial
  refine ⟨p.eval (344^644+91)+1,1288*p.natDegree,by omega,?_⟩
  intro m n r c htotal k
  have hS : 1 ≤ samplingSize n r k := by unfold samplingSize; omega
  calc
    _ ≤ p.eval (FiniteWordExecution.wordMeasure publicWordCount (encodeSamplingInput r c k)) := hp _
    _ ≤ p.eval ((344^644+91)*(samplingSize n r k)^1288) :=
      polynomial_eval_monotone p (public_wordMeasure_bound r c htotal k)
    _ ≤ p.eval (344^644+91)*(samplingSize n r k)^(1288*p.natDegree) :=
      polynomial_scaled_power p (344^644+91) (samplingSize n r k) 1288 hS
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma allSamplingMachine_outputs (htotal : (∑ i,r i)=∑ j,c j) (k t : ℕ)
    (ht : allSamplingMachineTime (encodeSamplingInput r c k)≤t) :
    ∀ bits : Bits t,∃ X : Table r c,
      OutputsTable allSamplingMachine (encodeSamplingInput r c k) bits X.val := by
  let as := encodeSamplingInput r c k
  let P : Tape MatchingFPRAS.Symbol → Prop := fun tape => ∃ X : Table r c,
    tape.right₀=ListBlank.mk (encodeMatrix X.val)
  have hf : ∀ bits : Bits (publicWordCount as),P (Tape.mk₁ (publicSamplingAll (as,List.ofFn bits))) := by
    dsimp only [as]
    rw [publicWordCount_spec]
    intro bits
    refine ⟨scheduledTableDraw r c htotal k bits,?_⟩
    rw [publicSamplingAll_spec r c htotal]
    simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]
  have hP := FiniteWordExecution.machine_all publicWordCountRealizer publicSamplingAllRealizer as
    (samplingInput_nonzero r c k) (publicSamplingAll_alphabet as) P hf t ht
  have hhalt := (FiniteWordExecution.machine_law publicWordCountRealizer publicSamplingAllRealizer as
    (samplingInput_nonzero r c k) (publicSamplingAll_alphabet as) t ht).1
  intro bits
  obtain ⟨X,hX⟩ := hP bits
  exact ⟨X,hhalt bits,hX⟩

lemma allSamplingMachine_mass (htotal : (∑ i,r i)=∑ j,c j) (k t : ℕ)
    (ht : allSamplingMachineTime (encodeSamplingInput r c k)≤t) (X : Table r c) :
    tableMass allSamplingMachine (encodeSamplingInput r c k) t X.val=
      ((mapLaw (uniformLaw (α := Bits (finiteSamplerBits r c k)))
        (scheduledTableDraw r c htotal k)).mass X:ℝ) :=
  FiniteWordExecution.machine_tableMass publicWordCountRealizer publicSamplingAllRealizer
    (encodeSamplingInput r c k) (samplingInput_nonzero r c k)
    (publicSamplingAll_alphabet _) (publicWordCount_spec r c k) (scheduledTableDraw r c htotal k)
    (publicSamplingAll_spec r c htotal k) t ht X

/-- Paper 200-01, main theorem (i), conditional only on Prékopa (1973)
Theorem 3/(2.3) on finite boxes and Levin--Peres (2017) Theorem 13.10,
(13.6), Lemma 13.7 on the completion grids. -/
theorem boundedSampling_conditional
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q d,PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin q) (4*d^8))) : BoundedSamplingStatement := by
  obtain ⟨C,D,hC,hbound⟩ := allSamplingMachineTime_public_bound
  refine ⟨allSamplingMachine,C,D,hC,?_⟩
  intro m n r c htotal k hk
  dsimp only
  have ht := hbound m n r c htotal k
  refine ⟨allSamplingMachine_outputs r c htotal k _ ht,?_⟩
  let : Nonempty (Table r c) := ⟨GreedyFeasibleTable.table r c htotal⟩
  have hv := scheduledTableDraw_accuracy r c (hPL _)
    (hCheeger _ (dimensionAllowance (I := Fin m) (J := Fin n))) htotal k hk
  dsimp only at hv
  simp_rw [allSamplingMachine_mass r c htotal k _ ht]
  simpa only [variation,Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,
    Rat.cast_ofNat,Rat.cast_inv,uniformLaw,uniformMass,Rat.cast_one,Rat.cast_natCast,one_div] using hv

end
end ContingencyTables.SmallGraphProfiles

end OAI
