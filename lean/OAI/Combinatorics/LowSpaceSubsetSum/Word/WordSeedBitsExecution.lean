import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedMeasured
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedDraws
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SignMaskExecution

namespace OAI

/-! # Stored fair sign bits and the explicitly scanned sign mask -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

def bitsRun (w n : ℕ) (stream : ℕ → Fin (2^w)) (cursor : ℕ) :
    Result (bitArrayCoupling n) :=
  let buffer := WordCandidateExecution.run (k := 1) stream 2 (by norm_num) n cursor
  let f : Fin n → Bool := fun i => finTwoEquiv (buffer.data[i.val])
  ⟨some ⟨WordSeedRealization.bitsSeed n f,f,rfl⟩,buffer.cursor,
    buffer.work+2,buffer.cells+8,n+8⟩

def bits (w n : ℕ) (hw : 1 ≤ w) : Execution (WordSeedRealization.bits w n hw) where
  run := bitsRun w n
  value stream cursor := by
    simp only [WordSeedRealization.bits,WordSeedRejectionExecution.program_run_map,
      WordSeedRejectionExecution.tuple_run,bitsRun,WordCandidateExecution.run_data,
      WordCandidateExecution.run_cursor,Vector.getElem_ofFn,Option.map_some]

theorem bits_bounded (w n : ℕ) (hw : 1 ≤ w) :
    (bits w n hw).Bounded (5*n+3) (2*n+20) (n+8) := by
  intro stream cursor
  have hc := WordCandidateExecution.run_cells stream 2 (by norm_num : 2=2^1) n cursor
  have hw := WordCandidateExecution.run_work stream 2 (by norm_num : 2=2^1) n cursor
  change _+2 ≤ _ ∧ _+8 ≤ _ ∧ n+8 ≤ n+8
  exact ⟨by omega,by omega,le_rfl⟩

def signsCompute (n : ℕ) (f : Fin n → Bool) : (Finset (Fin n) × ℕ) × ℕ :=
  let out := SignMaskExecution.run n f
  let value : Finset (Fin n) :=
    ⟨(out.1.indices : Multiset (Fin n)),by
      change ((List.finRange n).filter f).Nodup
      exact (List.nodup_finRange n).filter _⟩
  ((value,out.2+1),SignMaskExecution.cells n f+4)

theorem signsCompute_value (n : ℕ) (f : Fin n → Bool) :
    (signsCompute n f).1.1 = bitsSubsetEquiv n f := by
  ext i
  simp [signsCompute,SignMaskExecution.run,bitsSubsetEquiv]

def signs (w n : ℕ) (hw : 1 ≤ w) : Execution (WordSeedRealization.signs w n hw) :=
  map (bits w n hw) (bitsSubsetEquiv n) (signsCompute n) (signsCompute_value n)

theorem signs_bounded (w n : ℕ) (hw : 1 ≤ w) :
    (signs w n hw).Bounded (9*n+8) (3*n+26) (3*n+24) := by
  unfold signs
  have hc (f : Fin n → Bool) : (signsCompute n f).2 ≤ 2*n+8 := by
    have h := SignMaskExecution.cells_le n f
    change SignMaskExecution.cells n f+4 ≤ _
    omega
  have hwork (f : Fin n → Bool) : (signsCompute n f).1.2 ≤ 4*n+3 := by
    simp only [signsCompute,SignMaskExecution.work]
    omega
  have h := map_bounded (bits w n hw) (bitsSubsetEquiv n) (signsCompute n)
    (signsCompute_value n) (5*n+3) (2*n+20) (n+8) (4*n+3) (2*n+8)
    (bits_bounded w n hw) hwork hc
  intro stream cursor
  have hh := h stream cursor
  exact ⟨by omega,hh.2.1.trans (by omega),by omega⟩

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
