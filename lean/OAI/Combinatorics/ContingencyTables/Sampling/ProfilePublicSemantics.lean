import OAI.Combinatorics.ContingencyTables.Sampling.ProfilePublicProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileScheduleSemantics

namespace OAI

/-! # Exact public input/output semantics of the profile sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.LiteralParse MatchingFPRAS.LiteralCodec

lemma samplingPrecision_spec (m n : ℕ) (rs cs : List ℕ) (k : ℕ) (tail : List ℕ)
    (hr : rs.length=m) (hc : cs.length=n) :
    samplingPrecision (m::n::(rs++cs++k::tail))=k := by
  change ((m::n::(rs++cs++k::tail)).drop (2+m+n)).headD 0=k
  have hlen : 2+m+n=(m::n::(rs++cs)).length := by
    simp only [List.length_cons,List.length_append,hr,hc]
    omega
  rw [hlen]
  change (((m::n::(rs++cs))++k::tail).drop (m::n::(rs++cs)).length).headD 0=k
  rw [List.drop_left]
  rfl

lemma samplingInput_spec (m n : ℕ) (rs cs : List ℕ) (k : ℕ)
    (hr : rs.length=m) (hc : cs.length=n) :
    samplingInput (m::n::(rs++cs++[k]))=((rs,cs),k) := by
  apply Prod.ext
  · exact GreedyFeasibleTable.marginLists_spec m n rs cs [k] hr hc
  · exact samplingPrecision_spec m n rs cs k [] hr hc

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open MatchingFPRAS.LiteralParse MatchingFPRAS.LiteralCodec
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

lemma parsedSampling_spec (k : ℕ) :
    parsedSampling (Algorithms.encodeSamplingInput r c k)=((List.ofFn r,List.ofFn c),k) := by
  unfold parsedSampling Algorithms.encodeSamplingInput
  rw [GreedyFeasibleTable.encodeMargins_natWords]
  have he : MatchingFPRAS.encodeNat k=([k].flatMap MatchingFPRAS.encodeNat) := by
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [he,←List.flatMap_append,GreedyFeasibleTable.parse_natWords]
  simp only [List.cons_append,List.append_assoc]
  simpa only [List.append_assoc] using
    samplingInput_spec m n (List.ofFn r) (List.ofFn c) k List.length_ofFn List.length_ofFn

lemma publicWordCount_spec (k : ℕ) :
    publicWordCount (Algorithms.encodeSamplingInput r c k)=finiteSamplerBits r c k := by
  rw [publicWordCount,parsedSampling_spec,parameterWordCount_ofFn]

/-- Each concrete public word prints the matrix of the proved finite draw. -/
theorem publicSampling_spec
    (hr : 0<(largeIndices (d^20,List.ofFn r)).length)
    (hc : 0<(largeIndices (d^20,List.ofFn c)).length)
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ)
    (bits : Fin (finiteSamplerBits r c k) → Bool) :
    publicSampling (Algorithms.encodeSamplingInput r c k,List.ofFn bits)=
      Algorithms.encodeMatrix (listedOuterDraw r c (computedCellEquiv r c) hr hc b
        (outerAccuracy d b k) (smallBinaryLength_parameters r c).1
        (tableState r c (GreedyFeasibleTable.table r c htotal))
        (outerSteps d b k) (outerTrials d k) (GreedyFeasibleTable.table r c htotal) bits).val := by
  rw [publicSampling,parsedSampling_spec,samplingMatrix_code r c hr hc htotal]
  exact GreedyFeasibleTable.printMatrix_ofFn _

end
end ContingencyTables.SmallGraphProfiles

end OAI
