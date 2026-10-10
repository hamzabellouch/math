import OAI.Combinatorics.EditApproximation.Binary.BinaryTriangularChoice
import OAI.Combinatorics.EditApproximation.Queries.QueryBufferSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem triangularMassAllocation_le_work (K : ℕ) :
    triangularMassAllocation K ≤ (triangularMassWithWork K).2 := by
  have ha := bitAddAllocation_le_work K.bits (1 : ℕ).bits false
  have hm := bitMulAllocation_le_work K.bits (bitWordValue (binaryNaturalAddWithWork K 1).1).bits
  have hd := bitDivModAllocation_le_work (2 : ℕ).bits
    (bitWordValue (binaryNaturalMulWithWork K (bitWordValue (binaryNaturalAddWithWork K 1).1)).1).bits
  unfold triangularMassAllocation triangularMassWithWork binaryNaturalAddWithWork
    binaryNaturalMulWithWork binaryNaturalDivModWithWork at *
  dsimp only at *
  omega

/-- Allocate the exact threshold words visited by the triangular sampler.
The sampled integer and thresholds are already bounded finite words. -/


theorem triangularChoiceAllocation_le_work (K : ℕ) (integer : Fin (optimizerTriangularMass K)) :
    triangularChoiceAllocation K integer ≤ (triangularChoiceWithWork K integer).2 := by
  induction K with
  | zero => exact Fin.elim0 integer
  | succ K ih =>
    have ht := triangularMassAllocation_le_work K
    have hc := bitCompareWithWork_input_cells integer.val.bits
      (bitWordValue (triangularMassWithWork K).1).bits
    change _ ≤ (binaryNaturalCompareWithWork integer.val (bitWordValue (triangularMassWithWork K).1)).2 at hc
    change (let threshold := triangularMassWithWork K
      let test := binaryNaturalCompareWithWork integer.val (bitWordValue threshold.1)
      let localCells := triangularMassAllocation K + integer.val.bits.length +
        (bitWordValue threshold.1).bits.length
      if h : test.1 = .lt then
        let hsmall : integer.val < optimizerTriangularMass K := by
          have hp := (binaryNaturalCompareWithWork_lt _ _).mp h
          simpa only [threshold, triangularMassWithWork_value] using hp
        localCells + triangularChoiceAllocation K ⟨integer.val, hsmall⟩
      else localCells) ≤
      (let threshold := triangularMassWithWork K
       let test := binaryNaturalCompareWithWork integer.val (bitWordValue threshold.1)
       if h : test.1 = .lt then
         let hsmall : integer.val < optimizerTriangularMass K := by
           have hp := (binaryNaturalCompareWithWork_lt _ _).mp h
           simpa only [threshold, triangularMassWithWork_value] using hp
         let chosen := triangularChoiceWithWork K ⟨integer.val, hsmall⟩
         (chosen.1.castSucc, threshold.2 + test.2 + chosen.2 + 2)
       else (⟨K, Nat.lt_succ_self K⟩, threshold.2 + test.2 + 1) : Fin (K + 1) × ℕ).2
    dsimp only
    split_ifs with h
    · have hsmall : integer.val < optimizerTriangularMass K := by
        have hp := (binaryNaturalCompareWithWork_lt _ _).mp h
        simpa only [triangularMassWithWork_value] using hp
      have hnext := ih ⟨integer.val, hsmall⟩
      dsimp only
      exact (Nat.add_le_add
        ((Nat.add_assoc _ _ _).le.trans (Nat.add_le_add ht hc)) hnext).trans
        (Nat.le_add_right _ 2)
    · dsimp only
      exact ((Nat.add_assoc _ _ _).le.trans (Nat.add_le_add ht hc)).trans (Nat.le_succ _)

end EditApproximation

end OAI
