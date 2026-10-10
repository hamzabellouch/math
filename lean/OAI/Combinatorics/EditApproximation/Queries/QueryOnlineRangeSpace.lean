import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineSources
import OAI.Combinatorics.EditApproximation.Binary.BinaryRepresentativeSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryTriangularSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem onlineIndexSetupAllocation_le_work {M n : ℕ} (H : ℕ) (band : List (Fin M → TargetInterval n)) :
    onlineIndexSetupAllocation H band ≤ (onlineIndexSetupWithWork H band).2 := by
  have hc := bandCoordinatesAllocation_le_work band
  have hs := binaryNaturalAddAllocation_le_work H (bandCoordinatesWithWork band).1.length
  have ho := binaryNaturalAddAllocation_le_work (bitWordValue (binaryNaturalAddWithWork H
    (bandCoordinatesWithWork band).1.length).1) 2
  have hp := bitPowerAllocation_le_work (binaryNaturalAddWithWork
    (bitWordValue (binaryNaturalAddWithWork H (bandCoordinatesWithWork band).1.length).1) 2).1 80
  unfold onlineIndexSetupAllocation onlineIndexSetupWithWork
  dsimp only
  omega



theorem queryOnlineRangeAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (P exponent H : ℕ) (tau : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ) (key : ℕ × TargetInterval ny)
    (h : ∀ i q, allocation i q ≤ (child i q).2) :
    queryOnlineRangeAllocation parent P exponent H tau child allocation key ≤
      (queryOnlineRangeWithWork parent P exponent H tau child key).2 := by
  let width := (saturatingSubtractWithWork parent.hi parent.lo).1
  let band := (preparedRepresentativeReadWithWork parent key.2 (bitWordValue width) key.1 P
    tau (inversePowerTwo exponent) child).1
  let setup := (onlineIndexSetupWithWork H band).1
  have hw := saturatingSubtractAllocation_le_work parent.hi parent.lo
  have hb := preparedRepresentativeReadAllocation_le_work parent key.2 (bitWordValue width) key.1 P
    tau (inversePowerTwo exponent) child allocation h
  have hs := onlineIndexSetupAllocation_le_work H band
  have hp := bitPowerAllocation_le_work setup.bits 80
  have hm := triangularMassAllocation_le_work (bitWordValue (bitPowerWithWork setup.bits 80).1)
  unfold queryOnlineRangeAllocation queryOnlineRangeWithWork
  dsimp only [width, band, setup] at hb hs hp hm ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
