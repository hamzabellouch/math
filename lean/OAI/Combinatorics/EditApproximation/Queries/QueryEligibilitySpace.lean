import OAI.Combinatorics.EditApproximation.Binary.BinaryGuardSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryRefinementLists
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem centerEligibilityAllocation_le_work (b F : ℕ) (a initial : BinaryFraction) :
    centerEligibilityAllocation b F a initial ≤ (centerEligibilityWithWork b F a initial).2 := by
  have hd := canonicalMulAllocation_le_work (nat 4) a
  have hlo := divAllocation_le_work (nat b) (canonicalMulWithWork (nat 4) a).1
  have hfac := canonicalMulAllocation_le_work (nat 8) (nat F)
  have hup := canonicalMulAllocation_le_work (canonicalMulWithWork (nat 8) (nat F)).1 (nat b)
  have hl := leAllocation_le_work (divWithWork (nat b) (canonicalMulWithWork (nat 4) a).1).1 initial
  have hh := leAllocation_le_work initial (canonicalMulWithWork (canonicalMulWithWork (nat 8) (nat F)).1 (nat b)).1
  unfold centerEligibilityAllocation centerEligibilityWithWork
  dsimp only
  omega



theorem refinementScaleGuardAllocation_le_work (F b : ℕ) (a w : BinaryFraction) :
    refinementScaleGuardAllocation F b a w ≤ (refinementScaleGuardWithWork F b a w).2 := by
  have hd := canonicalMulAllocation_le_work (nat 16) (nat F)
  have hlo := divAllocation_le_work w (canonicalMulWithWork (nat 16) (nat F)).1
  have hfac := canonicalMulAllocation_le_work (nat 8) a
  have hup := canonicalMulAllocation_le_work (canonicalMulWithWork (nat 8) a).1 w
  have hl := leAllocation_le_work (divWithWork w (canonicalMulWithWork (nat 16) (nat F)).1).1 (nat b)
  have hh := leAllocation_le_work (nat b) (canonicalMulWithWork (canonicalMulWithWork (nat 8) a).1 w).1
  unfold refinementScaleGuardAllocation refinementScaleGuardWithWork
  dsimp only
  omega



theorem queryExponentsAllocation_le_work (N F : ℕ) (a w : BinaryFraction) :
    queryExponentsAllocation N F a w ≤ (queryExponentsWithWork N F a w).2 := by
  have hf := filterAllocation_le_work
    (fun e => ((refinementScaleGuardWithWork F (2 ^ e) a w).1,
      (refinementScaleGuardWithWork F (2 ^ e) a w).2 + e + 2))
    (fun e => refinementScaleGuardAllocation F (2 ^ e) a w + e + 1)
    (List.range (max 1 N.bits.length)) (by
      intro e _
      have h := refinementScaleGuardAllocation_le_work F (2 ^ e) a w
      dsimp only
      omega)
  unfold queryExponentsAllocation queryExponentsWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
