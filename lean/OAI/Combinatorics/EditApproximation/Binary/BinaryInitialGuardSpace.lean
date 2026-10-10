import OAI.Combinatorics.EditApproximation.Binary.BinaryNormalizationSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem dyadicScalesAllocation_le_work (N : ℕ) :
    dyadicScalesAllocation N ≤ (dyadicScalesWithWork N).2 := by
  have h := arithmeticMapAllocation_le_work
    (fun e => (bitWordValue (powerTwoWord e), e + 3)) (fun e => e + 1)
    (List.range (max 1 N.bits.length)) (fun _ _ => by dsimp only; omega)
  unfold dyadicScalesAllocation dyadicScalesWithWork
  dsimp only
  omega

namespace BinaryFraction



theorem initialScaleGuardAllocation_le_work (U b : ℕ) (A : BinaryFraction) :
    initialScaleGuardAllocation U b A ≤ (initialScaleGuardWithWork U b A).2 := by
  have h1 := canonicalMulAllocation_le_work A A
  have h2 := canonicalMulAllocation_le_work (nat 16) (canonicalMulWithWork A A).1
  have h3 := divAllocation_le_work (nat U) (canonicalMulWithWork (nat 16) (canonicalMulWithWork A A).1).1
  have h4 := canonicalMulAllocation_le_work (nat 4) A
  have h5 := canonicalMulAllocation_le_work (canonicalMulWithWork (nat 4) A).1 (nat U)
  have h6 := leAllocation_le_work (divWithWork (nat U) (canonicalMulWithWork (nat 16) (canonicalMulWithWork A A).1).1).1 (nat b)
  have h7 := leAllocation_le_work (nat b) (canonicalMulWithWork (canonicalMulWithWork (nat 4) A).1 (nat U)).1
  unfold initialScaleGuardAllocation initialScaleGuardWithWork
  dsimp only
  omega



theorem initialCenterGuardAllocation_le_work (b U : ℕ) (A : BinaryFraction) :
    initialCenterGuardAllocation b U A ≤ (initialCenterGuardWithWork b U A).2 := by
  have h1 := divAllocation_le_work (nat b) (nat 2)
  have h2 := canonicalMulAllocation_le_work (nat 4) A
  have h3 := canonicalMulAllocation_le_work (canonicalMulWithWork (nat 4) A).1 (nat b)
  have h4 := leAllocation_le_work (divWithWork (nat b) (nat 2)).1 (nat U)
  have h5 := leAllocation_le_work (nat U) (canonicalMulWithWork (canonicalMulWithWork (nat 4) A).1 (nat b)).1
  unfold initialCenterGuardAllocation initialCenterGuardWithWork
  dsimp only
  omega



theorem scaledSeedAllocation_le_work (U : ℕ) (a gap : BinaryFraction) :
    scaledSeedAllocation U a gap ≤ (scaledSeedWithWork U a gap).2 := by
  have hd := divAllocation_le_work (nat U) a
  have hc := naturalCeilingAllocation_le_work (divWithWork (nat U) a).1
  have hm := maxAllocation_le_work (ofNaturalWord (naturalCeilingWithWork (divWithWork (nat U) a).1).1) gap.absolute
  unfold scaledSeedAllocation scaledSeedWithWork
  dsimp only
  omega



theorem initialConeAllocation_le_work {n : ℕ} (sourceLength U : ℕ) (a L : BinaryFraction)
    (query center : TargetInterval n) :
    initialConeAllocation sourceLength U a L query center ≤
      (initialConeWithWork sourceLength (fun _ => U) a L query center).2 := by
  have h1 := stateGapAllocation_le_work sourceLength center
  have h2 := scaledSeedAllocation_le_work U a (stateGapWithWork sourceLength center).1
  have h3 := endpointDistanceAllocation_le_work query center
  have h4 := canonicalMulAllocation_le_work L (endpointDistanceWithWork query center).1
  have h5 := canonicalAddAllocation_le_work (scaledSeedWithWork U a (stateGapWithWork sourceLength center).1).1
    (canonicalMulWithWork L (endpointDistanceWithWork query center).1).1
  unfold initialConeAllocation initialConeWithWork
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
