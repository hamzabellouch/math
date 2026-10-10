import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedHistoryExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedSeparatorPreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSamplingBounds

namespace OAI

/-! # Executed separator families complete the representation history -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

variable {n : ℕ}

private theorem clog_le (k w : ℕ) (h : k ≤ w) : Nat.clog 2 k ≤ w :=
  (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans h

def separatorDraws (R : RepresentationSetup n) (h : R.PrimeHistory)
    (hn : 2200 ≤ n) (w : ℕ)
    (hw : Nat.clog 2 (2*RepresentationSetup.blockHalf n 0) ≤ w) :
    Execution (WordSeedRealization.separatorDraws R h hn w hw) := by
  unfold WordSeedRealization.separatorDraws RepresentationSetup.separatorParameters
  exact familiesPrepared _ _ _ _ _ _ w n hw

def bucketHistory (I : Instance n) (hn : 10000 ≤ n) (w : ℕ) (hw : 3*n+1 ≤ w) :
    Execution (WordSeedRealization.bucketHistory (canonicalRepresentationData I).zeroSetup hn w hw) :=
  bind (extraHistory I (by omega) w hw)
    (fun h => (canonicalRepresentationData I).zeroSetup.SeparatorDraws h.1.1 (by omega))
    (fun h => (canonicalRepresentationData I).zeroSetup.separatorCoupling h.1.1 (by omega))
    (fun h => WordSeedRealization.separatorDraws _ h.1.1 (by omega) w
      (clog_le _ _ (by
        have hg := WordSamplingBounds.family_width n
        omega)))
    (fun h => separatorDraws _ h.1.1 (by omega) w
      (clog_le _ _ (by
        have hg := WordSamplingBounds.family_width n
        omega)))

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
