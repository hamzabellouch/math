import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIdentityFrequencyGuards
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIdentityFrequencyLeaf

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIdentityFrequency
open Construction Characters FrequencyExposure BinaryExposure HistoryFrequencyResidues
open HistoryPairedFrequencyAverage HistorySignedResidueFactorization

theorem leafIndicator_split (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h k : History l)
    (p : List Bool) (c : PairedContext R)
    (z : BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l) :
    leafIndicator K R d f h k p c z =
      leafIndicator K R (fun p => leftData (d p)) (fun p => leftFactors (f p))
        h h p (leftContext c) z *
      leafIndicator K R (fun p => rightData (d p)) (fun p => rightFactors (f p))
        k k p (rightContext c) z := by
  simp only [leafIndicator]
  rw [knownPairFrequencyUnits_split,leafAdmissible_split,← guardIndicator_and]
  congr 1
  apply propext
  tauto

end Ostmann.Arithmetic.HistoryBulkIdentityFrequency

end

end OAI
