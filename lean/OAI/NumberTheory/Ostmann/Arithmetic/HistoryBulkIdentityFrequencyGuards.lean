import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIdentityFrequencyBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIdentityFrequency
open Construction Characters FrequencyExposure BinaryExposure HistoryFrequencyResidues

theorem knownPairFrequencyUnits_split (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) {l : ℕ} (h k : History l)
    (p : List Bool) (c : PairedContext R)
    (z : BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l) :
    knownPairFrequencyUnits K R d f h k p c z ↔
      knownPairFrequencyUnits K R (fun p => leftData (d p))
        (fun p => leftFactors (f p)) h h p (leftContext c) z ∧
      knownPairFrequencyUnits K R (fun p => rightData (d p))
        (fun p => rightFactors (f p)) k k p (rightContext c) z := by
  induction h generalizing p c with
  | leaf a =>
    cases k
    simp only [knownPairFrequencyUnits,leftContext,rightContext,and_self]
  | @node l a pivot u hp hm left right ihl ihr =>
    cases k with
    | node a' pivot' u' hp' hm' left' right' =>
      simp only [knownPairFrequencyUnits,exposureStep_left,exposureStep_right]
      rw [ihl,ihr]
      simp only [leftContext,rightContext]
      tauto

end Ostmann.Arithmetic.HistoryBulkIdentityFrequency

end

end OAI
