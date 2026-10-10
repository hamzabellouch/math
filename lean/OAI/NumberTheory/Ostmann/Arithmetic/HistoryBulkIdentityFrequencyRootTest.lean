import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIdentityFrequency
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementTests

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIdentityFrequency
open Construction HistoryBulkSelectedIntegralReplacement HistoryBulkResidueRootAverage
open HistoryBulkResidueNormSum HistoryFrequencyResidues

theorem rootTest_identity (mixed : Bool) (d : Decomposition) {l m : ℕ}
    {V : ℕ→ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q) (K : ℕ)
    (x : Fin (2^l)×Fin m→(ZMod (outside.prod*(pairedFrequencyProduct h k)^(K+2)))ˣ) :
    rootTest true mixed d h k hs ks hp hV 1 K x =
      rootTest false mixed d h k hs ks hp hV 1 K x := by
  cases mixed
  · change independentUnit d h k hs ks hp hV 1 K x = canonicalUnit d h k hs ks hp hV 1 K x
    simp only [independentUnit,canonicalUnit,independentUnitTest,canonicalUnitTest,
      independentRTest_identity]
  · change independentMixed d h k hs ks hp hV 1 K x = canonicalMixed d h k hs ks hp hV 1 K x
    simp only [independentMixed,canonicalMixed,independentMixedTest,canonicalMixedTest,
      independentRTest_identity]

end Ostmann.Arithmetic.HistoryBulkIdentityFrequency

end

end OAI
