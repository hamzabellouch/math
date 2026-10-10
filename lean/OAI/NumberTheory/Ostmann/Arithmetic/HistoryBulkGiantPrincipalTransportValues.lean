import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransportModulus

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport
open Construction HistoryPairPattern HistoryCRTIntegration HistorySignedSpectatorCRT
open HistoryBulkReferenceTests HistoryBulkResidueNormSum HistoryFrequencyResidues
open HistorySignedResidueFactorization HistoryBulkReferenceNewModuli
variable {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem newReferenceResidueTest_intCast (d : Decomposition) (K : ℕ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (newh newk : History l)
    (σ : Equiv.Perm (Fin (2^l)×Fin m))
    (x : Fin (2^l)×Fin m→(ZMod (frequencyModulus h k (K+2)))ˣ)
    (v : PairKey h k→ℤ)
    (fA : ZMod (rootModulus newh)×ZMod (rootModulus newh)→ℂ) (P Q : ℤ) :
    newReferenceResidueTest d K h k hs ks newh newk σ x v fA
      ((P:ZMod (newComparisonModulus newh h k outside K)),Q) =
    fA (P,Q)*residuePairSpectator (residueTransform d) outside outside.prod newh newk (P,Q)*
      independentRTest K h k σ (P,Q) x*primeResidueIndicatorAt h k hs ks v (P,Q) := by
  simp only [newReferenceResidueTest,referenceResidueTest,projectedRingPair,map_intCast]

end Ostmann.Arithmetic.HistoryBulkGiantPrincipalTransport

end

end OAI
