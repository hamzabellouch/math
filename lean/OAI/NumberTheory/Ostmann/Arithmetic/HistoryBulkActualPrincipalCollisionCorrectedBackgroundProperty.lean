import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedSpectatorDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualRootReferenceFamily HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualPrincipalCollision

def correctedBackgroundErrorProperty (d : Decomposition) (Bs BD Bz H : ℝ)
    (k : ℕ) (L : ℝ) : Prop :=
    ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
      (∀j,spectator.law.mass (ds j)≠0) →
      ∀(l : ℕ)(_hl : l<k)
        (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
        (hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      ‖correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C spectator ds e he hV true-
        correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C spectator ds e he hV false‖≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C spectator ds e he hV true-
        correctedCollisionPrincipal (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E) C spectator ds e he hV false‖≤
          Real.exp (-H*(bulkSize k L:ℝ))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrected

end

end OAI
