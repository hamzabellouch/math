import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrectedStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction Conclusion HistoryBulkIndependentFibreReference
open HistoryBulkActualRootReferenceFamily Filter
attribute [local instance] Classical.propDecidable

def SelectedKernelIndexEstimate (d : Decomposition)
    (Bs BD Bz H : ℝ) (k : ℕ) : Prop :=
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ q:spectator.Sample, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (q:ℕ) ∧
        Real.log (q:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ (outside : List ℕ) (_houtside : ∀ q∈outside, ∃ r:spectator.Sample, (r:ℕ)=q)
        (hlen : outside.length=2*(bulkSize k L/2)),
      ∀ l, l<k →
      ∀ (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
        (he : PreservesRemainingBands _ e),
      ∃ (hprime : ∀ q∈outside, q.Prime)
        (hV : ∀ q∈outside, ∀ j≤l, frequencyBound Bs BD Bz k L j<q),
      ‖(∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
          selectedKernelMean (l:=l) C p outside e he hlen hprime hV i.1 i.2.1 i.2.2 false)-
        (∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
          selectedKernelMean (l:=l) C p outside e he hlen hprime hV i.1 i.2.1 i.2.2 true)‖ ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖(∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
          selectedKernelMean (l:=l) C p outside e he hlen hprime hV i.1 i.2.1 i.2.2 false)-
        (∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,
          selectedKernelMean (l:=l) C p outside e he hlen hprime hV i.1 i.2.1 i.2.2 true)‖ ≤
          Real.exp (-H*(bulkSize k L:ℝ))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
