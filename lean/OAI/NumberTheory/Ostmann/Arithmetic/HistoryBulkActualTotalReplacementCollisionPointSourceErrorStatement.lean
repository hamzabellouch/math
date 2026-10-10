import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePlainCollisionDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointSourceValueDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkActualPrincipalCollision

def PlainCollisionSourceError (d : Decomposition) (Bs BD Bz H : ℝ) (k : ℕ) (L : ℝ) : Prop :=
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
      ∀hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
      ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
      (∀q,spectator.law.mass (ds q)≠0) →
      ∀(l : ℕ)(hl : l≤k)(σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
        (mixed : Bool)(hV : ∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      ‖plainKernelCollisionSourceValue (l:=l) C spectator ds hactual hl σ mixed hV-
        plainCollisionSourceBulkValue (l:=l) C spectator ds hactual hl σ mixed hV‖≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖plainKernelCollisionSourceValue (l:=l) C spectator ds hactual hl σ mixed hV-
        plainCollisionSourceBulkValue (l:=l) C spectator ds hactual hl σ mixed hV‖≤
          Real.exp (-H*(bulkSize k L:ℝ))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
