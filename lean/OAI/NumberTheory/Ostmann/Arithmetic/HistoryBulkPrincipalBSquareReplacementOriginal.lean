import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationOriginalBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable
local instance squareOriginalInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

def principalValue (R : ReferenceFamily C outside l) (corrected mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  match R p b with
  | none => 0
  | some r => r.principal.value corrected mixed r.newBulk

def principalPatternFactor (R : ReferenceFamily C outside l) (probability corrected mixed : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  (if mask p b then (1:ℂ) else 0) *
    (principalValue R corrected mixed p b * optionalPrincipalBFactor R probability mixed p b)

theorem principalBExpressionSum_eq_patternComplexSum
    (R : ReferenceFamily C outside l) (probability corrected mixed : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop) :
    principalBExpressionSum R probability corrected mixed mask=
      patternComplexSum C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (principalPatternFactor R probability corrected mixed mask) := by
  rw [←sum_pattern_original_eq_patternComplexSum]
  unfold principalBExpressionSum
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  unfold principalPatternFactor principalValue principalAmplitude
  by_cases hm : mask p b.val <;> simp only [hm,ite_true,ite_false,one_mul,zero_mul,mul_zero]
  congr 1
  cases R p b.val <;> rfl

theorem patternComplexSum_sub_eq_principalBErrorSum
    (R : ReferenceFamily C outside l) (corrected mixed : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop) :
    patternComplexSum C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (principalPatternFactor R false corrected mixed mask)-
      patternComplexSum C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (principalPatternFactor R true corrected mixed mask)=principalBErrorSum R corrected mixed mask := by
  rw [←principalBExpressionSum_eq_patternComplexSum,←principalBExpressionSum_eq_patternComplexSum]
  exact principalBExpressionSum_sub R corrected mixed mask

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement

end

end OAI
