import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationRootTestDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementOriginal

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum HistoryPairVariableBSquareErrorSelected
open HistoryBulkFibreGiantApproximation HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable
local instance squareDensityBasicInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

abbrev DensitySources (C : InitialSourceChoice d Bs BD Bz k L E) (l : ℕ) :=
  ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
    (Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
        Frame.Source (C:=C) (l:=l)

def densityFactor (X : DensitySources C l) (mixed : Bool) (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  if mixed then Frame.extractedDensity (C:=C) (X p b) else 1

theorem norm_densityFactor_le (X : DensitySources C l) (mixed : Bool) (p b) :
    ‖densityFactor X mixed p b‖≤1 := by
  cases mixed
  · exact le_of_eq (norm_one : ‖(1:ℂ)‖=1)
  · exact Frame.norm_extractedDensity_le (X p b)

def densityAmplitude (R : ReferenceFamily C outside l) (X : DensitySources C l)
    (corrected mixed : Bool) (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : BlockDraw p (CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))) : ℂ :=
  densityFactor X mixed p b.val * principalAmplitude R corrected mixed p b

def densityBErrorSum (R : ReferenceFamily C outside l) (X : DensitySources C l)
    (corrected mixed : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop) : ℂ :=
  weightedOriginalDecodedBErrorSum C
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
    mixed (frequencyBound Bs BD Bz k L) outside l (squareReferences R)
    (fun p b=>if mask p b then 1 else 0) (densityAmplitude R X corrected mixed)

def densityPatternFactor (R : ReferenceFamily C outside l) (X : DensitySources C l)
    (probability corrected mixed : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop) (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  densityFactor X mixed p b * principalPatternFactor R probability corrected mixed mask p b

def densityBExpressionSum (R : ReferenceFamily C outside l) (X : DensitySources C l)
    (probability corrected mixed : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop) : ℂ :=
  patternComplexSum C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
    (densityPatternFactor R X probability corrected mixed mask)

theorem densityBExpressionSum_sub (R : ReferenceFamily C outside l) (X : DensitySources C l)
    (corrected mixed : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop) :
    densityBExpressionSum R X false corrected mixed mask-
      densityBExpressionSum R X true corrected mixed mask=densityBErrorSum R X corrected mixed mask := by
  unfold densityBExpressionSum densityBErrorSum weightedOriginalDecodedBErrorSum
  rw [←sum_pattern_original_eq_patternComplexSum,←sum_pattern_original_eq_patternComplexSum]
  simp only [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  unfold densityPatternFactor principalPatternFactor densityAmplitude principalValue principalAmplitude
  cases hr : R p b.val with
  | none => simp [optionalPrincipalBFactor,optionalDecodedBError,squareReferences,hr]
  | some r =>
    simp only [optionalPrincipalBFactor,hr,Bool.false_eq_true,ite_false,ite_true,
      optionalDecodedBError,squareReferences,Option.map_some]
    split_ifs <;> simp only [Complex.ofReal_one,Complex.ofReal_zero,one_mul,zero_mul,mul_zero]
    · rw [←bMean_sub_probabilityProduct]
      ring
    · simp

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement

end

end OAI
