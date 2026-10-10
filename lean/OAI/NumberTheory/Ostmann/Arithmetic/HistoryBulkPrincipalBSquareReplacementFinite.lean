import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum
open HistoryPairVariableBSquareErrorSelected HistoryBulkPrincipalCollisionError
open HistoryPairPattern HistoryPairRepresentatives HistoryPairKernelReplacement
open HistoryCRTIntegration HistorySignedResidueFactorization HistoryBulkReferenceTests ResidueHaar
attribute [local instance] Classical.propDecidable
local instance squareFiniteInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
variable {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
variable {b : Block p → CommonSample C.sources
    (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)}

def bMean (r : PrincipalSquareReference C outside l p b) (mixed : Bool) : ℂ :=
  let D := r.square.leftDraw
  let F := r.square.rightDraw
  letI : NeZero (representativeModulus D.history F.history) :=
    ⟨(representativeModulus_pos D.history F.history D.supported F.supported).ne'⟩
  if mixed then
    average (fun z : MixedPair (representativeModulus D.history F.history) =>
      primeResidueIndicatorAt D.history F.history D.supported F.supported r.square.sample (z.1,z.2))
  else
    average (fun z : UnitPair (representativeModulus D.history F.history) =>
      primeResidueIndicatorAt D.history F.history D.supported F.supported r.square.sample (z.1,z.2))

def probabilityProduct (r : PrincipalSquareReference C outside l p b) (mixed : Bool) : ℂ :=
  ((∏q : Representative r.square.leftDraw.history r.square.rightDraw.history,
    actualProbability mixed r.square.leftDraw.history r.square.rightDraw.history
      r.square.leftDraw.supported r.square.rightDraw.supported q
      (prime r.square.leftDraw.history r.square.rightDraw.history q) r.square.sample):ℝ)

theorem bMean_sub_probabilityProduct (r : PrincipalSquareReference C outside l p b)
    (mixed : Bool) : bMean r mixed-probabilityProduct r mixed=
      decodedBProbabilityError mixed r.square.leftDraw r.square.rightDraw r.square.sample := rfl

def optionalPrincipalBFactor (R : ReferenceFamily C outside l) (probability mixed : Bool)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  match R p b with
  | none => 0
  | some r => if probability then probabilityProduct r mixed else bMean r mixed

def principalBExpressionSum (R : ReferenceFamily C outside l) (probability corrected mixed : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop) : ℂ :=
  let origin := pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l
  let τ := pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l
  ∑p:Pattern τ,∑b:BlockDraw p (CommonSample C.sources origin),
    (((∏q,blockWeight p (sourceWeight C.sources origin) q (b.val q))*
      (∏i,((expand p b i).val:ℝ)):ℝ):ℂ)*
    ((if mask p b.val then (1:ℂ) else 0)*
      (principalAmplitude R corrected mixed p b*optionalPrincipalBFactor R probability mixed p b.val))

theorem principalBExpressionSum_sub (R : ReferenceFamily C outside l) (corrected mixed : Bool)
    (mask : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      (Block p → CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) → Prop) :
    principalBExpressionSum R false corrected mixed mask-
      principalBExpressionSum R true corrected mixed mask=principalBErrorSum R corrected mixed mask := by
  unfold principalBExpressionSum principalBErrorSum weightedOriginalDecodedBErrorSum
  simp only [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  cases hr : R p b.val with
  | none => simp [optionalPrincipalBFactor,optionalDecodedBError,squareReferences,hr]
  | some r =>
    simp only [optionalPrincipalBFactor,hr,Bool.false_eq_true,ite_false,ite_true,
      optionalDecodedBError,squareReferences,Option.map_some]
    split_ifs <;> simp only [Complex.ofReal_one,Complex.ofReal_zero,one_mul,zero_mul]
    · rw [←mul_sub,←mul_sub,bMean_sub_probabilityProduct]
    · simp

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReplacement

end

end OAI
