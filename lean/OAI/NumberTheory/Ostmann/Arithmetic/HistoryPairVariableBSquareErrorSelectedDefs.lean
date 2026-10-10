import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedPointwise
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedReferences
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedSum

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum
open HistoryPairVariableBSquareErrorSelectedKernel
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sourceReferences (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,(b:Block p → CommonSample C.sources origin) →
      Option (DecodedSquareReference C origin τ p b V outside l)) :
    ∀p:Pattern τ,(b:Block p → CommonSample C.sources origin) →
      Option (SourcePatternReference C origin τ p b V outside l) :=
  fun p b => (refs p b).map DecodedSquareReference.toSourceReference

def optionalDecodedBError (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,(b:Block p → CommonSample C.sources origin) →
      Option (DecodedSquareReference C origin τ p b V outside l))
    (p : Pattern τ) (b : Block p → CommonSample C.sources origin) : ℂ :=
  match refs p b with
  | none => 0
  | some r => decodedBProbabilityError mixed r.leftDraw r.rightDraw r.sample

def originalDecodedBErrorSum (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin τ : ι → ℕ) (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ) (l : ℕ)
    (refs : ∀p:Pattern τ,(b:Block p → CommonSample C.sources origin) →
      Option (DecodedSquareReference C origin τ p b V outside l))
    (mask : ∀p:Pattern τ,(Block p → CommonSample C.sources origin) → ℝ) : ℂ :=
  ∑p:Pattern τ,∑b:BlockDraw p (CommonSample C.sources origin),
    (((∏q,blockWeight p (sourceWeight C.sources origin) q (b.val q))*
      (∏i:ι,((expand p b i).val:ℝ)):ℝ):ℂ)*
    ((mask p b.val:ℂ)*optionalDecodedBError C origin τ mixed V outside l refs p b.val)

end Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected

end

end OAI
