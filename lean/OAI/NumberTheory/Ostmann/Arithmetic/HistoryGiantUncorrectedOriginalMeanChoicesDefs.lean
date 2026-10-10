import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantOriginalMeanChoicesDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMeanApproximation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean
open Construction Conclusion HistoryGiantReferenceMean
open HistoryGiantOriginalMeanFactorization (Seed Current Choices history compensationFactor compensationFactor_eq)
open HistoryGiantOriginalMeanFactorization (PrimeReference MixedReference)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
variable (s t : ℤ) (c e : Choices (l:=l) C)

def primeReferenceMain (hout : ∀q∈outside,q.Prime)
    (r : Option (PrimeReference C outside x y s t c e)) : ℂ :=
  match r with
  | none => 0
  | some r => compensationFactor C x y s t c e *
      primeMainTerm C outside _ _ r.left_supported r.right_supported hout (k+2)

def mixedReferenceMain (hout : ∀q∈outside,q.Prime)
    (r : Option (MixedReference C outside x y s t c e)) : ℂ :=
  match r with
  | none => 0
  | some r => compensationFactor C x y s t c e *
      mixedMainTerm C outside _ _ r.left_supported r.right_supported hout (k+2)

end Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean

end

end OAI
