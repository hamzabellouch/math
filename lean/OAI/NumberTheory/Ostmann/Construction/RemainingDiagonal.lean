import OAI.NumberTheory.Ostmann.Construction.ActualIntegerTransfer
import OAI.NumberTheory.Ostmann.Construction.RemainingSupport
import OAI.NumberTheory.Ostmann.Construction.RowDiagonal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
section
variable (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))

abbrev RemainingTerm :=
  RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant × AllowedFrequency V l

def remainingTermMass (z : RemainingTerm sources seed V giant l) : ℝ :=
  (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass z.1

def remainingTermExactTag (z : RemainingTerm sources seed V giant l) : ℚ :=
  remainingExactTag sources (Template.remainder (l+1) (Template.current seed l)) giant z.1 z.2.val

def remainingTermModularTag (z : RemainingTerm sources seed V giant l) :
    ZMod (halfProduct p (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u)) :=
  modFraction (halfProduct p (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u))
    z.2.val (remainingProduct sources (Template.remainder (l+1) (Template.current seed l)) giant z.1)

def remainingTermValue (z : RemainingTerm sources seed V giant l) : ℂ :=
  remainingIntegrand d P sources seed V giant X G bins outside l p u z.1 z.2

def remainingDiagonal : ℝ :=
  (refinedRowDiagonal (remainingTermMass sources seed V giant l)
    (remainingTermExactTag sources seed V giant l)
    (remainingTermValue d P sources seed V giant X G bins outside l p u)).re

def remainingOffDiagonal : ℂ :=
  refinedRowOffDiagonal (remainingTermMass sources seed V giant l)
    (remainingTermModularTag sources seed V giant l p u)
    (remainingTermExactTag sources seed V giant l)
    (remainingTermValue d P sources seed V giant X G bins outside l p u)

theorem remainingDiagonal_nonneg :
    0≤remainingDiagonal d P sources seed V giant X G bins outside l p u :=
  refinedRowDiagonal_nonneg _ _ _

theorem remainingRowSquare_split [NeZero p] :
    (remainingRowSquare d P sources seed V giant X G bins outside l u p:ℂ)=
      (remainingDiagonal d P sources seed V giant X G bins outside l p u:ℂ)+
      remainingOffDiagonal d P sources seed V giant X G bins outside l p u := by
  rw [remainingRowSquare_eq]
  have hs := refinedRow_split (remainingTermMass sources seed V giant l)
    (remainingTermModularTag sources seed V giant l p u)
    (remainingTermExactTag sources seed V giant l)
    (remainingTermValue d P sources seed V giant X G bins outside l p u)
    (fun x y hx hy he => remainingExactTag_refines d P sources seed V giant X G bins outside l p u
      x.1 y.1 x.2 y.2 hx hy he)
  have hd : refinedRowDiagonal (remainingTermMass sources seed V giant l)
      (remainingTermExactTag sources seed V giant l)
      (remainingTermValue d P sources seed V giant X G bins outside l p u)=
      (remainingDiagonal d P sources seed V giant X G bins outside l p u:ℂ) := by
    apply Complex.ext
    · rfl
    · exact (refinedRowDiagonal_real _ _ _).trans (Complex.ofReal_im _).symm
  rw [hd] at hs
  exact hs

end
end Ostmann.Construction

end

end OAI
