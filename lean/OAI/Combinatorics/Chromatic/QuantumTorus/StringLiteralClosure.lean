import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.SeriesApproximation
import OAI.Combinatorics.Chromatic.QuantumTorus.StringSumPush
import OAI.Combinatorics.Chromatic.Walls.WeightedCompletion

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {S I : Type*} [Fintype I] [DecidableEq I]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D) (h0 : ∀s,dim s≠0)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M] (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)

def finiteStringProducts : Set (PowerSeries (Torus LaurentRay.vUnit Ω)) :=
  {F | ∃l : List S,l.Nodup ∧ F=(l.map (stringLiteralUnit a dim k w Ω P)).prod}

include h0 hdim hiso in
lemma finiteStart_literal (T : Finset S) :
    push w LaurentRay.vUnit Ω P (finiteStartSeries a dim k he T)∈finiteStringProducts a dim k w Ω P := by
  classical
  obtain ⟨l,hl,hall,H⟩:=finiteString_literal (fun s:T=>a s.val) (fun s:T=>dim s.val)
    (fun s:T=>k s.val) (finiteStart_admissible a dim k he T) D (fun s=>hdim s.val)
    (fun s=>h0 s.val) w Ω P hiso
  refine ⟨l.map Subtype.val,hl.map Subtype.val_injective,?_⟩
  rw [List.map_map]
  change push w LaurentRay.vUnit Ω P (stringSeries (fun s:T=>a s.val)
    (fun s:T=>dim s.val) (fun s:T=>k s.val) (finiteStart_admissible a dim k he T)) =
      (l.map (stringLiteralUnit (fun s:T=>a s.val) (fun s:T=>dim s.val)
        (fun s:T=>k s.val) w Ω P)).prod
  exact H

include h0 hdim hiso in

theorem stringLiteral_closure :
    InPrecisionClosure LaurentRay.vUnit Ω (finiteStringProducts a dim k w Ω P)
      (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) := by
  apply InPrecisionClosure.of_converges LaurentRay.vUnit Ω (Filter.atTop : Filter (Finset S))
    (push_converges w LaurentRay.vUnit Ω P Filter.atTop
      (finiteStartSeries_converges a dim k he))
  exact Filter.Eventually.of_forall (fun T=>inPrecisionClosure_self LaurentRay.vUnit Ω
    (finiteStart_literal a dim k he D hdim h0 w Ω P hiso T))
end
end ElementaryPositivity.UnitSelections

end

end OAI
