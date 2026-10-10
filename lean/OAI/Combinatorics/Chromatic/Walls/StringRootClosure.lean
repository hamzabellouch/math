import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.StringLiteralClosure

namespace OAI

section
namespace ElementaryPositivity.UnitSelections
open SignedMultiplicity RawShuffle EnergyLaurent QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {S I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (a : S→ℕ) (dim : S→(I→ℕ)) (k : S→ℤ)
variable (he : ∀d,Admissible (stringEnergy a dim k d))
variable (D : AddSubmonoid (I→ℕ)) (hdim : ∀s,dim s∈D) (h0 : ∀s,dim s≠0)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M) (C : (J→ℤ)→+M)
variable (hiso : ∀d∈D,∀e∈D,Ω (P d) (P e)=0)
variable (V : M→Prop) (hr : ∀s,HasRootDegree C (WeightedTorusSeries.weight w (dim s)) (P (dim s)))
variable (hv : ∀s,V (P (dim s)))

def stringWallDatum (s : S) : WallUnitDatum M :=
  ⟨WeightedTorusSeries.weight w (dim s),P (dim s),a s,k s⟩

omit [DecidableEq I] in
include h0 hr hv in
lemma finiteStringProducts_rootProducts :
    finiteStringProducts a dim k w Ω P ⊆ literalRootProducts Ω C V := by
  rintro F ⟨l,hl,rfl⟩
  refine ⟨l.map (stringWallDatum a dim k w P),?_,?_⟩
  · intro u hu
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hu
    exact ⟨weight_pos w (dim s) (h0 s),hr s,hv s⟩
  · rw [List.map_map]
    rfl

include h0 hdim hiso hr hv in
theorem stringRoot_closure :
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C V)
      (push w LaurentRay.vUnit Ω P (stringSeries a dim k he)) :=
  (stringLiteral_closure a dim k he D hdim h0 w Ω P hiso).mono LaurentRay.vUnit Ω
    (finiteStringProducts_rootProducts a dim k h0 w Ω P C V hr hv)
end
end ElementaryPositivity.UnitSelections

end

end OAI
