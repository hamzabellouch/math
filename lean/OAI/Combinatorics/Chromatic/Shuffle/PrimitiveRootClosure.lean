import Mathlib
import OAI.Combinatorics.Chromatic.Walls.StringRootClosure
import OAI.Combinatorics.Chromatic.Shuffle.HNZeroFactor

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
open QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (a : I→I→ℕ) (κ : I→ℤ) (c η : I→ℝ) (hc : ∀i,0<c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]
local instance (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M) (C : (J→ℤ)→+M)
variable (hgeom : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (hroot : ∀d,HasRootDegree C (WeightedTorusSeries.weight w d) (P d))
variable (θ : ℝ) (V : M→Prop) (hv : ∀d∈slopeDimensions c η hc θ,V (P d))

include hgeom hroot hv in
lemma primitiveFactor_rootClosure :
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C V)
      (push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)) := by
  let dim : SlopeStringStart a c η hc θ → (I→ℕ) := fun s=>s.1.val.1.val
  have hdim : ∀s,dim s∈slopeDimensions c η hc θ := fun s=>s.1.val.1.property
  have hi : ∀d∈slopeDimensions c η hc θ,∀e∈slopeDimensions c η hc θ,Ω (P d) (P e)=0 := by
    intro d hd e he
    rw [hgeom,eulerForm_slopeDimensions_symm a c η hc θ ⟨d,hd⟩ ⟨e,he⟩,sub_self]
  exact stringRoot_closure (slopeStartRowType a c η hc θ) dim
    (slopeStartParameter a κ c η hc θ) (primitiveCountsEnergy_admissible a κ c η hc θ)
    (slopeDimensions c η hc θ) hdim (fun s=>s.1.property) w Ω P C hi V
    (fun s=>hroot (dim s)) (fun s=>hv _ (hdim s))

variable (h : M→+ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)
include hgeom hroot hv hh in
theorem finiteInput_zero_rootClosure (ε : I→Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) :
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C V)
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h)
        (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε))) := by
  rw [←literalInput_primitiveFactor a κ c η hc w Ω P hgeom h θ hh ε ha]
  exact primitiveFactor_rootClosure a κ c η hc w Ω P C hgeom hroot θ V hv
end
end ElementaryPositivity.RawShuffle

end

end OAI
