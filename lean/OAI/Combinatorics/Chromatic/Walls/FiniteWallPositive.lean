import Mathlib
import OAI.Combinatorics.Chromatic.Walls.StringPositiveFactor
import OAI.Combinatorics.Chromatic.Shuffle.HNZeroFactor

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections EnergyLaurent
open QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]
local instance (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
variable (hΩ : ∀x,Ω x x=0)
variable (hgeom : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (θ : ℝ) (m : M)
variable (hm : ∀d∈slopeDimensions c η hc θ,0≤Ω (P d) m)

include hΩ hgeom hm in
lemma primitiveFactor_adjoint_positive :
    IntegralPositive Ω
      (push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)*
        C (Torus.X LaurentRay.vUnit Ω m)*
        invOfUnit (push w LaurentRay.vUnit Ω P (primitiveCountsSeries a κ c η hc θ)) 1) := by
  let dim : SlopeStringStart a c η hc θ → (I→ℕ) := fun s=>s.1.val.1.val
  let τ : (I→ℕ) →+ ℤ := (Ω.flip m).comp P
  let t : SlopeStringStart a c η hc θ → ℕ := fun s=>(τ (dim s)).toNat
  have hdim : ∀s,dim s∈slopeDimensions c η hc θ := fun s=>s.1.val.1.property
  have ht : ∀s,(t s:ℤ)=τ (dim s) := fun s=>Int.toNat_of_nonneg (hm _ (hdim s))
  have hi : ∀d∈slopeDimensions c η hc θ,∀e∈slopeDimensions c η hc θ,Ω (P d) (P e)=0 := by
    intro d hd e he
    rw [hgeom,eulerForm_slopeDimensions_symm a c η hc θ ⟨d,hd⟩ ⟨e,he⟩,sub_self]
  exact stringSeries_adjoint_positive (slopeStartRowType a c η hc θ) t dim
    (slopeStartParameter a κ c η hc θ) (primitiveCountsEnergy_admissible a κ c η hc θ)
    (slopeDimensions c η hc θ) hdim τ ht Ω P hi m (fun _=>rfl) w hΩ
    (primitiveCountsSeries_zero a κ c η hc θ)

variable (h : M →+ ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)
include hΩ hgeom hm hh in

theorem finiteInput_zero_adjoint_positive (ε : I → Bool)
    (ha : ∀i,a i i=elementaryDiagonal ε i) :
    let F := PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
      (zeroProject LaurentRay.vUnit Ω h) (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε))
    IntegralPositive Ω (F*C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1) := by
  dsimp only
  rw [←literalInput_primitiveFactor a κ c η hc w Ω P hgeom h θ hh ε ha]
  exact primitiveFactor_adjoint_positive a κ c η hc w Ω P hΩ hgeom θ m hm

end
end ElementaryPositivity.RawShuffle

end

end OAI
