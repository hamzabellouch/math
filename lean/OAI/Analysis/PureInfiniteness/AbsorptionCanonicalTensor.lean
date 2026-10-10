import OAI.Analysis.PureInfiniteness.AbsorptionFromHalfFlip
import OAI.Analysis.Nuclearity.MinimalTensorAlgebraic

namespace OAI

/-! Absorption through the faithful minimal tensor realization and the connected
approximate half-flip of O∞, as in Kirchberg (2006), Proposition 4.4(3),(5)
and Remark 4.6. -/
noncomputable section
open Filter
open scoped TensorProduct
namespace WeakPureInfiniteness

universe u
structure HalfFlipTensorModel (D : Type u) [CStarAlgebra D] where
  Carrier : Type (u + 1)
  [cstar : CStarAlgebra Carrier]
  map : D ⊗[ℂ] D →⋆ₐ[ℂ] Carrier
  injective : Function.Injective map
  dense : DenseRange map

attribute [instance] HalfFlipTensorModel.cstar

@[irreducible] def minimalHalfFlipTensorModel (D : Type u) [CStarAlgebra D] :
    HalfFlipTensorModel D := by
  letI := UnitalMinimalTensor.algebraicTensorUnital (A := D) (B := D)
  exact {
    Carrier := MinimalTensor D D
    cstar := inferInstance
    map := UnitalMinimalTensor.algebraicMap
    injective := UnitalMinimalTensor.algebraicMap_injective
    dense := UnitalMinimalTensor.algebraicMap_dense }

namespace Campaign
variable {A : Type u} [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem nuclear_absorption_of_tensorModel_halfFlip
    (hA : Nuclear A) (M : HalfFlipTensorModel OInfinity)
    (hh : CStarAbsorption.ConnectedApproximateInnerHalfFlip M.map)
    {n : ℕ} (hn : 1 ≤ n) (hF : FixedAmplification A n) : AbsorbsOInfinity A := by
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let : Fact ((U : Filter ℕ) ≤ atTop) := ⟨Ultrafilter.of_le _⟩
  exact nuclear_absorption_from_halfFlip U hA M.map M.injective M.dense hh hn hF

theorem nuclear_absorption_of_canonical_halfFlip
    (hA : Nuclear A)
    (hh : CStarAbsorption.ConnectedApproximateInnerHalfFlip
      (minimalHalfFlipTensorModel OInfinity).map)
    {n : ℕ} (hn : 1 ≤ n) (hF : FixedAmplification A n) : AbsorbsOInfinity A :=
  nuclear_absorption_of_tensorModel_halfFlip hA (minimalHalfFlipTensorModel OInfinity) hh hn hF

end Campaign
end WeakPureInfiniteness

end

end OAI
