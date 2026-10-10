import OAI.Analysis.PureInfiniteness.CentralSequenceAbsorption
import OAI.Analysis.OInfinity.Simple
import OAI.Analysis.OInfinity.TensorNorm

namespace OAI

/-! Absorption from a central embedding and a connected approximate half-flip,
using the nuclearity and simplicity of O∞ and Kirchberg's criterion. -/

noncomputable section
open scoped TensorProduct
open Filter

namespace WeakPureInfiniteness.Campaign

universe u w
variable {A : Type u} [NonUnitalCStarAlgebra A]
  [TopologicalSpace.SeparableSpace A]

local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- The full absorption corollary, still conditional on the published central
embedding and connected half-flip; O∞ nuclearity and simplicity are proved. -/
theorem nuclear_absorption_from_central_embedding_and_halfFlip
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (hcentral : Nontrivial A → Nuclear A → StronglyPurelyInfinite A →
      Nonempty (OInfinity →⋆ₐ[ℂ]
        NonunitalGamma.CentralSequenceAlgebra (A := A) U))
    {T : Type w} [CStarAlgebra T]
    (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] T)
    (hf : Function.Injective f) (hd : DenseRange f)
    (hh : CStarAbsorption.ConnectedApproximateInnerHalfFlip f)
    (hNuclear : Nuclear A) {n : ℕ} (hn : 1 ≤ n)
    (hF : FixedAmplification A n) : AbsorbsOInfinity A :=
  nuclear_absorption_from_published_inputs U hcentral
    oInfinity_isNuclear oInfinity_topologicallySimple f hf hd hh hNuclear hn hF

end WeakPureInfiniteness.Campaign

end

end OAI
