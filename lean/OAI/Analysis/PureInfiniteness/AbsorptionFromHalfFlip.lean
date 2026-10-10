import OAI.Analysis.Nuclearity.NuclearRepresentedQuotient

namespace OAI

/-! Nonunital absorption through a represented quotient and a connected
approximate half-flip of O∞ (Kirchberg, Proposition 4.4 and Remark 4.6). -/
noncomputable section
open Filter
open scoped TensorProduct
namespace WeakPureInfiniteness.Campaign

universe u w
variable {A : Type u} [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
local instance : PartialOrder A := CStarAlgebra.spectralOrder A
local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem nuclear_absorption_from_halfFlip
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)] (hA : Nuclear A)
    {T : Type w} [CStarAlgebra T]
    (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] T)
    (hf : Function.Injective f) (hd : DenseRange f)
    (hh : CStarAbsorption.ConnectedApproximateInnerHalfFlip f)
    {n : ℕ} (hn : 1 ≤ n) (hF : FixedAmplification A n) : AbsorbsOInfinity A :=
  nuclear_absorption_from_quotient_nuclearity_and_halfFlip U hA
    (nuclear_unitizedFactorImageNuclear U Fact.out hA) f hf hd hh hn hF

end WeakPureInfiniteness.Campaign

end

end OAI
