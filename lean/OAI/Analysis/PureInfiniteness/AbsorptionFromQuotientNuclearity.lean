import OAI.Analysis.Nuclearity.RepresentedIdealGeneration
import OAI.Analysis.Nuclearity.UnitizedIdealGeneration
import OAI.Analysis.Nuclearity.ConeIdealGeneration
import OAI.Analysis.PureInfiniteness.AbsorptionFromTensorIdeal

namespace OAI

/-! Absorption from quotient nuclearity and a connected approximate half-flip.
The represented left algebra is a quotient of the unitized nuclear source.
Nuclearity of this quotient follows from Choi–Effros, Duke Math. J. 43 (1976),
Corollary 3.3, and permanence under unitization. -/

noncomputable section
open Filter
open scoped TensorProduct

namespace WeakPureInfiniteness

universe u
variable (A : Type u) [NonUnitalCStarAlgebra A]

def UnitizedFactorImageNuclear : Prop :=
  ∀ (B : Type u) [CStarAlgebra B] (H : ComplexHilbert.{u+1})
    (π : UnitalTensorRepresentation (A := Unitization ℂ A) (B := B) (H := H)),
    (∀ T : H →L[ℂ] H, (∀ x, Commute T (π x)) → ∃ c : ℂ, T = c • 1) →
    Pureness.IsNuclear.{u+1,u+1} (representedAlgebra (leftRepresentedMap π))

variable {A}

theorem elementary_generation_from_factor_images (hQ : UnitizedFactorImageNuclear A)
    (B : Type u) [CStarAlgebra B]
    (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B)) :
    (elementaryGeneratedIdeal J).module = J.module := by
  let _ : PartialOrder (Unitization ℂ A) := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing (Unitization ℂ A) := CStarAlgebra.spectralOrderedRing _
  let _ : PartialOrder B := CStarAlgebra.spectralOrder B
  let _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  apply elementary_generation_of_unitization (J := J)
  exact fun K => elementary_generation_of_represented_nuclearity (hQ B) K

namespace Campaign

universe w
variable [TopologicalSpace.SeparableSpace A]
local instance quotientAbsorptionOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance quotientAbsorptionOrdered : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem nuclear_absorption_from_quotient_nuclearity_and_halfFlip
    (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
    (hA : Nuclear A) (hQ : UnitizedFactorImageNuclear A)
    {T : Type w} [CStarAlgebra T]
    (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] T)
    (hf : Function.Injective f) (hd : DenseRange f)
    (hh : CStarAbsorption.ConnectedApproximateInnerHalfFlip f)
    {n : ℕ} (hn : 1 ≤ n) (hF : FixedAmplification A n) : AbsorbsOInfinity A := by
  apply nuclear_absorption_from_tensor_ideal_and_halfFlip U hA ?_ f hf hd hh hn hF
  intro I _ l R
  apply R.elementarySpan_of_ideal_generation U hA
    (NonunitalGamma.normInclusion (A := A) U)
  exact fun J => elementary_generation_from_factor_images hQ R.C J

end Campaign
end WeakPureInfiniteness

end

end OAI
