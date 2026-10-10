import OAI.Analysis.Nuclearity.RepresentedAlgebra

namespace OAI

/-! The range of a representation, with its carrier and C*-structure kept
abstract when tensor products are formed. All fields are constructed from
the actual closed range; this introduces no mathematical assumption. -/

noncomputable section

namespace WeakPureInfiniteness

universe u w
variable {A : Type u} {H : Type w} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure RepresentedImageData (L : A →⋆ₐ[ℂ] (H →L[ℂ] H)) where
  Carrier : Type w
  [cstar : CStarAlgebra Carrier]
  quotient : A →⋆ₐ[ℂ] Carrier
  inclusion : Carrier →⋆ₐ[ℂ] (H →L[ℂ] H)
  surjective : Function.Surjective quotient
  injective : Function.Injective inclusion
  agrees : ∀ a, inclusion (quotient a) = L a

attribute [instance] RepresentedImageData.cstar

def representedImageData (L : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : RepresentedImageData L where
  Carrier := representedAlgebra L
  cstar := representedAlgebra_cstar L
  quotient := representedQuotientMap L
  inclusion := representedInclusion L
  surjective := representedQuotientMap_surjective L
  injective := representedInclusion_injective L
  agrees := representedInclusion_quotientMap L

theorem representedImageData_separable [TopologicalSpace.SeparableSpace A]
    (L : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (F : RepresentedImageData L) :
    TopologicalSpace.SeparableSpace F.Carrier :=
  F.surjective.denseRange.separableSpace
    (nonUnitalStarHom_continuous F.quotient.toNonUnitalStarAlgHom)

end WeakPureInfiniteness

end

end OAI
