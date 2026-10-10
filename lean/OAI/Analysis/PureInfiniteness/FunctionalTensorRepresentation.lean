import OAI.Analysis.OperatorAlgebra.FunctionalCommutant

namespace OAI

/-! Simultaneous GNS data, with its commutant kept as an abstract C*-algebra.
This interface does not add a hypothesis: every finite real functional family
has such a representation by `functionalTensorRepresentation_nonempty`. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

universe u v

structure FunctionalTensorRepresentation {D : Type u} [NonUnitalCStarAlgebra D]
    {I : Type v} (l : I → selfAdjoint D →L[ℝ] ℝ) where
  H : Type u
  normed : NormedAddCommGroup H
  inner : InnerProductSpace ℂ H
  complete : CompleteSpace H
  C : Type u
  cstar : CStarAlgebra C
  π : Unitization ℂ D →⋆ₐ[ℂ] (H →L[ℂ] H)
  η : C →⋆ₐ[ℂ] (H →L[ℂ] H)
  commute : ∀ d c, Commute (π d) (η c)
  ξ : H
  cyclic : DenseRange (fun a => π a ξ)
  c : I → C
  c_selfAdjoint : ∀ i, IsSelfAdjoint (c i)
  represents : ∀ i (a : selfAdjoint D), l i a =
    (⟪ξ, π (a : Unitization ℂ D) (η (c i) ξ)⟫_ℂ).re

attribute [instance] FunctionalTensorRepresentation.normed
  FunctionalTensorRepresentation.inner FunctionalTensorRepresentation.complete
  FunctionalTensorRepresentation.cstar

variable {D : Type u} [NonUnitalCStarAlgebra D] {I : Type v} [Fintype I]

theorem functionalTensorRepresentation_nonempty (l : I → selfAdjoint D →L[ℝ] ℝ) :
    Nonempty (FunctionalTensorRepresentation l) := by
  let : PartialOrder (Unitization ℂ D) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (Unitization ℂ D) := CStarAlgebra.spectralOrderedRing _
  obtain ⟨f, _, c, hc, hrep⟩ := finite_functionals_in_commutant l
  exact ⟨{
    H := f.GNS
    normed := inferInstance
    inner := inferInstance
    complete := inferInstance
    C := representationCommutant f.gnsStarAlgHom
    cstar := inferInstance
    π := f.gnsStarAlgHom
    η := (representationCommutant f.gnsStarAlgHom).subtype
    commute := representationCommutant_commute f.gnsStarAlgHom
    ξ := Pureness.stateGNSVector f
    cyclic := gns_vector_cyclic f
    c := c
    c_selfAdjoint := hc
    represents := hrep }⟩

end WeakPureInfiniteness

end

end OAI
