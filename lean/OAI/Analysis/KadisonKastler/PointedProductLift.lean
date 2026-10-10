import OAI.Analysis.KadisonKastler.PointedSitesTransport

namespace OAI

/-! # Universe lift of a concrete pointed product

The construction takes place in a separable Hilbert space in `Type`.
Spatial transport along `ULift` gives the same concrete product data in
any ambient universe required by the stability theorem.
-/

namespace KadisonKastler

open UnitalTomsWinter

noncomputable section

universe u

/-- Raise the universe without changing any product-state data. -/
def PointedMatrixProduct.universeLift {I : Type} {ν : I → ℝ}
    (P : PointedMatrixProduct.{0} ν) : PointedMatrixProduct.{u} ν := by
  letI : InnerProductSpace ℂ (ULift.{u} P.K) :=
    InnerProductSpace.induced (LinearIsometryEquiv.ulift ℂ P.K).toLinearMap
  let e : P.K ≃ₗᵢ[ℂ] ULift.{u} P.K := (LinearIsometryEquiv.ulift ℂ P.K).symm
  letI : TopologicalSpace.SeparableSpace (ULift.{u} P.K) :=
    e.surjective.denseRange.separableSpace e.continuous
  exact {
    K := ULift.{u} P.K
    algebra := spatialTransportAlgebra e P.algebra
    vector := e P.vector
    coordinates := P.coordinates.transport e }

end

end KadisonKastler

end OAI
