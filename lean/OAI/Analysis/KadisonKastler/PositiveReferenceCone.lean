import OAI.Analysis.KadisonKastler.PositiveConeSelfDual

namespace OAI

/-! # Changing the cyclic reference inside the same positive cone

The quadratic positivity and the generated cone are unchanged when the
reference is replaced by a cyclic vector in that cone. These are the
reference-transport facts needed for projection-family amplification.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveReferenceRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ=ξ)
  (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))

include hJ hright hpos in
theorem positiveCone_quadratic_nonneg {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) (a : Algebra M) :
    0 ≤ inner ℝ η (modularQuadratic J a η) :=
  modularPositiveCone_acute J hJ hright ξ hpos hη
    (modularQuadratic_preserves_positiveCone J hJ hright ξ a hη)

include hJ hright in
theorem positiveCone_change_reference_le {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) :
    modularPositiveCone (M := M) J η ≤ modularPositiveCone (M := M) J ξ := by
  apply closure_minimal
  · apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact modularQuadratic_preserves_positiveCone J hJ hright ξ a hη
  · exact modularPositiveCone_isClosed J ξ

include hJ hright hξ hpos in
theorem positiveCone_change_reference_eq
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hcyc : DenseRange (algebraVectorMap M η)) :
    modularPositiveCone (M := M) J η = modularPositiveCone (M := M) J ξ := by
  have hle := positiveCone_change_reference_le J hJ hright ξ hη
  apply le_antisymm hle
  intro x hx
  exact modularPositiveCone_mem_of_dual J hJ hright hleft η
    (modularPositiveCone_fixed J hright ξ hξ hη) hcyc
    (modularPositiveCone_fixed J hright ξ hξ hx)
    (fun _ hw => modularPositiveCone_acute J hJ hright ξ hpos hx (hle hw))

end

end KadisonKastler

end OAI
