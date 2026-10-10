import OAI.AlgebraicGeometry.SurfaceCones.RingProperties

namespace OAI

/-!
# The completed surface cone

The explicit Kummer surface construction of OpenAI's
*A Complete Local Domain without a Small Cohen–Macaulay Module* (2026)
gives a complete normal Noetherian local domain of dimension three over ℂ.
-/

namespace SmallCM

/-- Ring-theoretic properties of the completed surface cone. -/
theorem candidate_ring_properties :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R)
      (_ : IsIntegrallyClosed R) (_ : IsLocalRing R) (_ : Algebra ℂ R),
      IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      ringKrullDim R = 3 ∧
      Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField R)) := by
  let := ExplicitCone.actualCompletion_noetherian
  exact ⟨ExplicitCone.completedRing, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    ExplicitCone.completedRing_dimension, ExplicitCone.completedRing_residue_bijective⟩

end SmallCM

end OAI
