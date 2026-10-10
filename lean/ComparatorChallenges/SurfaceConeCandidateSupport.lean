import Mathlib

namespace OAI

namespace SmallCM

/-- Ring-theoretic properties of the completed surface cone. -/
theorem candidate_ring_properties :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R)
      (_ : IsIntegrallyClosed R) (_ : IsLocalRing R) (_ : Algebra ℂ R),
      IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
      ringKrullDim R = 3 ∧
      Function.Bijective (algebraMap ℂ (IsLocalRing.ResidueField R)) := by
  sorry
end SmallCM


end OAI
