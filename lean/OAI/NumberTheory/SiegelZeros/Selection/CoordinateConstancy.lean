import OAI.NumberTheory.SiegelZeros.Differentials.SelectedCotangent
import OAI.NumberTheory.SiegelZeros.Structure.CanonicalDivisorScalars

namespace OAI

namespace SiegelZeros

section

open CategoryTheory AlgebraicGeometry
namespace SiegelZerosAwei.Workers.W14
open SiegelZerosAwei.Workers.W15 SiegelZeros.W58
open WeightedTorusJets.IdentityCotangentRank

variable (p : Ideal (TorusRing ℂ)) [p.IsPrime]

theorem prime_eq_identity_of_constant_coordinates
    (hp : p ≤ identityIdeal ℂ) :
    letI := torusFunctionFieldAlgebra p
    (∀ i : Fin 4, ∃ a : ℂ,
      torusCoordinateFunction ℂ p i =
        algebraMap ℂ (TorusSubvariety ℂ p).functionField a) →
      p = identityIdeal ℂ := by
  let := torusFunctionFieldAlgebra p
  intro h
  apply le_antisymm hp
  rw [← identityIdeal_span ℂ]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  obtain ⟨a, ha⟩ := h i
  have hinj := IsFractionRing.injective (TorusSubvarietyRing ℂ p)
    (TorusSubvariety ℂ p).functionField
  have hquot : Ideal.Quotient.mk p (coordinate ℂ i) =
      algebraMap ℂ (TorusSubvarietyRing ℂ p) a := by
    apply hinj
    exact ha
  have hmem : coordinate ℂ i - algebraMap ℂ (TorusRing ℂ) a ∈ p := by
    exact (Ideal.Quotient.eq (I := p)).mp hquot
  have haone : a = 1 := by
    have hev := hp hmem
    rw [mem_identityIdeal] at hev
    have heval : identityEvaluation ℂ (algebraMap ℂ (TorusRing ℂ) a) = a := by
      rw [IsScalarTower.algebraMap_apply ℂ (AmbientPolynomial ℂ) (TorusRing ℂ)]
      simp
    rw [map_sub, identityEvaluation_coordinate, heval] at hev
    exact (sub_eq_zero.mp hev).symm
  simpa [haone] using hmem

theorem not_all_coordinates_constant (hp : p ≤ identityIdeal ℂ) (hh : p.height ≤ 3) :
    letI := torusFunctionFieldAlgebra p
    ¬ (∀ i : Fin 4, ∃ a : ℂ,
      torusCoordinateFunction ℂ p i =
        algebraMap ℂ (TorusSubvariety ℂ p).functionField a) := by
  let := torusFunctionFieldAlgebra p
  intro h
  exact WeightedTorusJets.IdentityHeight.prime_ne_identity_of_height_le_three
    ℂ p hh (prime_eq_identity_of_constant_coordinates p hp h)

end SiegelZerosAwei.Workers.W14

end

end SiegelZeros

end OAI
