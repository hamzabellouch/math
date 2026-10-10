import OAI.AlgebraicGeometry.StableCoordinate.ReesToDegeneration
import OAI.AlgebraicGeometry.StableCoordinate.SourceInvariant
import OAI.AlgebraicGeometry.StableCoordinate.SourceCoordinateTransport

namespace OAI

/-!
# The source-coordinate hypothesis gives the actual quadric obstruction data

This assembles Section 3 with its literal polynomial input.  The associated
graded ring, its integer grading, the leading derivation, the Laurent
extension, and the positive center-ideal numerator are all concrete proved
constructions imported above.  The only hypothesis in the final theorem is
the coordinate hypothesis which the subsequent rigidity argument refutes.
-/

noncomputable section

namespace StableCoordinate.CoordinateToQuadric

open MvPolynomial Obstruction

/-- Over any field, a coordinate system on the source algebra with first
coordinate `p` produces a nonzero LND and nonzero invariant in the actual
quadric-center ideal. -/
theorem source_coordinate_produces_quadric_lnd
    (k : Type*) [Field k]
    (e : P k 4 ≃ₐ[k] A k) (hp : e (X 0) = aX k 0) :
    ∃ E : Derivation k (B k) (B k),
      IsLocallyNilpotent E ∧ E ≠ 0 ∧
      ∃ h : B k, h ∈ I k ∧ h ≠ 0 ∧ E h = 0 := by
  obtain ⟨m, D, hDne, hD, hshift, hpD, d, η, hd, hη, hηne, hDη⟩ :=
    ReesToDegeneration.coordinate_produces_degeneration_lnd k e hp
  exact SourceInvariant.exists_quadric_lnd_invariant D m hshift hD hDne hpD
    hd hη hηne hDη

/-- The literal degree-five polynomial's unrestricted four-variable coordinate
hypothesis produces precisely the obstruction data on `B` and `I`. -/
theorem f_coordinate_produces_quadric_lnd
    (hf : IsCoordinate (by decide : 0 < 4) StableCoordinate.f) :
    ∃ E : Derivation ℂ (B ℂ) (B ℂ),
      IsLocallyNilpotent E ∧ E ≠ 0 ∧
      ∃ h : B ℂ, h ∈ I ℂ ∧ h ≠ 0 ∧ E h = 0 := by
  obtain ⟨e, hp⟩ := source_coordinate_system_of_f_coordinate hf
  exact source_coordinate_produces_quadric_lnd ℂ e hp

end StableCoordinate.CoordinateToQuadric

end

end OAI
