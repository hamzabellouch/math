import OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry

variable {R σ : Type} [CommRing R] [IsDomain R] [Finite σ] [Nonempty σ]

theorem lineBundle_ample : (lineBundle (R := R) (σ := σ)).IsAmple := by
  let : CompactSpace (projectiveSpace R σ) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveProjection R σ)
  exact LineBundle.ample_of_affine_section_cover (lineBundle (R := R) (σ := σ))
    coordinateSection coordinateSection_cover coordinateSection_isAffineOpen

end PiExponent.ProjectiveO1

end

end OAI
