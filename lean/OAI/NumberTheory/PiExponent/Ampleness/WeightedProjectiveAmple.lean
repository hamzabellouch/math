import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Ampleness.ProjectiveO1Ample
import OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

variable {R ι σ : Type} [CommRing R]

theorem lineBundle_ample [IsDomain R] [Finite σ] [Nonempty σ] (a : σ → ι →₀ ℕ) :
    (lineBundle (R := R) a).IsAmple :=
  LineBundle.IsAmple.pullback_closedImmersion (ProjectiveO1.lineBundle (R := R) (σ := σ))
    ProjectiveO1.lineBundle_ample (projectiveMonomialMap a)

end PiExponent.WeightedCompactification

end

end OAI
