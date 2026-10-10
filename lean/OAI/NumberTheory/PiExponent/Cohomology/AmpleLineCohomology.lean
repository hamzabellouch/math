import OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite
import OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair
import OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}
theorem line_cohomology_finite_of_ample_all
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (q : ℕ) :
    letI := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf q) := by
  cases isEmpty_or_nonempty X with
  | inr hX =>
    let := hX
    let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
    exact AmpleCohomologyFinite.cohomology_finite_of_ample p H hH L.sheaf q
  | inl hX =>
    let := hX
    let := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    let M := (Scheme.Modules.pushforward (𝟙 X)).obj L.sheaf
    let := Module.compHom (cohomology M q) (baseScalars p)
    let : FiniteDimensional ℂ (cohomology M q) :=
      PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional (𝟙 X) p L q
    let e := PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearEquiv (𝟙 X) p L.sheaf q
    exact FiniteDimensional.of_surjective e.symm.toLinearMap e.symm.surjective
end
end PiExponent.NumericalAmpleness

end OAI
