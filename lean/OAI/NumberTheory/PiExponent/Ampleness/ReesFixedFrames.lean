import OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)

theorem frame_nonempty_congr {X : Scheme} (M : X.Modules) {U V : X.Opens}
    (h : U = V)
    (he : Nonempty (M.restrict U.ι ≅ PiExponentSeshadri.Frames.O U.toScheme)) :
    Nonempty (M.restrict V.ι ≅ PiExponentSeshadri.Frames.O V.toScheme) := by
  subst V
  exact he

theorem chartFrame_nonempty {p : J} (hp : p ∈ s) :
    Nonempty ((exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      PiExponentSeshadri.Frames.O (chartOpen I a hs).1.toScheme) :=
  frame_nonempty_congr (exceptionalLineBundle I).sheaf (chartOpen_eq I a hs).symm
    (ReesProductPowerSections.chartFrame_nonempty I a hs hp)

def chartFrame {p : J} (hp : p ∈ s) :
    (exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      PiExponentSeshadri.Frames.O (chartOpen I a hs).1.toScheme :=
  (chartFrame_nonempty I a hs hp).some

end
end PiExponent.ReesFrozenChart

end OAI
