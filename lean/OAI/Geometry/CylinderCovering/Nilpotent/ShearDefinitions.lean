import OAI.Geometry.CylinderCovering.Ruled.C1Definitions

namespace OAI

noncomputable section
namespace RuledApproximation.NilpotentShear

def field (ell : Plane →L[ℝ] ℝ) (v c : Plane) (f : ℝ → ℝ) (p : Plane) : Plane :=
  c + f (ell p) • v

def signedSquare (y : ℝ) : ℝ := y * |y|

def signedSquareField : Plane → Plane :=
  field (EuclideanSpace.proj 1) (vec2 1 0) 0 signedSquare

end RuledApproximation.NilpotentShear

end

end OAI
