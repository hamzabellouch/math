import Mathlib

namespace OAI

noncomputable section
namespace ShortenedBeam

abbrev Space := EuclideanSpace ℝ (Fin 3)

def point (x y t : ℝ) : Space := !₂[x / Real.sqrt 2, y / Real.sqrt 2, t]

def tetrahedron : Set Space :=
  {z | ∃ x y t : ℝ, |t| ≤ 1 ∧ |x| ≤ 1-t ∧ |y| ≤ 1+t ∧ z = point x y t}

def leftCoordinates (a x y t : ℝ) : Prop :=
  ∃ p h : ℝ, 0 ≤ p ∧ p ≤ 1 ∧ 0 ≤ h ∧ h ≤ 2-a ∧
    x = -1+h*p+t*(1-a*(2-a)*p^2) ∧
    y = -1+h*(1-p)+t*(-1+a*(2-a)*(1-p)^2)

def beamMinus (a : ℝ) : Set Space :=
  {z | ∃ x y t : ℝ, |t| ≤ 1 ∧ leftCoordinates a x y t ∧ z = point x y t}

def beamPlus (a : ℝ) : Set Space :=
  {z | ∃ x y t : ℝ, |t| ≤ 1 ∧ leftCoordinates a (-x) (-y) t ∧ z = point x y t}

def velocity (a p : ℝ) : Space :=
  point (1-a*(2-a)*p^2) (-1+a*(2-a)*(1-p)^2) 0

def axisMinus (a p : ℝ) : Space :=
  ‖point 0 0 1 + velocity a p‖⁻¹ • (point 0 0 1 + velocity a p)

def axisPlus (a p : ℝ) : Space :=
  ‖point 0 0 1 - velocity a p‖⁻¹ • (point 0 0 1 - velocity a p)

def drift (a t : ℝ) : ℝ := 2*a*t-2*a^2*t^3

def width (a t : ℝ) : ℝ :=
  max (a*(1-2*t^2)+a^2*t^2*(1+(1-|t|)^2+t^2)+25*a^3) 0

def strip (a : ℝ) : Set Space :=
  {z | ∃ x y t : ℝ, |t| ≤ 1 ∧ |x| ≤ 1-t ∧ |y| ≤ 1+t ∧
    |x+y+drift a t*((x-y)/2)| ≤ width a t ∧ z = point x y t}

end ShortenedBeam

end

end OAI
