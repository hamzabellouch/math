import Mathlib

namespace OAI

noncomputable section
namespace CylinderCovering.BeamNeighborhood
open Set
abbrev Plane := EuclideanSpace ℝ (Fin 2)
def radial (p : ℝ) : Plane := !₂[p, 1-p]
def transverse : Plane := !₂[1, -1]
def velocity (a p : ℝ) : Plane := !₂[1-a*(2-a)*p^2, -1+a*(2-a)*(1-p)^2]
def sector (a l r δ : ℝ) : Set Plane :=
  {z | ∃ p ∈ Icc l r, ∃ d ∈ Icc (-δ) (2-a+δ), z = d • radial p}
def paddedSector (a l r δ : ℝ) : Set Plane := Metric.cthickening (δ^2) (sector a l r δ)
def intercept (a p m h t : ℝ) : Plane :=
  h • radial p + t • (velocity a p - velocity a m)

def enclosingRadius (a δ : ℝ) : ℝ := 2-a+11*δ+2*δ^2
def enclosingApex (l r δ : ℝ) : Plane := (-10*δ) • radial ((l+r)/2)
def enclosingTriangle (a l r δ : ℝ) : Set Plane :=
  let c := enclosingApex l r δ
  let R := enclosingRadius a δ
  convexHull ℝ (Set.range (![c, c+R • radial l, c+R • radial r] : Fin 3 → Plane))
end CylinderCovering.BeamNeighborhood

end

end OAI
