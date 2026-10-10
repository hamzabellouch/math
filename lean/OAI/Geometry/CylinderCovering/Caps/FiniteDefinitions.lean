import OAI.Geometry.CylinderCovering.Footprints.FootprintsDefinitions
import OAI.Geometry.CylinderCovering.Radial.PairedSweepDefinitions

namespace OAI

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace CylinderCovering.HalfheightFinite
abbrev Space := TriangularCovering.Space

def height : ℝ := 1 / Real.sqrt 2
def point (X Y Z : ℝ) : Space := !₂[X/2,Y/2,height*Z]
def tetrahedron : Set Space :=
  {z | ∃ X Y Z : ℝ, |X| ≤ 1-Z ∧ |Y| ≤ Z ∧ z = point X Y Z}
def alpha (r : ℝ) : ℝ := (1+r^2)/4
def beta (r : ℝ) : ℝ := r/2
def profile (r : ℝ) : ℝ := r^2*(1+r^2)/16
def cubicCap (δ r : ℝ) : ℝ := 1/2+δ^2*profile r+4*δ^3
def fractionalCap (δ r : ℝ) : ℝ := 1/2+δ^2*profile r+δ^(5/2:ℝ)
def firstRaw (δ r : ℝ) : Space := !₂[1,δ*alpha r,2*height*δ*beta r]
def secondRaw (δ r : ℝ) : Space := !₂[-δ*alpha r,1,2*height*δ*beta r]
def firstAxis (δ r : ℝ) : Space := ‖firstRaw δ r‖⁻¹ • firstRaw δ r
def secondAxis (δ r : ℝ) : Space := ‖secondRaw δ r‖⁻¹ • secondRaw δ r
def firstFoot (p : ℝ × ℝ) : Space := !₂[0,p.2/2,height*p.1]
def secondFoot (p : ℝ × ℝ) : Space := !₂[p.2/2,0,height*(1-p.1)]
def halfwidth (N : ℕ) : ℝ := 1/(N:ℝ)
def midpoint (N : ℕ) (i : Fin N) : ℝ :=
  (RadialRiemann.point (-1) 1 N i+RadialRiemann.point (-1) 1 N (i+1))/2
def maxCap (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : ℝ := RadialRiemann.capMax R (-1) 1 N i
def collar (δ : ℝ) (N : ℕ) : ℝ := δ*halfwidth N/2
def foot (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : Set (ℝ × ℝ) :=
  RadialFootprints.halfheightFootprint (halfwidth N) (collar δ N) (maxCap R N i) (midpoint N i)
def firstBase (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (firstAxis δ (midpoint N i)) '' (firstFoot '' foot δ R N i)
def secondBase (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (secondAxis δ (midpoint N i)) '' (secondFoot '' foot δ R N i)
def localArea (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  let M := maxCap R N i
  let e := collar δ N
  height/2 * halfwidth N * (M^2+6*e*M+8*e^2) /
    Real.sqrt (1+δ^2*(alpha (midpoint N i)^2+2*beta (midpoint N i)^2))
def totalArea (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ i : Fin N, TriangularCovering.area (firstBase δ R N i))+
    ∑ i : Fin N, TriangularCovering.area (secondBase δ R N i)
def limitingArea (δ : ℝ) (R : ℝ → ℝ) : ℝ :=
  height/2 * ∫ r in (-1:ℝ)..1, R r^2 /
    Real.sqrt (1+δ^2*(alpha r^2+2*beta r^2))
def BaseProperties (u : Space) (B : Set Space) : Prop :=
  ‖u‖=1 ∧ IsCompact B ∧ Convex ℝ B ∧ MeasurableSet B ∧
    Measure.euclideanHausdorffMeasure 2 B ≠ ⊤ ∧ ∀ z ∈ B, inner ℝ u z=0

def FamilyConclusion (δ : ℝ) (R : ℝ → ℝ) : Prop :=
  (∀ N : ℕ, 0<N →
    (∀ i : Fin N,
      BaseProperties (firstAxis δ (midpoint N i)) (firstBase δ R N i) ∧
      BaseProperties (secondAxis δ (midpoint N i)) (secondBase δ R N i) ∧
      TriangularCovering.area (firstBase δ R N i)=localArea δ R N i ∧
      TriangularCovering.area (secondBase δ R N i)=localArea δ R N i) ∧
    (∀ z ∈ tetrahedron,
      (∃ i : Fin N, z ∈ RadialSweep.cylinder (firstAxis δ (midpoint N i)) (firstBase δ R N i)) ∨
      (∃ i : Fin N, z ∈ RadialSweep.cylinder (secondAxis δ (midpoint N i)) (secondBase δ R N i)))) ∧
  Tendsto (totalArea δ R) atTop (𝓝 (limitingArea δ R))

def Statement : Prop :=
  (∀ δ : ℝ, 0<δ → δ≤1/2 → FamilyConclusion δ (cubicCap δ)) ∧
  (∀ᶠ δ : ℝ in 𝓝[>] 0, FamilyConclusion δ (fractionalCap δ)) ∧
  ((fun δ => limitingArea δ (cubicCap δ)-
    height/2*(1/2-δ^2/240+8*δ^3)) =O[𝓝[>] (0:ℝ)] (fun δ => δ^4)) ∧
  ((fun δ => limitingArea δ (fractionalCap δ)-
    height/2*(1/2-δ^2/240+2*δ^(5/2:ℝ))) =O[𝓝[>] (0:ℝ)] (fun δ => δ^4)) ∧
  (∀ᶠ δ : ℝ in 𝓝[>] 0,
    (∀ᶠ N in atTop, 0<N ∧ totalArea δ (cubicCap δ) N < height/4) ∧
    (∀ᶠ N in atTop, 0<N ∧ totalArea δ (fractionalCap δ) N < height/4))
end CylinderCovering.HalfheightFinite

end

end OAI
