import OAI.Geometry.CylinderCovering.Physical.FiniteDefinitions

namespace OAI

open Set Filter
open scoped Topology
noncomputable section
namespace RadialPhysical.ExplicitTriangles
open CylinderCovering

def error (centered : Bool) (b eta : ℝ) : ℝ := axialBound centered b * |eta|

def left (centered : Bool) (b eta : ℝ) (N : ℕ) : ℝ :=
  -(3 * error centered b eta + 1) * RadialRiemann.step (-b) b N

def right (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  RadialRiemann.capMax T (-b) b N i +
    error centered b eta * RadialRiemann.step (-b) b N

def middle (b : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  (RadialRiemann.point (-b) b N i + RadialRiemann.point (-b) b N (i + 1)) / 2

def coordinates (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (i : Fin N) : Fin 3 → ℝ × ℝ :=
  let l := left centered b eta N
  let r := right centered b eta T N i
  let m := middle b N i
  let d := RadialRiemann.step (-b) b N
  ![(l, m*l), (r, m*r-d/2*(r-l)), (r, m*r+d/2*(r-l))]

def upperIntercept (b : ℝ) (p : ℝ × ℝ) : Space := point b 0 p.2 (1-p.1)

def lowerIntercept (centered : Bool) (b : ℝ) (p : ℝ × ℝ) : Space :=
  point b p.2 0 ((if centered then (-1:ℝ) else 0)+p.1)

def upperVertices (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (i : Fin N) : Fin 3 → Space :=
  upperIntercept b ∘ coordinates centered b eta T N i

def lowerVertices (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (i : Fin N) : Fin 3 → Space :=
  lowerIntercept centered b ∘ coordinates centered b eta T N i

def upperBase (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (upperPhysicalAxis b eta (tag i)) ''
    convexHull ℝ (Set.range (upperVertices centered b eta T N i))

def lowerBase (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (lowerPhysicalAxis b eta (tag i)) ''
    convexHull ℝ (Set.range (lowerVertices centered b eta T N i))

def localArea (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) : ℝ :=
  height b * RadialRiemann.step (-b) b N *
    (RadialRiemann.capMax T (-b) b N i +
      (4 * error centered b eta + 1) * RadialRiemann.step (-b) b N)^2 /
    (2 * Real.sqrt (1 + eta^2 *
      (((tag i)^2+b^2)^2/4 + height b^2*(tag i)^2)))

def ConstructionStatement : Prop :=
  ∀ (centered : Bool) (b eta : ℝ), 0 < b → ∀ T : ℝ → ℝ,
    ContinuousOn T (Icc (-b) b) → (∀ s ∈ Icc (-b) b, 0 ≤ T s) →
    ∀ tagU tagL : (N : ℕ) → Fin N → ℝ,
    (∀ N, RadialRiemann.IsTagged (-b) b N (tagU N)) →
    (∀ N, RadialRiemann.IsTagged (-b) b N (tagL N)) →
    ∃ U L : (N : ℕ) → Fin N → TriangularCovering.TriCylinder,
      (∀ N i,
        (U N i).axis = upperPhysicalAxis b eta (tagU N i) ∧
        (L N i).axis = lowerPhysicalAxis b eta (tagL N i) ∧
        (U N i).base = upperBase centered b eta T N (tagU N) i ∧
        (L N i).base = lowerBase centered b eta T N (tagL N) i ∧
        TriangularCovering.area (U N i).base = localArea centered b eta T N (tagU N) i ∧
        TriangularCovering.area (L N i).base = localArea centered b eta T N (tagL N) i ∧
        upperPhysicalBase centered b eta T N (tagU N) i ⊆ (U N i).base ∧
        lowerPhysicalBase centered b eta T N (tagL N) i ⊆ (L N i).base) ∧
      (∀ N, 0 < N →
        (∀ z ∈ upperSweepOn centered b eta T (Icc (-b) b),
          ∃ i : Fin N, z ∈ (U N i).carrier) ∧
        (∀ z ∈ lowerSweepOn centered b eta T (Icc (-b) b),
          ∃ i : Fin N, z ∈ (L N i).carrier)) ∧
      Tendsto (fun N => TriangularCovering.totalArea (U N) +
        TriangularCovering.totalArea (L N)) atTop (𝓝 (scaledCost b eta T))

end RadialPhysical.ExplicitTriangles

end

end OAI
