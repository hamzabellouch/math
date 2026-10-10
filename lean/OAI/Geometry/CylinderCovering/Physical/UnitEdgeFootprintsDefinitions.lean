import OAI.Geometry.TriangularCovering.Basic
import OAI.Geometry.CylinderCovering.Radial.RiemannDefinitions

namespace OAI

noncomputable section
namespace CylinderCovering.UnitEdgeFootprints

abbrev Space := TriangularCovering.Space

def height : ℝ := 1 / Real.sqrt 2

def intercept (u v : ℝ) : Space := !₂[0, v, height * u]

def rawDirection (η m : ℝ) : Space :=
  !₂[1, η * (1 / 4 + m ^ 2), 2 * height * η * m]

def axis (η m : ℝ) : Space := ‖rawDirection η m‖⁻¹ • rawDirection η m

def vertices (η d M m : ℝ) : Fin 3 → Space :=
  ![intercept (-η * d) (m * (-η * d)),
    intercept (M + η * d) (m * (M + η * d) - d / 2 * (M + 2 * η * d)),
    intercept (M + η * d) (m * (M + η * d) + d / 2 * (M + 2 * η * d))]

def foot (η d M m : ℝ) : Set Space := convexHull ℝ (Set.range (vertices η d M m))

def base (η d M m : ℝ) : Set Space :=
  TriangularCovering.projection (axis η m) '' foot η d M m

def representedPoint (η s ρ x : ℝ) : Space :=
  !₂[x, s * ρ + η * x * (1 / 4 + s ^ 2), height * (ρ + 2 * η * x * s)]

def areaFormula (η d M m : ℝ) : ℝ :=
  height * d * (M + 2 * η * d) ^ 2 /
    (2 * Real.sqrt (1 + η ^ 2 * ((1 / 4 + m ^ 2) ^ 2 + 2 * m ^ 2)))

def LocalRealizationStatement : Prop :=
  ∀ η d M m : ℝ, 0 < η → 0 < d → 0 ≤ M →
    ∃ C : TriangularCovering.TriCylinder,
      C.axis = axis η m ∧ C.base = base η d M m ∧
      TriangularCovering.area C.base = areaFormula η d M m ∧
      ∀ s ρ x : ℝ, |s - m| ≤ d / 2 → 0 ≤ ρ → ρ ≤ M → |x| ≤ 1 / 2 →
        representedPoint η s ρ x ∈ C.carrier

def sourceCap (η s : ℝ) : ℝ :=
  Real.sqrt (1 / 4 + η ^ 2 * (s ^ 2 / 4 + s ^ 4 + 1 / 960))

def sweep (η : ℝ) (R : ℝ → ℝ) : Set Space :=
  {z | ∃ s ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), ∃ ρ ∈ Set.Icc (0 : ℝ) (R s),
    ∃ x : ℝ, |x| ≤ 1 / 2 ∧ z = representedPoint η s ρ x}

def mesh (N : ℕ) : ℝ := RadialRiemann.step (-1 / 2) (1 / 2) N

def midpoint (N : ℕ) (i : Fin N) : ℝ :=
  (RadialRiemann.point (-1 / 2) (1 / 2) N i +
    RadialRiemann.point (-1 / 2) (1 / 2) N (i + 1)) / 2

def maximumCap (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  RadialRiemann.capMax R (-1 / 2) (1 / 2) N i

def limitingArea (η : ℝ) (R : ℝ → ℝ) : ℝ :=
  height * ∫ s in (-1 / 2 : ℝ)..(1 / 2),
    R s ^ 2 / (2 * Real.sqrt (1 + η ^ 2 * ((1 / 4 + s ^ 2) ^ 2 + 2 * s ^ 2)))

def FamilyRealizationStatement : Prop :=
  ∀ η : ℝ, 0 < η → ∀ R : ℝ → ℝ,
    ContinuousOn R (Set.Icc (-1 / 2 : ℝ) (1 / 2)) →
    (∀ s ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2), 0 ≤ R s) →
    ∃ C : (N : ℕ) → Fin N → TriangularCovering.TriCylinder,
      (∀ N (i : Fin N),
        (C N i).axis = axis η (midpoint N i) ∧
        (C N i).base = base η (mesh N) (maximumCap R N i) (midpoint N i) ∧
        TriangularCovering.area (C N i).base =
          areaFormula η (mesh N) (maximumCap R N i) (midpoint N i)) ∧
      (∀ N, 0 < N → ∀ z ∈ sweep η R, ∃ i : Fin N, z ∈ (C N i).carrier) ∧
      Filter.Tendsto (fun N => TriangularCovering.totalArea (C N)) Filter.atTop
        (nhds (limitingArea η R))

end CylinderCovering.UnitEdgeFootprints

end

end OAI
