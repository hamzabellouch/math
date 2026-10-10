import OAI.Geometry.TriangularCovering.Basic
import OAI.Geometry.CylinderCovering.Radial.RiemannDefinitions

namespace OAI

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace CylinderCovering.RadialSweep

abbrev Space := TriangularCovering.Space

structure Data where
  e : Space
  a : Space
  b : Space
  p₀ : Space
  α : ℝ
  β : ℝ
  L : ℝ
  R : ℝ → ℝ
  lam : ℝ → ℝ
  w : ℝ → Space
  interval_nonempty : α < β
  length_pos : 0 < L
  normal_unit : ‖e‖ = 1
  a_perp : inner ℝ e a = 0
  b_perp : inner ℝ e b = 0
  origin_perp : inner ℝ e p₀ = 0
  independent : LinearIndependent ℝ ![a, b]
  cap_continuous : ContinuousOn R (Icc α β)
  cap_nonneg : ∀ t ∈ Icc α β, 0 ≤ R t
  scalar_continuous : ContinuousOn lam (Icc α β)
  velocity_continuous : ContinuousOn w (Icc α β)
  velocity_perp : ∀ t ∈ Icc α β, inner ℝ e (w t) = 0
  aligned : ∀ t ∈ Icc α β,
    HasDerivWithinAt w (lam t • (a + t • b)) (Icc α β) t

def sweep (D : Data) : Set Space :=
  {z | ∃ t ∈ Icc D.α D.β, ∃ ρ ∈ Icc (0 : ℝ) (D.R t),
    ∃ s : ℝ, |s| ≤ D.L ∧
      z = D.p₀ + ρ • (D.a + t • D.b) + s • (D.e + D.w t)}

def kappa (D : Data) : ℝ :=
  Real.sqrt (inner ℝ D.a D.a * inner ℝ D.b D.b - (inner ℝ D.a D.b) ^ 2)

def direction (D : Data) (t : ℝ) : Space :=
  ‖D.e + D.w t‖⁻¹ • (D.e + D.w t)

def weightedArea (D : Data) : ℝ :=
  kappa D * ∫ t in D.α..D.β,
    D.R t ^ 2 / (2 * Real.sqrt (1 + ‖D.w t‖ ^ 2))

def scalarBound (D : Data) : ℝ := sSup ((fun t => |D.lam t|) '' Icc D.α D.β)

def radialError (D : Data) : ℝ := D.L * scalarBound D

def collar (D : Data) : ℝ := 3 * radialError D + 1

def midpoint (D : Data) (N : ℕ) (i : Fin N) : ℝ :=
  (RadialRiemann.point D.α D.β N i + RadialRiemann.point D.α D.β N (i + 1)) / 2

def leftTip (D : Data) (N : ℕ) : ℝ := -collar D * RadialRiemann.step D.α D.β N

def rightEdge (D : Data) (N : ℕ) (i : Fin N) : ℝ :=
  RadialRiemann.capMax D.R D.α D.β N i + radialError D * RadialRiemann.step D.α D.β N

def coordinateMap (D : Data) (p : ℝ × ℝ) : Space := D.p₀ + p.1 • D.a + p.2 • D.b

def frozenVertices (D : Data) (N : ℕ) (i : Fin N) : Fin 3 → Space :=
  let l := leftTip D N
  let r := rightEdge D N i
  let m := midpoint D N i
  let d := RadialRiemann.step D.α D.β N
  ![coordinateMap D (l, m * l),
    coordinateMap D (r, m * r - d / 2 * (r - l)),
    coordinateMap D (r, m * r + d / 2 * (r - l))]

def frozenTriangle (D : Data) (N : ℕ) (i : Fin N) : Set Space :=
  convexHull ℝ (Set.range (frozenVertices D N i))

def frozenBase (D : Data) (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (direction D (tag i)) '' frozenTriangle D N i

def frozenArea (D : Data) (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) : ℝ :=
  kappa D * RadialRiemann.step D.α D.β N *
    (RadialRiemann.capMax D.R D.α D.β N i +
      (radialError D + collar D) * RadialRiemann.step D.α D.β N) ^ 2 /
    (2 * Real.sqrt (1 + ‖D.w (tag i)‖ ^ 2))

def localSweep (D : Data) (N : ℕ) (i : Fin N) : Set Space :=
  {z | ∃ t ∈ RadialRiemann.cell D.α D.β N i,
    ∃ ρ ∈ Icc (0 : ℝ) (D.R t), ∃ s : ℝ, |s| ≤ D.L ∧
      z = D.p₀ + ρ • (D.a + t • D.b) + s • (D.e + D.w t)}

def actualBase (D : Data) (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) : Set Space :=
  TriangularCovering.projection (direction D (tag i)) '' localSweep D N i

def cylinder (u : Space) (B : Set Space) : Set Space :=
  {z | ∃ b ∈ B, ∃ s : ℝ, z = b + s • u}

def actualCost (D : Data) (N : ℕ) (tag : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, TriangularCovering.area (actualBase D N tag i)

def AlignedStatement : Prop :=
  ∀ D : Data, ∀ tag : (N : ℕ) → Fin N → ℝ,
    (∀ N, RadialRiemann.IsTagged D.α D.β N (tag N)) →
    ∃ C : (N : ℕ) → Fin N → TriangularCovering.TriCylinder,
      (∀ N, 0 < N →
        (∀ i, (C N i).axis = direction D (tag N i) ∧
          (C N i).base = frozenBase D N (tag N) i ∧
          TriangularCovering.area (C N i).base = frozenArea D N (tag N) i) ∧
        (∀ z ∈ sweep D, ∃ i : Fin N, z ∈ (C N i).carrier)) ∧
      Tendsto (fun N => TriangularCovering.totalArea (C N)) atTop (𝓝 (weightedArea D))

def ActualSweepStatement : Prop :=
  ∀ D : Data, ∀ tag : (N : ℕ) → Fin N → ℝ,
    (∀ N, RadialRiemann.IsTagged D.α D.β N (tag N)) →
    (∀ N, 0 < N →
      (∀ i : Fin N, ‖direction D (tag N i)‖ = 1 ∧
        IsCompact (actualBase D N (tag N) i) ∧
        MeasurableSet (actualBase D N (tag N) i) ∧
        Measure.euclideanHausdorffMeasure 2 (actualBase D N (tag N) i) ≠ ⊤ ∧
        (∀ z ∈ actualBase D N (tag N) i, inner ℝ (direction D (tag N i)) z = 0) ∧
        actualBase D N (tag N) i ⊆ frozenBase D N (tag N) i) ∧
      (∀ z ∈ sweep D, ∃ i : Fin N,
        z ∈ cylinder (direction D (tag N i)) (actualBase D N (tag N) i))) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, actualCost D N (tag N) ≤ weightedArea D + ε) ∧
    Filter.limsup (fun N => actualCost D N (tag N)) atTop ≤ weightedArea D

end CylinderCovering.RadialSweep

end

end OAI
