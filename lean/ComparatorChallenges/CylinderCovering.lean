import Mathlib

namespace OAI

section
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

abbrev Space := EuclideanSpace ℝ (Fin 3)

def H : ℝ := Real.sqrt 2

def point (x y t : ℝ) : Space := !₂[x, y, H * t]

def K : Set Space :=
  {z | ∃ x y t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ |x| ≤ 1 - t ∧ |y| ≤ t ∧ z = point x y t}

def projection (u z : Space) : Space := z - (inner ℝ u z) • u

def area (B : Set Space) : ℝ := (Measure.euclideanHausdorffMeasure 2 B).toReal

def shadowArea (u : Space) : ℝ := area (projection u '' K)

def A_min : ℝ := sInf {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = shadowArea u}

structure TriCylinder where
  axis : Space
  base : Set Space
  unit_axis : ‖axis‖ = 1
  perpendicular : ∀ z ∈ base, inner ℝ axis z = 0
  triangular : ∃ v : Fin 3 → Space, AffineIndependent ℝ v ∧
    base = convexHull ℝ (Set.range v)
  compact : IsCompact base
  convex : Convex ℝ base
  measurable : MeasurableSet base
  finite_area : Measure.euclideanHausdorffMeasure 2 base ≠ ⊤

def TriCylinder.carrier (c : TriCylinder) : Set Space :=
  {z | ∃ b ∈ c.base, ∃ r : ℝ, z = b + r • c.axis}

def Covers {m : ℕ} (c : Fin m → TriCylinder) : Prop :=
  ∀ z ∈ K, ∃ i : Fin m, z ∈ (c i).carrier

def totalArea {m : ℕ} (c : Fin m → TriCylinder) : ℝ :=
  ∑ i : Fin m, area (c i).base

def relativeCost {m : ℕ} (c : Fin m → TriCylinder) : ℝ :=
  ∑ i : Fin m, area (c i).base / shadowArea (c i).axis

def n (ε : ℝ) : ℕ := ⌈2 / ε ^ 2⌉₊
end TriangularCovering
end
end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def η : ℝ := 1 / 1000

def alpha (a b : ℝ) : ℝ := (1 + a * b) / 4

def beta (a b : ℝ) : ℝ := (a + b) / 4

def d (q : ℝ) : ℝ := q ^ 2 * (1 + q ^ 2) / 16

def cutoffCoeff (a b : ℝ) : ℝ := η + max (d a) (d b)

def step (N : ℕ) : ℝ := 2 / N

def mesh (N i : ℕ) : ℝ := -1 + i * step N

def cutoff (ε a b : ℝ) : ℝ := 1 / 2 + ε ^ 2 * cutoffCoeff a b

def speedSq (a b : ℝ) : ℝ := (alpha a b)^2 + 2*(beta a b)^2

def normalizedTerm (ε a b : ℝ) : ℝ :=
  (b-a) * (cutoff ε a b)^2 / Real.sqrt (1+ε^2*speedSq a b)

end TriangularCovering
end
end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def unit (v : Space) : Space := ‖v‖⁻¹ • v

end TriangularCovering
end
end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def tiltV (ε A B : ℝ) : Space := !₂[1, ε*A, H*ε*B]

def tiltW (ε A B : ℝ) : Space := !₂[-ε*A, 1, H*ε*B]

def lowerVertices (a b T : ℝ) : Fin 3 → Space :=
  ![point 0 0 0, point 0 (a*T) T, point 0 (b*T) T]

def upperVertices (a b T : ℝ) : Fin 3 → Space :=
  ![point 0 0 1, point (a*T) 0 (1-T), point (b*T) 0 (1-T)]

end TriangularCovering
end
end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering.Planar

abbrev Coord := Fin 2 → ℝ

def standard : Set Coord := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}

def vertices : Fin 3 → Coord := ![0, ![1, 0], ![0, 1] ]

end TriangularCovering.Planar

namespace TriangularCovering

section Triangles
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def triangle (a b c : E) : Set E := convexHull ℝ (range (![a, b, c] : Fin 3 → E))

end Triangles
end TriangularCovering
end
end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section
open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace TriangularCovering

def lowerAngularIndex {N : ℕ} (j : Fin N) : Fin (2*N) :=
  Fin.cast (two_mul N).symm (Fin.castAdd N j)

def upperAngularIndex {N : ℕ} (j : Fin N) : Fin (2*N) :=
  Fin.cast (two_mul N).symm (Fin.natAdd N j)

def lowerAngularAxis (ε : ℝ) (j : ℕ) : Space :=
  let a := mesh (n ε) j
  let b := mesh (n ε) (j+1)
  unit (tiltV ε (alpha a b) (beta a b))

def upperAngularAxis (ε : ℝ) (j : ℕ) : Space :=
  let a := mesh (n ε) j
  let b := mesh (n ε) (j+1)
  unit (tiltW ε (alpha a b) (beta a b))

def lowerAngularBase (ε : ℝ) (j : ℕ) : Set Space :=
  let a := mesh (n ε) j
  let b := mesh (n ε) (j+1)
  let v := lowerVertices a b (cutoff ε a b)
  projection (lowerAngularAxis ε j) '' triangle (v 0) (v 1) (v 2)

def upperAngularBase (ε : ℝ) (j : ℕ) : Set Space :=
  let a := mesh (n ε) j
  let b := mesh (n ε) (j+1)
  let v := upperVertices a b (cutoff ε a b)
  projection (upperAngularAxis ε j) '' triangle (v 0) (v 1) (v 2)

def ExplicitAngularFamily (ε : ℝ) (c : Fin (2*n ε) → TriCylinder) : Prop :=
  ∀ j : Fin (n ε),
    (c (lowerAngularIndex j)).axis = lowerAngularAxis ε j ∧
    (c (lowerAngularIndex j)).base = lowerAngularBase ε j ∧
    (c (upperAngularIndex j)).axis = upperAngularAxis ε j ∧
    (c (upperAngularIndex j)).base = upperAngularBase ε j

def AngularAreaStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ c : Fin (2*n ε) → TriCylinder,
      ExplicitAngularFamily ε c ∧
      totalArea c/H = ∑ j : Fin (n ε),
        normalizedTerm ε (mesh (n ε) j) (mesh (n ε) (j+1)) ∧
      |totalArea c/H - (1/2-(13/6000:ℝ)*ε^2)| ≤ 2*ε^4

def ExplicitAngularStatement : Prop :=
  A_min = H ∧
  ∀ ε : ℝ, 0 < ε → ε ≤ 1/2000 →
    ∃ c : Fin (2*n ε) → TriCylinder,
      ExplicitAngularFamily ε c ∧ Covers c ∧
      |totalArea c/H - (1/2-(13/6000:ℝ)*ε^2)| ≤ 2*ε^4 ∧
      totalArea c < A_min/2 ∧ relativeCost c < 1/2

end TriangularCovering
end
end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section
noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise
namespace RuledApproximation

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)
def vec2 (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]
def vec3 (x y z : ℝ) : Space := WithLp.toLp 2 ![x, y, z]
def axial (s : ℝ) (p : Plane) : Space := vec3 s (p 0) (p 1)

def IsParallelogram {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : Prop :=
  ∃ c u v : E, LinearIndependent ℝ ![u, v] ∧
    P = {x | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      x = c + s • u + t • v}
structure Cylinder where
  axis : Space
  unit_axis : ‖axis‖ = 1
  base : Set ((Submodule.span ℝ ({axis} : Set Space))ᗮ)

namespace Cylinder

def carrier (C : Cylinder) : Set Space :=
  {x | ∃ b ∈ C.base, ∃ t : ℝ, x = (b : Space) + t • C.axis}

def area (C : Cylinder) : ℝ := volume.real C.base

def parallelogram (C : Cylinder) : Prop := IsParallelogram C.base

def openBounded (C : Cylinder) : Prop :=
  IsOpen C.base ∧ Bornology.IsBounded C.base ∧ MeasurableSet C.base
end Cylinder

def familySet {n : ℕ} (C : Fin n → Cylinder) : Set Space := ⋃ i, (C i).carrier
def familyArea {n : ℕ} (C : Fin n → Cylinder) : ℝ := ∑ i, (C i).area

def HasFiniteCover (shape : Cylinder → Prop) (S : Set Space) (A : ℝ) : Prop :=
  ∃ n : ℕ, ∃ C : Fin n → Cylinder,
    (∀ i, shape (C i)) ∧ S ⊆ familySet C ∧ familyArea C ≤ A

def SmoothNear (n : WithTop ℕ∞) (D : Set Plane) (v : Plane → Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ D ⊆ U ∧ ContDiffOn ℝ n v U

def HyperbolicAt (L : ℝ) (v : Plane → Plane) (p : Plane) : Prop :=
  ∃ lam : ℝ, 0 < L * lam ∧ L * lam < 1 ∧
    Module.End.HasEigenvalue (fderiv ℝ v p).toLinearMap lam ∧
    Module.End.HasEigenvalue (fderiv ℝ v p).toLinearMap (-lam)

def weight (v : Plane) : ℝ := 1 / Real.sqrt (1 + ‖v‖ ^ 2)
def physicalWeight (h : ℝ) (w : Plane) : ℝ :=
  1 / Real.sqrt (1 + w 0 ^ 2 + h ^ 2 * w 1 ^ 2)

def ruled (D : Set Plane) (v : Plane → Plane) (L : ℝ) : Set Space :=
  {z | ∃ p ∈ D, ∃ r : ℝ, |r| ≤ L ∧
    z = vec3 (p 0 + r * v p 0) (p 1 + r * v p 1) r}

def physicalRuled (h : ℝ) (D : Set Plane) (v : Plane → Plane) (L : ℝ) : Set Space :=
  {z | ∃ p ∈ D, ∃ s : ℝ, |s| ≤ L ∧
    z = vec3 s (p 0 + s * v p 0) (h * (p 1 + s * v p 1))}

def HyperbolicStatement : Prop :=
  ∀ (D : Set Plane) (v : Plane → Plane) (L : ℝ),
    IsCompact D → SmoothNear 1 D v → 0 < L →
    (∀ p ∈ D, HyperbolicAt L v p) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.parallelogram (ruled D v L)
      ((∫ p in D, weight (v p)) + e)

def unitSquare : Set Plane := {x | ∀ i, |x i| ≤ (1 : ℝ) / 2}

def IsSquareTile (T : Set Plane) : Prop :=
  ∃ c : Plane, ∃ R : Plane ≃ₗᵢ[ℝ] Plane, ∃ a : ℝ, 0 < a ∧
    T = (fun x => c + a • R x) '' unitSquare

def auxiliaryCylinder (T : Set Plane) (g : Plane) : Set Space :=
  {z | ∃ s : ℝ, ∃ b ∈ T, z = axial s (b + s • g)}

def firstPhysicalMap (h : ℝ) (z : Space) : Space := vec3 (z 0) (z 1) (h * z 2)
def secondPhysicalMap (h a : ℝ) (z : Space) : Space :=
  vec3 (z 1) (z 0) (h * (a - z 2))
end RuledApproximation
end
end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace CylinderCovering

abbrev Space := EuclideanSpace ℝ (Fin 3)

def IsRegularTetrahedron (K : Set Space) : Prop :=
  ∃ v : Fin 4 → Space, AffineIndependent ℝ v ∧
    ∃ edge : ℝ, 0 < edge ∧
      (∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge) ∧
      K = convexHull ℝ (range v)

def shadowArea (K : Set Space) (u : Space) : ℝ :=
  TriangularCovering.area (TriangularCovering.projection u '' K)

def minimumShadowArea (K : Set Space) : ℝ :=
  sInf {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = shadowArea K u}

def triangularCovers {n : ℕ} (K : Set Space)
    (C : Fin n → TriangularCovering.TriCylinder) : Prop :=
  ∀ x ∈ K, ∃ i : Fin n, x ∈ (C i).carrier

def triangularRelativeCost {n : ℕ} (K : Set Space)
    (C : Fin n → TriangularCovering.TriCylinder) : ℝ :=
  ∑ i, TriangularCovering.area (C i).base / shadowArea K (C i).axis

def relativeCost {n : ℕ} (K : Set Space)
    (C : Fin n → RuledApproximation.Cylinder) : ℝ :=
  ∑ i, (C i).area / shadowArea K (C i).axis

def AngularExplicitStatement : Prop :=
  TriangularCovering.AngularAreaStatement ∧ TriangularCovering.ExplicitAngularStatement

def RegularTriangularCounterexampleStatement : Prop :=
  ∀ K : Set Space, IsRegularTetrahedron K →
    ∃ n : ℕ, ∃ C : Fin n → TriangularCovering.TriCylinder,
      triangularCovers K C ∧
      TriangularCovering.totalArea C < minimumShadowArea K / 2 ∧
      triangularRelativeCost K C < 1 / 2

def RegularParallelogramCounterexampleStatement : Prop :=
  ∀ K : Set Space, IsRegularTetrahedron K →
    ∃ n : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
      (∀ i, (C i).parallelogram) ∧
      K ⊆ RuledApproximation.familySet C ∧
      RuledApproximation.familyArea C < minimumShadowArea K / 2 ∧
      relativeCost K C < 1 / 2

def RegularOpenCounterexampleStatement : Prop :=
  ∀ K : Set Space, IsRegularTetrahedron K →
    ∃ n : ℕ, ∃ C : Fin n → RuledApproximation.Cylinder,
      (∀ i, (C i).openBounded) ∧
      K ⊆ RuledApproximation.familySet C ∧
      RuledApproximation.familyArea C < minimumShadowArea K / 2 ∧
      relativeCost K C < 1 / 2

end CylinderCovering
end
end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace RuledApproximation

def NilpotentC1Statement : Prop :=
  ∀ (D : Set Plane) (G : Plane → Plane), IsCompact D → SmoothNear 1 D G →
    (∀ b ∈ D, (fderiv ℝ G b).comp (fderiv ℝ G b) = 0) →
    ∀ h eps : ℝ, 0 < h → 0 < eps →
    ∃ n : ℕ, ∃ T : Fin n → Set Plane, ∃ g : Fin n → Plane,
      (∀ i, IsSquareTile (T i)) ∧
      physicalRuled 1 D G 1 ⊆ ⋃ i, auxiliaryCylinder (T i) (g i) ∧
      (∑ i, volume.real (T i) * physicalWeight h (g i)) ≤
        (∫ b in D, physicalWeight h (G b)) + eps ∧
      ∀ a : ℝ, ∃ C₁ C₂ : Fin n → Cylinder,
        (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram ∧
          (C₁ i).carrier = firstPhysicalMap h '' auxiliaryCylinder (T i) (g i) ∧
          (C₂ i).carrier = secondPhysicalMap h a '' auxiliaryCylinder (T i) (g i) ∧
          (C₁ i).area = h * volume.real (T i) * physicalWeight h (g i) ∧
          (C₂ i).area = h * volume.real (T i) * physicalWeight h (g i))

end RuledApproximation
end
end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section
noncomputable section
namespace CylinderCovering.RadialRiemann
open Set

def step (a b : ℝ) (N : ℕ) : ℝ := (b - a) / N

def point (a b : ℝ) (N i : ℕ) : ℝ := a + i * step a b N

def cell (a b : ℝ) (N : ℕ) (i : Fin N) : Set ℝ :=
  Icc (point a b N i) (point a b N (i + 1))

def IsTagged (a b : ℝ) (N : ℕ) (tag : Fin N → ℝ) : Prop :=
  ∀ i, tag i ∈ cell a b N i

def capMax (R : ℝ → ℝ) (a b : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  sSup (R '' cell a b N i)
end CylinderCovering.RadialRiemann
end
end

run_cmd Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

section
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
end

namespace CylinderCovering

theorem fourPaperMain :
    AngularExplicitStatement ∧
    RuledApproximation.HyperbolicStatement ∧
    RuledApproximation.NilpotentC1Statement ∧
    RegularParallelogramCounterexampleStatement ∧
    RegularOpenCounterexampleStatement ∧
    RadialSweep.AlignedStatement ∧
    RadialSweep.ActualSweepStatement := by
  sorry

end CylinderCovering

end OAI
