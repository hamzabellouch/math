import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
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

def IsTriangle {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : Prop :=
  ∃ c u v : E, LinearIndependent ℝ ![u, v] ∧
    P = {x | ∃ s : ℝ, ∃ t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧
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

def triangle (C : Cylinder) : Prop := IsTriangle C.base

def openBounded (C : Cylinder) : Prop :=
  IsOpen C.base ∧ Bornology.IsBounded C.base ∧ MeasurableSet C.base
end Cylinder

def familySet {n : ℕ} (C : Fin n → Cylinder) : Set Space := ⋃ i, (C i).carrier
def familyArea {n : ℕ} (C : Fin n → Cylinder) : ℝ := ∑ i, (C i).area

def HasFiniteCover (shape : Cylinder → Prop) (S : Set Space) (A : ℝ) : Prop :=
  ∃ n : ℕ, ∃ C : Fin n → Cylinder,
    (∀ i, shape (C i)) ∧ S ⊆ familySet C ∧ familyArea C ≤ A

/-- No boundary hypothesis is included in this neighborhood regularity predicate. -/
def SmoothNear (n : WithTop ℕ∞) (D : Set Plane) (v : Plane → Plane) : Prop :=
  ∃ U : Set Plane, IsOpen U ∧ D ⊆ U ∧ ContDiffOn ℝ n v U

/-- In dimension two these two distinct nonzero eigenvalues are all the eigenvalues. -/
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

def PhysicalHyperbolicStatement : Prop :=
  ∀ (h L : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < h → 0 < L → IsCompact D → SmoothNear 1 D v →
    (∀ p ∈ D, HyperbolicAt L v p) →
    ∀ (e : ℝ), 0 < e → ∀ F : Space ≃ᵢ Space,
    HasFiniteCover Cylinder.parallelogram (F '' physicalRuled h D v L)
      (h * (∫ p in D, physicalWeight h (v p)) + e)

def OpenRectangleC2 (D : Set Plane) (v : Plane → Plane) : Prop :=
  ∃ a b : Plane, (∀ i, a i < b i) ∧
    D ⊆ {p | ∀ i, p i ∈ Ioo (a i) (b i)} ∧
    ContDiffOn ℝ 2 v {p | ∀ i, p i ∈ Ioo (a i) (b i)}

def LogarithmicStatement : Prop :=
  ∀ (X k : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < X → 0 < k → IsCompact D → volume (frontier D) = 0 →
    OpenRectangleC2 D v →
    (∀ p ∈ D, LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ v p).toLinearMap < 0 ∧
      k * X * Real.sqrt (-LinearMap.det (fderiv ℝ v p).toLinearMap) < 1) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.openBounded
      (physicalRuled 1 D (fun p => k • v p) X)
      ((∫ p in D, 1 / Real.sqrt (1 + k ^ 2 * ‖v p‖ ^ 2)) + e)

def ProductCellStatement : Prop :=
  ∀ (h M : ℝ) (D : Set Plane) (v : Plane → Plane),
    0 < h → 0 < M → IsCompact D → volume (frontier D) = 0 →
    SmoothNear 1 D v → (∀ p ∈ D, HyperbolicAt M v p) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.openBounded (physicalRuled h D v M)
      (h * (∫ p in D, physicalWeight h (v p)) + e)

def OrthogonalGridStatement : Prop :=
  ∀ (D : Set Plane) (v : Plane → Plane) (kappa : ℝ),
    IsCompact D → volume (frontier D) = 0 → SmoothNear 1 D v → kappa < 1 →
    (∀ p ∈ D, LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ v p).toLinearMap < 0 ∧ ‖fderiv ℝ v p‖ ≤ kappa) →
    ∀ e : ℝ, 0 < e → HasFiniteCover Cylinder.parallelogram
      (physicalRuled (Real.sqrt 2) D v 1)
      (Real.sqrt 2 * (∫ p in D,
        1 / Real.sqrt (1 + v p 0 ^ 2 + 2 * v p 1 ^ 2)) + e)

def unitSquare : Set Plane := {x | ∀ i, |x i| ≤ (1 : ℝ) / 2}

def IsSquareTile (T : Set Plane) : Prop :=
  ∃ c : Plane, ∃ R : Plane ≃ₗᵢ[ℝ] Plane, ∃ a : ℝ, 0 < a ∧
    T = (fun x => c + a • R x) '' unitSquare

def auxiliaryCylinder (T : Set Plane) (g : Plane) : Set Space :=
  {z | ∃ s : ℝ, ∃ b ∈ T, z = axial s (b + s • g)}

def firstPhysicalMap (h : ℝ) (z : Space) : Space := vec3 (z 0) (z 1) (h * z 2)
def secondPhysicalMap (h a : ℝ) (z : Space) : Space :=
  vec3 (z 1) (z 0) (h * (a - z 2))

def NilpotentStatement : Prop :=
  ∀ (D : Set Plane) (G : Plane → Plane), IsCompact D → SmoothNear ∞ D G →
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

/-- The regular edge-2 tetrahedron in physical coordinates. -/
def tetrahedron : Set Space :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ |z 0| ≤ 1 - t ∧ |z 1| ≤ t ∧
    z 2 = Real.sqrt 2 * t}

def singularField (p : ℝ) (b : Plane) : Plane :=
  vec2 (((1 / 2 : ℝ) / 2) * (b 1 / (1 / 2)) ^ (p - 1) *
    (p + (2 - p) * (b 0 / b 1) ^ 2))
    ((b 1 / (1 / 2)) ^ (p - 2) * b 0)

def ceilingPolynomial (p b : ℝ) : ℝ :=
  b ^ 2 * ((1 / 2 : ℝ) * p / 2 + (2 - p) / (2 * (1 / 2)) * b ^ 2)

def singularDomain (p gamma c : ℝ) : Set Plane :=
  {b | c ^ gamma ≤ b 1 ∧ b 1 ≤ 2 ∧ |b 0| ≤ b 1 ∧
    b 1 ≤ (1 / 2 : ℝ) + c ^ 2 * ceilingPolynomial p (b 0) + c ^ (5 / 2 : ℝ)}

def singularLower (p gamma c : ℝ) : Set Space :=
  physicalRuled (Real.sqrt 2) (singularDomain p gamma c)
    (fun b => c • singularField p b) 1

def singularUpper (p gamma c : ℝ) : Set Space :=
  {z | ∃ b ∈ singularDomain p gamma c, ∃ y : ℝ, |y| ≤ 1 ∧
    z = vec3 (b 0 - c * y * singularField p b 0) y
      (Real.sqrt 2 * (1 - (b 1 - c * y * singularField p b 1)))}

def lowerTip (d : ℝ) : Set Space :=
  {z | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 2 * d ∧ |z 1| ≤ t ∧ z 2 = Real.sqrt 2 * t}

def upperTip (d : ℝ) : Set Space :=
  {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 2 * d ∧ |z 0| ≤ s ∧ z 2 = Real.sqrt 2 * (1 - s)}

def singularCost (p gamma c : ℝ) : ℝ :=
  Real.sqrt 2 * ∫ b in singularDomain p gamma c,
    physicalWeight (Real.sqrt 2) (c • singularField p b)

def singularCoefficient (p : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ 4 * (2 * p ^ 2 + 10 * p - 13) / (30 * p)

def SingularStatement : Prop :=
  ∀ p gamma : ℝ, 1 < p → p < (Real.sqrt 51 - 5) / 2 →
    1 < gamma → gamma < 1 / (2 - p) →
    singularCoefficient p < 0 ∧
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun c => 2 * singularCost p gamma c + 8 * Real.sqrt 2 * (c ^ gamma) ^ 2 -
        (Real.sqrt 2 / 2 + 2 * Real.sqrt 2 * singularCoefficient p * c ^ 2))
      (fun c => c ^ 2) ∧
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      ∃ n m : ℕ, ∃ C : Fin n → Cylinder, ∃ D : Fin m → Cylinder,
      ∃ B₁ B₂ : Cylinder,
        (∀ i, (C i).parallelogram) ∧ (∀ j, (D j).parallelogram) ∧
        B₁.triangle ∧ B₂.triangle ∧
        singularLower p gamma c ⊆ familySet C ∧
        singularUpper p gamma c ⊆ familySet D ∧
        B₁.carrier = lowerTip (c ^ gamma) ∧ B₂.carrier = upperTip (c ^ gamma) ∧
        tetrahedron ⊆ familySet C ∪ familySet D ∪ B₁.carrier ∪ B₂.carrier ∧
        familyArea C + familyArea D + B₁.area + B₂.area < Real.sqrt 2 / 2

def FullMain : Prop :=
  HyperbolicStatement ∧ PhysicalHyperbolicStatement ∧ LogarithmicStatement ∧
  ProductCellStatement ∧ OrthogonalGridStatement ∧ NilpotentStatement ∧ SingularStatement

theorem fullMain : FullMain := by
  sorry

end RuledApproximation

end

end OAI
