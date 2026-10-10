import OAI.Geometry.CylinderCovering.Singular.BasicDefinitions
import OAI.Geometry.CylinderCovering.Singular.EdgeOneDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory Filter Topology

namespace CylinderCovering.SingularEdgeOneCover
open RuledApproximation

def map (z : Space) : Space := vec3 (z 1 / 2) (z 0 / 2) (z 2 / 2)

def height : ℝ := 1 / Real.sqrt 2

def tetrahedron : Set Space :=
  {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ |z 0| ≤ s / 2 ∧
    |z 1| ≤ (1 - s) / 2 ∧ z 2 = height * s}

def labelDomain (p k d q : ℝ) : Set Plane :=
  {b | d ≤ b 1 ∧ b 1 ≤ 1 ∧ |b 0| ≤ b 1 / 2 ∧
    b 1 ≤ (1 / 2 : ℝ) + k ^ 2 * SingularEdgeOne.edgeCeiling p (b 0) + q}

def lowerFamily (p k d q : ℝ) : Set Space :=
  {z | ∃ b ∈ labelDomain p k d q, ∃ y : ℝ, |y| ≤ 1 / 2 ∧
    z = vec3 (b 0 + k * y * SingularEdgeOne.edgeU p (b 0) (b 1)) y
      (height * (b 1 + k * y * SingularEdgeOne.edgeV p (b 0) (b 1)))}

def upperFamily (p k d q : ℝ) : Set Space :=
  {z | ∃ b ∈ labelDomain p k d q, ∃ x : ℝ, |x| ≤ 1 / 2 ∧
    z = vec3 x (b 0 - k * x * SingularEdgeOne.edgeU p (b 0) (b 1))
      (height * (1 - (b 1 - k * x * SingularEdgeOne.edgeV p (b 0) (b 1))))}

def lowerTip (d : ℝ) : Set Space :=
  {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 2 * d ∧ |z 0| ≤ s / 2 ∧ z 2 = height * s}

def upperTip (d : ℝ) : Set Space :=
  {z | ∃ s : ℝ, 0 ≤ s ∧ s ≤ 2 * d ∧ |z 1| ≤ s / 2 ∧ z 2 = height * (1 - s)}

def cost (p k d q : ℝ) : ℝ :=
  height * ∫ b in labelDomain p k d q,
    physicalWeight height
      (k • vec2 (SingularEdgeOne.edgeU p (b 0) (b 1))
        (SingularEdgeOne.edgeV p (b 0) (b 1)))

def FiniteCoverAt (p k d q : ℝ) : Prop :=
  ∃ n m : ℕ, ∃ C : Fin n → Cylinder, ∃ D : Fin m → Cylinder,
  ∃ B₁ B₂ : Cylinder,
    (∀ i, (C i).parallelogram) ∧ (∀ j, (D j).parallelogram) ∧
    B₁.triangle ∧ B₂.triangle ∧
    lowerFamily p k d q ⊆ familySet C ∧ upperFamily p k d q ⊆ familySet D ∧
    B₁.carrier = lowerTip d ∧ B₂.carrier = upperTip d ∧
    B₁.area = 2 * height * d ^ 2 ∧ B₂.area = 2 * height * d ^ 2 ∧
    tetrahedron ⊆ familySet C ∪ familySet D ∪ B₁.carrier ∪ B₂.carrier ∧
    familyArea C + familyArea D + B₁.area + B₂.area < height / 4

def AlternativeStatement : Prop :=
  ∀ p β : ℝ, 1 < p → p < (Real.sqrt 51 - 5) / 2 →
    1 < β → β < 1 / (2 - p) →
    ∀ᶠ k : ℝ in 𝓝[>] 0, FiniteCoverAt p k (k ^ β) (k ^ (5 / 2 : ℝ))

def FlexibleStatement : Prop :=
  ∀ (p : ℝ) (ρ q : ℝ → ℝ), 1 < p → p < (Real.sqrt 51-5)/2 →
    SingularCutoff.Admissible p ρ q →
    ∀ᶠ k : ℝ in 𝓝[>] 0, FiniteCoverAt p k (ρ (k/4)) (q (k/4))

def ExactStatement : Prop :=
  ∀ p γ : ℝ, 1 < p → p < (Real.sqrt 51-5)/2 →
    1 < γ → γ < 1/(2-p) →
    ∀ᶠ k : ℝ in 𝓝[>] 0,
      FiniteCoverAt p k ((4:ℝ)^(-γ)*k^γ) (k^(5/2:ℝ)/32)

def CostAt (p k d q : ℝ) : Prop :=
  2*cost p k d q+4*height*d^2 < height/4 ∧
  ∀ e : ℝ, 0 < e →
    HasFiniteCover Cylinder.parallelogram (lowerFamily p k d q) (cost p k d q+e) ∧
    HasFiniteCover Cylinder.parallelogram (upperFamily p k d q) (cost p k d q+e)

def CostStatement : Prop :=
  ∀ (p : ℝ) (ρ q : ℝ → ℝ), 1 < p → p < (Real.sqrt 51-5)/2 →
    SingularCutoff.Admissible p ρ q →
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun k => cost p k (ρ (k/4)) (q (k/4))/height-
        (1/8+singularCoefficient p/32*k^2)) (fun k => k^2) ∧
    ∀ᶠ k : ℝ in 𝓝[>] 0, CostAt p k (ρ (k/4)) (q (k/4))

def AlternativeCostStatement : Prop :=
  ∀ p β : ℝ, 1 < p → p < (Real.sqrt 51-5)/2 →
    1 < β → β < 1/(2-p) →
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun k => cost p k (k^β) (k^(5/2:ℝ))/height-
        (1/8+singularCoefficient p/32*k^2)) (fun k => k^2) ∧
    ∀ᶠ k : ℝ in 𝓝[>] 0, CostAt p k (k^β) (k^(5/2:ℝ))

end CylinderCovering.SingularEdgeOneCover

end

end OAI
