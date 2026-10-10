import OAI.Geometry.RuledCovering.Model
import OAI.Geometry.CylinderCovering.Singular.CutoffDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory Filter Topology

namespace CylinderCovering.FlexibleSingular
open RuledApproximation

def labelDomain (p c d q : ℝ) : Set Plane :=
  {b | d ≤ b 1 ∧ b 1 ≤ 2 ∧ |b 0| ≤ b 1 ∧
    b 1 ≤ (1 / 2 : ℝ) + c ^ 2 * ceilingPolynomial p (b 0) + q}

def lowerFamily (p c d q : ℝ) : Set Space :=
  physicalRuled (Real.sqrt 2) (labelDomain p c d q)
    (fun b => c • singularField p b) 1

def upperFamily (p c d q : ℝ) : Set Space :=
  {z | ∃ b ∈ labelDomain p c d q, ∃ y : ℝ, |y| ≤ 1 ∧
    z = vec3 (b 0 - c * y * singularField p b 0) y
      (Real.sqrt 2 * (1 - (b 1 - c * y * singularField p b 1)))}

def cost (p c d q : ℝ) : ℝ :=
  Real.sqrt 2 * ∫ b in labelDomain p c d q,
    physicalWeight (Real.sqrt 2) (c • singularField p b)

def Statement : Prop :=
  ∀ (p : ℝ) (ρ q : ℝ → ℝ), 1 < p → p < (Real.sqrt 51 - 5) / 2 →
    SingularCutoff.Admissible p ρ q →
    singularCoefficient p < 0 ∧
    Asymptotics.IsLittleO (𝓝[>] (0 : ℝ))
      (fun c => 2 * cost p c (ρ c) (q c) + 8 * Real.sqrt 2 * (ρ c) ^ 2 -
        (Real.sqrt 2 / 2 + 2 * Real.sqrt 2 * singularCoefficient p * c ^ 2))
      (fun c => c ^ 2) ∧
    ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      ∃ n m : ℕ, ∃ C : Fin n → Cylinder, ∃ D : Fin m → Cylinder,
      ∃ B₁ B₂ : Cylinder,
        (∀ i, (C i).parallelogram) ∧ (∀ j, (D j).parallelogram) ∧
        B₁.triangle ∧ B₂.triangle ∧
        lowerFamily p c (ρ c) (q c) ⊆ familySet C ∧
        upperFamily p c (ρ c) (q c) ⊆ familySet D ∧
        B₁.carrier = lowerTip (ρ c) ∧ B₂.carrier = upperTip (ρ c) ∧
        B₁.area = 4 * Real.sqrt 2 * (ρ c) ^ 2 ∧
        B₂.area = 4 * Real.sqrt 2 * (ρ c) ^ 2 ∧
        tetrahedron ⊆ familySet C ∪ familySet D ∪ B₁.carrier ∪ B₂.carrier ∧
        familyArea C + familyArea D + B₁.area + B₂.area < Real.sqrt 2 / 2

def OrthogonalStatement : Prop :=
  ∀ (p : ℝ) (ρ q : ℝ → ℝ), 1 < p → p < 2 →
    SingularCutoff.Admissible p ρ q →
    (∀ c : ℝ, volume (frontier (labelDomain p c (ρ c) (q c))) = 0) ∧
    (∀ e : ℝ, 0 < e → ∀ᶠ c : ℝ in 𝓝[>] 0,
      ∀ z ∈ labelDomain p c (ρ c) (q c),
        ‖fderiv ℝ (fun w => c • singularField p w) z‖ < e ∧
        ‖fderiv ℝ (fun w => -c • singularField p w) z‖ < e) ∧
    ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ e : ℝ, 0 < e →
      HasFiniteCover Cylinder.parallelogram (lowerFamily p c (ρ c) (q c))
        (cost p c (ρ c) (q c)+e) ∧
      HasFiniteCover Cylinder.parallelogram (upperFamily p c (ρ c) (q c))
        (cost p c (ρ c) (q c)+e)

end CylinderCovering.FlexibleSingular

end

end OAI
