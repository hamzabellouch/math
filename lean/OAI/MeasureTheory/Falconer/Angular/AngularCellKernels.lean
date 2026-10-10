import OAI.MeasureTheory.Falconer.Angular.AngularRestrictedKernel
import OAI.MeasureTheory.Falconer.Angular.AngularTransformSplitting

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def angularCellTransform (Q : DyadicSquare) (ρ : Measure Plane)
    (M : ℝ) (β : Plane → UnitCircle → ℂ) (P : CellPath) (z : ℝ × UnitCircle) : ℂ :=
  sourceAngularTransform ρ (Q.descendant P).carrier M β z.1 z.2

theorem angularCellTransform_measurable (Q : DyadicSquare) (ρ : Measure Plane)
    [IsFiniteMeasure ρ] (M : ℝ) (β : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2)) (P : CellPath) :
    Measurable (angularCellTransform Q ρ M β P) :=
  measurable_sourceAngularTransform ρ _ M β hβ

theorem sourceAngularTransform_global_bound (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) {M : ℝ} (hM : 0 < M) (β : Plane → UnitCircle → ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hb : ∀ x u, ‖β x u‖ ≤ D) (r : ℝ) (u : UnitCircle) :
    ‖sourceAngularTransform ρ X M β r u‖ ≤ D*(ρ univ).toReal/M := by
  apply (sourceAngularTransform_norm_le ρ X M hM β D (fun x _ => hb x) r u).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (measure_ne_top ρ univ) (measure_mono (subset_univ X))) hD) hM.le

noncomputable def angularCellContribution (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (A B : CellPath) (n : ℕ) (a v : ℝ) (Ψ : ℝ → ℝ)
    (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (β γ : Plane → UnitCircle → ℂ)
    (G : (CellPath × CellPath) → (CellPath × CellPath) → Prop) : ℂ :=
  ((Mp₁/Ma₁)^2*(Mp₂/Ma₂)^2) • angularKernelIntegral a v Ψ
    (angularRestrictedKernel (sourceProductVertices Q₁ Q₂ ρ ν A B n) G
      (angularCellTransform Q₁ ρ Mp₁ β) (angularCellTransform Q₂ ν Mp₂ γ))

end PlanarFalconer

end OAI
