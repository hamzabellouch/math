import OAI.MeasureTheory.Falconer.Shells.AngularShellEnergy

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem measurable_sourceAngularTransform (ρ : Measure Plane) [IsFiniteMeasure ρ]
    (X : Set Plane) (M : ℝ) (b : Plane → UnitCircle → ℂ)
    (hb : Measurable (fun z : Plane × UnitCircle => b z.1 z.2)) :
    Measurable (fun z : ℝ × UnitCircle => sourceAngularTransform ρ X M b z.1 z.2) := by
  have hf : Measurable (fun z : (ℝ × UnitCircle) × Plane =>
      Complex.exp (Complex.I * (z.1.1 : ℂ) * (inner ℝ (z.1.2 : Plane) z.2 : ℂ)) * b z.2 z.1.2) := by
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν := ρ.restrict X)).measurable
  exact (measurable_const (a := (M⁻¹ : ℝ))).smul hi

theorem sourceAngularTransform_two_profile (ρ₁ ρ₂ : Measure Plane)
    [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂] (X Y : Set Plane) (M₁ M₂ a v : ℝ)
    (b₁ b₂ : Plane → UnitCircle → ℂ)
    (hb₁ : Measurable (fun z : Plane × UnitCircle => b₁ z.1 z.2))
    (hb₂ : Measurable (fun z : Plane × UnitCircle => b₂ z.1 z.2)) (Ψ : ℝ → ℝ) :
    sourceAngularH a v Ψ
      (fun z => sourceAngularTransform ρ₁ X M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ρ₂ Y M₂ b₂ z.1 z.2) ≤
    (sourceAngularH a v Ψ
      (fun z => sourceAngularTransform ρ₁ X M₁ b₁ z.1 z.2)
      (fun z => sourceAngularTransform ρ₁ X M₁ b₁ z.1 z.2))^(1/2 : ℝ) *
    (sourceAngularH a v Ψ
      (fun z => sourceAngularTransform ρ₂ Y M₂ b₂ z.1 z.2)
      (fun z => sourceAngularTransform ρ₂ Y M₂ b₂ z.1 z.2))^(1/2 : ℝ) :=
  sourceAngularH_two_profile a v Ψ _ _ (measurable_sourceAngularTransform ρ₁ X M₁ b₁ hb₁)
    (measurable_sourceAngularTransform ρ₂ Y M₂ b₂ hb₂)

end PlanarFalconer

end OAI
