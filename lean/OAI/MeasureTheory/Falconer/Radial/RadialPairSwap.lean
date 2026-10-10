import OAI.MeasureTheory.Falconer.Angular.AngularPairSwap
import OAI.MeasureTheory.Falconer.Radial.RadialLocalization
import OAI.MeasureTheory.Falconer.Graphs.ParentRetainedEnergy

namespace OAI

/-!
# Radial Fubini for an original-label cap pair

The finite shell law and bounded measurable endpoint factors justify moving
its integral inside both the angles and the original spatial labels. No
spatial regularity or separation of the two angles is required.
-/

namespace Falconer
open MeasureTheory

noncomputable def expandedCapTerm {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (v : ℝ) (Ψ : ℝ → ℝ) (v₁ v₂ : X → Space d)
    (b₁ b₂ : X → Sphere d → ℂ) : ℂ :=
  ∫ r, ∫ z : Sphere d × Sphere d, ∫ x,
    Complex.exp (Complex.I*(r : ℂ)*
      ((inner ℝ (z.1 : Space d) (v₁ x) : ℂ)+
       (inner ℝ (z.2 : Space d) (v₂ x) : ℂ))) * b₁ x z.1 * b₂ x z.2
    ∂μ ∂(sphereMeasure d).prod (sphereMeasure d)
    ∂PlanarFalconer.sourceAngularShellMeasure v Ψ

theorem expandedCapTerm_radial_swap {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (v : ℝ) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W) (hz : ∀ t, 4 < t → Ψ t = 0)
    (v₁ v₂ : X → Space d) (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (b₁ b₂ : X → Sphere d → ℂ)
    (hb₁ : Measurable (Function.uncurry b₁)) (hb₂ : Measurable (Function.uncurry b₂))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁)
    (hbound₁ : ∀ x w, ‖b₁ x w‖ ≤ B₁) (hbound₂ : ∀ x w, ‖b₂ x w‖ ≤ B₂) :
    expandedCapTerm μ v Ψ v₁ v₂ b₁ b₂ =
      ∫ p : (Sphere d × Sphere d) × X, ∫ r,
        (b₁ p.2 p.1.1 * b₂ p.2 p.1.2) *
        Complex.exp (Complex.I * (r *
          (inner ℝ (p.1.1 : Space d) (v₁ p.2) +
           inner ℝ (p.1.2 : Space d) (v₂ p.2)) : ℝ))
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ
        ∂((sphereMeasure d).prod (sphereMeasure d)).prod μ := by
  let := PlanarFalconer.sourceAngularShellMeasure_finite v Ψ hW hΨW hz
  let σ := ((sphereMeasure d).prod (sphereMeasure d)).prod μ
  let ρ := PlanarFalconer.sourceAngularShellMeasure v Ψ
  let F : ℝ × ((Sphere d × Sphere d) × X) → ℂ := fun p =>
    (b₁ p.2.2 p.2.1.1 * b₂ p.2.2 p.2.1.2) *
      Complex.exp (Complex.I * (p.1 *
        (inner ℝ (p.2.1.1 : Space d) (v₁ p.2.2) +
         inner ℝ (p.2.1.2 : Space d) (v₂ p.2.2)) : ℝ))
  have hm : Measurable F := by
    apply Measurable.mul
    · exact (hb₁.comp (measurable_snd.snd.prodMk measurable_snd.fst.fst)).mul
        (hb₂.comp (measurable_snd.snd.prodMk measurable_snd.fst.snd))
    · fun_prop
  have hnorm (p : ℝ × ((Sphere d × Sphere d) × X)) : ‖F p‖ ≤ B₁*B₂ := by
    have he : ‖Complex.exp (Complex.I * (p.1 *
        (inner ℝ (p.2.1.1 : Space d) (v₁ p.2.2) +
         inner ℝ (p.2.1.2 : Space d) (v₂ p.2.2)) : ℝ))‖ = 1 := by
      simp [Complex.norm_exp]
    simp only [F,norm_mul,he,mul_one]
    exact mul_le_mul (hbound₁ _ _) (hbound₂ _ _) (norm_nonneg _) hB₁
  have hi : Integrable F (ρ.prod σ) :=
    Integrable.of_bound hm.aestronglyMeasurable (B₁*B₂) (Filter.Eventually.of_forall hnorm)
  calc
    expandedCapTerm μ v Ψ v₁ v₂ b₁ b₂ = ∫ r, ∫ p, F (r,p) ∂σ ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hi.prod_right_ae] with r hr
      rw [integral_prod _ hr]
      apply integral_congr_ae
      filter_upwards with z
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [F]
      push_cast
      rw [mul_assoc Complex.I]
      ring
    _ = _ := integral_integral_swap hi

end Falconer

end OAI
