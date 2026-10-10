import OAI.MeasureTheory.Falconer.Angular.AngularPair

namespace OAI

/-!
# Fubini for the spatially expanded angular term

Bounded measurable amplitudes on finite original laws are sufficient.
There is no spatial differentiability requirement and no change of the
point labels in the two endpoint factors.
-/

namespace Falconer
open MeasureTheory

theorem angular_pair_spatial_swap {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Λ : ℝ) (v₁ v₂ : X → Space d)
    (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (b₁ b₂ : X → Sphere d → ℂ)
    (hb₁ : Measurable (Function.uncurry b₁)) (hb₂ : Measurable (Function.uncurry b₂))
    {B C : ℝ} (hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hbound₁ : ∀ x w, ‖b₁ x w‖ ≤ B) (hbound₂ : ∀ x w, ‖b₂ x w‖ ≤ C) :
    (∫ z : Sphere d × Sphere d, ∫ x,
      Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (z.1 : Space d) (v₁ x) : ℂ)+(inner ℝ (z.2 : Space d) (v₂ x) : ℂ))) *
          b₁ x z.1 * b₂ x z.2 ∂μ ∂(sphereMeasure d).prod (sphereMeasure d)) =
      ∫ x, (∫ w, sphereOscillator Λ (v₁ x) w*b₁ x w ∂sphereMeasure d) *
        (∫ w, sphereOscillator Λ (v₂ x) w*b₂ x w ∂sphereMeasure d) ∂μ := by
  let F : X × (Sphere d × Sphere d) → ℂ := fun p =>
    Complex.exp (Complex.I*(Λ : ℂ)*
      ((inner ℝ (p.2.1 : Space d) (v₁ p.1) : ℂ)+
       (inner ℝ (p.2.2 : Space d) (v₂ p.1) : ℂ))) * b₁ p.1 p.2.1 * b₂ p.1 p.2.2
  have hm : Measurable F := by
    apply Measurable.mul
    · apply Measurable.mul
      · fun_prop
      · exact hb₁.comp (measurable_fst.prodMk measurable_snd.fst)
    · exact hb₂.comp (measurable_fst.prodMk measurable_snd.snd)
  have hnorm (p : X × (Sphere d × Sphere d)) : ‖F p‖ ≤ B*C := by
    have hexp : ‖Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (p.2.1 : Space d) (v₁ p.1) : ℂ)+
         (inner ℝ (p.2.2 : Space d) (v₂ p.1) : ℂ)))‖ = 1 := by
      simp [Complex.norm_exp]
    simp only [F,norm_mul,hexp,one_mul]
    exact mul_le_mul (hbound₁ _ _) (hbound₂ _ _) (norm_nonneg _) hB
  have hi : Integrable F (μ.prod ((sphereMeasure d).prod (sphereMeasure d))) :=
    Integrable.of_bound hm.aestronglyMeasurable (B*C) (Filter.Eventually.of_forall hnorm)
  calc
    _ = ∫ x, ∫ z : Sphere d × Sphere d, F (x,z)
        ∂(sphereMeasure d).prod (sphereMeasure d) ∂μ := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      exact angular_pair_factorization Λ (v₁ x) (v₂ x) (b₁ x) (b₂ x)

end Falconer

end OAI
