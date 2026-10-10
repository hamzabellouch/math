import OAI.MeasureTheory.Falconer.Estimates.SphericalEnergy

namespace OAI

/-!
# The two independent angular variables in one graph term

For fixed spatial points, the four-point phase separates into two sphere
integrals. A nonstationary bound in either variable can thus be used without
any angle separation or pointwise truncation of the amplitude.
-/

namespace Falconer
open MeasureTheory

noncomputable def sphereOscillator {d : ℕ} (Λ : ℝ) (v : Space d) (w : Sphere d) : ℂ :=
  Complex.exp (Complex.I*(Λ : ℂ)*(inner ℝ (w : Space d) v : ℂ))

@[simp] theorem sphereOscillator_norm {d : ℕ} (Λ : ℝ) (v : Space d) (w : Sphere d) :
    ‖sphereOscillator Λ v w‖ = 1 := by
  simp [sphereOscillator,Complex.norm_exp]

theorem angular_pair_factorization {d : ℕ} (Λ : ℝ) (v₁ v₂ : Space d)
    (b₁ b₂ : Sphere d → ℂ) :
    (∫ z : Sphere d × Sphere d,
      Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (z.1 : Space d) v₁ : ℂ)+(inner ℝ (z.2 : Space d) v₂ : ℂ))) *
          b₁ z.1 * b₂ z.2 ∂(sphereMeasure d).prod (sphereMeasure d)) =
      (∫ w, sphereOscillator Λ v₁ w*b₁ w ∂sphereMeasure d) *
        (∫ w, sphereOscillator Λ v₂ w*b₂ w ∂sphereMeasure d) := by
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [sphereOscillator]
  rw [mul_add,Complex.exp_add]
  ring

theorem angular_pair_bound {d : ℕ} (Λ : ℝ) (v₁ v₂ : Space d)
    (b₁ b₂ : Sphere d → ℂ) {A B : ℝ} (hA : 0 ≤ A)
    (hfirst : ‖∫ w, sphereOscillator Λ v₁ w*b₁ w ∂sphereMeasure d‖ ≤ A)
    (hsecond : ∀ w, ‖b₂ w‖ ≤ B) :
    ‖∫ z : Sphere d × Sphere d,
      Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (z.1 : Space d) v₁ : ℂ)+(inner ℝ (z.2 : Space d) v₂ : ℂ))) *
          b₁ z.1 * b₂ z.2 ∂(sphereMeasure d).prod (sphereMeasure d)‖ ≤
      A*(B*(sphereMeasure d).real Set.univ) := by
  rw [angular_pair_factorization,norm_mul]
  apply mul_le_mul hfirst _ (norm_nonneg _) hA
  apply norm_integral_le_of_norm_le_const
  filter_upwards with w
  simpa only [norm_mul,sphereOscillator_norm,one_mul] using hsecond w

theorem angular_pair_outer_bound {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Λ : ℝ) (v₁ v₂ : X → Space d)
    (b₁ b₂ : X → Sphere d → ℂ) {A B : ℝ} (hA : 0 ≤ A)
    (hfirst : ∀ x, ‖∫ w, sphereOscillator Λ (v₁ x) w*b₁ x w ∂sphereMeasure d‖ ≤ A)
    (hsecond : ∀ x w, ‖b₂ x w‖ ≤ B) :
    ‖∫ x, ∫ z : Sphere d × Sphere d,
      Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (z.1 : Space d) (v₁ x) : ℂ)+(inner ℝ (z.2 : Space d) (v₂ x) : ℂ))) *
          b₁ x z.1 * b₂ x z.2 ∂(sphereMeasure d).prod (sphereMeasure d) ∂μ‖ ≤
      (A*(B*(sphereMeasure d).real Set.univ))*μ.real Set.univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards with x
  exact angular_pair_bound Λ (v₁ x) (v₂ x) (b₁ x) (b₂ x) hA (hfirst x) (hsecond x)

end Falconer

end OAI
