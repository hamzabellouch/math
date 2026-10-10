import OAI.Geometry.SurfaceImmersion.Geometry.FiniteParametrix

namespace OAI

/-! Adding a differential perturbation to a finite parametrix: the two error
parameters add, while the prescribed finite derivative loss stays explicit. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.FiniteParametrix

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma defect_add (A R : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (f : F) :
    defect (A + R) S f = defect A S f + R (S f) := by
  simp only [defect, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply]
  abel

theorem perturbed_defect_bound (A R : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E)
    (p : ℕ → Seminorm ℝ F) (L : ℕ) (K₀ K₁ : ℕ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₀ : ∀ m f, p m (defect A S f) ≤ a * K₀ m * p (m + L) f)
    (h₁ : ∀ m f, p m (R (S f)) ≤ b * K₁ m * p (m + L) f)
    (m : ℕ) (f : F) :
    p m (defect (A + R) S f) ≤ (a + b) * max (K₀ m) (K₁ m) * p (m + L) f := by
  rw [defect_add]
  calc
    _ ≤ p m (defect A S f) + p m (R (S f)) := map_add_le_add _ _ _
    _ ≤ a * K₀ m * p (m + L) f + b * K₁ m * p (m + L) f := add_le_add (h₀ m f) (h₁ m f)
    _ ≤ a * max (K₀ m) (K₁ m) * p (m + L) f +
        b * max (K₀ m) (K₁ m) * p (m + L) f := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (apply_nonneg _ _)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
          (apply_nonneg _ _)
    _ = _ := by ring

/-- The same finite algorithm improves the perturbed operator to every fixed
accuracy. The number of required input derivatives grows with that accuracy. -/
theorem perturbed_residual_bound (A R : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E) (f : F) (z : E)
    (p : ℕ → Seminorm ℝ F) (L : ℕ) (K₀ K₁ C : ℕ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : ∀ m, 0 ≤ K₀ m)
    (h₀ : ∀ m g, p m (defect A S g) ≤ a * K₀ m * p (m + L) g)
    (h₁ : ∀ m g, p m (R (S g)) ≤ b * K₁ m * p (m + L) g)
    (hinit : ∀ m, p m ((A + R) z - f) ≤ C m) (j m : ℕ) :
    p m (residual (A + R) S f z j) ≤
      (a + b) ^ j * boundProfile L (fun r => max (K₀ r) (K₁ r)) C j m := by
  exact residual_bound (A + R) S f z p L _ C (add_nonneg ha hb)
    (fun m => (hK m).trans (le_max_left _ _))
    (perturbed_defect_bound A R S p L K₀ K₁ ha hb h₀ h₁) hinit j m

end ClosedSurfaceR4.FiniteParametrix

end

end OAI
