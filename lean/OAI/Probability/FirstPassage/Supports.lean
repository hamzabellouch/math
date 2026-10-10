import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace PlanarFPP

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem support_le_of_positive_halfspace (μ : E → ℝ) (x f : E →ₗ[ℝ] ℝ) (u : E)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hfu : f u = μ u)
    (hhalf : ∀ z, 0 < x z → f z ≤ μ z) : ∀ z, f z ≤ μ z := by
  intro z
  let t : ℝ := |x z| + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 < x (z + t • u) := by
    simp only [map_add, map_smul, hxu, smul_eq_mul, mul_one]
    dsimp [t]
    linarith [neg_le_abs (x z)]
  have hh := hhalf (z + t • u) hz
  have ha := hadd z (t • u)
  rw [hhom t ht u] at ha
  simp only [map_add, map_smul, smul_eq_mul, hfu] at hh
  linarith

noncomputable def coordinateSupport (x r : E →ₗ[ℝ] ℝ) (m a : ℝ) : E →ₗ[ℝ] ℝ :=
  m • x + a • r

@[simp] theorem coordinateSupport_apply (x r : E →ₗ[ℝ] ℝ) (m a : ℝ) (z : E) :
    coordinateSupport x r m a z = m * x z + a * r z := rfl

theorem support_from_transverse_subgradient (μ : E → ℝ) (x r : E →ₗ[ℝ] ℝ)
    (u e : E) (a : ℝ)
    (hadd : ∀ z w, μ (z + w) ≤ μ z + μ w)
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ z, μ (t • z) = t * μ z)
    (hxu : x u = 1) (hru : r u = 0)
    (hcoords : ∀ z, z = x z • u + r z • e)
    (hsub : ∀ t : ℝ, μ u + a * t ≤ μ (u + t • e)) :
    (∀ z, coordinateSupport x r (μ u) a z ≤ μ z) ∧
      coordinateSupport x r (μ u) a u = μ u := by
  have hcontact : coordinateSupport x r (μ u) a u = μ u := by
    simp [hxu, hru]
  refine ⟨support_le_of_positive_halfspace μ x _ u hadd hhom hxu hcontact ?_, hcontact⟩
  intro z hz
  have hrepr : z = x z • (u + (r z / x z) • e) := by
    rw [smul_add, smul_smul]
    have heq : x z * (r z / x z) = r z := by field_simp [ne_of_gt hz]
    rw [heq]
    exact hcoords z
  have hbound := mul_le_mul_of_nonneg_left (hsub (r z / x z)) (le_of_lt hz)
  have hμ : μ z = x z * μ (u + (r z / x z) • e) := by
    conv_lhs => rw [hrepr]
    exact hhom _ (le_of_lt hz) _
  rw [coordinateSupport_apply, hμ]
  calc
    μ u * x z + a * r z = x z * (μ u + a * (r z / x z)) := by
      field_simp [ne_of_gt hz]
    _ ≤ x z * μ (u + (r z / x z) • e) := hbound

theorem average_support (μ : E → ℝ) (f g : E →ₗ[ℝ] ℝ) (u : E)
    (hf : ∀ z, f z ≤ μ z) (hg : ∀ z, g z ≤ μ z)
    (hfu : f u = μ u) (hgu : g u = μ u) :
    (∀ z, ((1 / 2 : ℝ) • (f + g)) z ≤ μ z) ∧
      ((1 / 2 : ℝ) • (f + g)) u = μ u := by
  constructor
  · intro z
    change 1 / 2 * (f z + g z) ≤ μ z
    linarith [hf z, hg z]
  · change 1 / 2 * (f u + g u) = μ u
    rw [hfu, hgu]
    ring

end
end PlanarFPP

end OAI
