import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Transport and correction of multiplication

These are the algebraic and norm estimates in the UCP criterion of §2 of
*Universal strong Kadison–Kastler stability* (2026). No perturbation theorem
is assumed here. If a linear equivalence correcting the transported product
is supplied, its composition with the original map gives an actual algebra
equivalence.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [NormedRing B] [NormedAlgebra ℂ B]

/-- Multiplication on the source transported through a linear equivalence. -/
def transportedMul (F : A ≃ₗ[ℂ] B) (x y : A) : A := F.symm (F x * F y)

@[simp] theorem map_transportedMul (F : A ≃ₗ[ℂ] B) (x y : A) :
    F (transportedMul F x y) = F x * F y := F.apply_symm_apply _

theorem transportedMul_assoc (F : A ≃ₗ[ℂ] B) (x y z : A) :
    transportedMul F (transportedMul F x y) z =
      transportedMul F x (transportedMul F y z) := by
  apply F.injective
  simp only [map_transportedMul, mul_assoc]

theorem transportedMul_add_left (F : A ≃ₗ[ℂ] B) (x y z : A) :
    transportedMul F (x + y) z = transportedMul F x z + transportedMul F y z := by
  simp only [transportedMul, map_add, add_mul]

theorem transportedMul_add_right (F : A ≃ₗ[ℂ] B) (x y z : A) :
    transportedMul F x (y + z) = transportedMul F x y + transportedMul F x z := by
  simp only [transportedMul, map_add, mul_add]

theorem transportedMul_smul_left (F : A ≃ₗ[ℂ] B) (c : ℂ) (x y : A) :
    transportedMul F (c • x) y = c • transportedMul F x y := by
  simp only [transportedMul, map_smul, smul_mul_assoc]

theorem transportedMul_smul_right (F : A ≃ₗ[ℂ] B) (c : ℂ) (x y : A) :
    transportedMul F x (c • y) = c • transportedMul F x y := by
  simp only [transportedMul, map_smul, mul_smul_comm]

theorem transportedMul_one_left (F : A ≃ₗ[ℂ] B) (x : A) :
    transportedMul F (F.symm 1) x = x := by simp [transportedMul]

theorem transportedMul_one_right (F : A ≃ₗ[ℂ] B) (x : A) :
    transportedMul F x (F.symm 1) = x := by simp [transportedMul]

/-- The transported product differs from the original product by applying
the inverse equivalence to the original map's multiplicative defect. -/
theorem transportedMul_sub_eq (F : A ≃ₗ[ℂ] B) (x y : A) :
    transportedMul F x y - x * y = F.symm (F x * F y - F (x * y)) := by
  simp only [transportedMul, map_sub, LinearEquiv.symm_apply_apply]

/-- An inverse norm bound and a multiplicative-defect bound control the
distance between transported and original multiplication. -/
theorem norm_transportedMul_sub_le (F : A ≃ₗ[ℂ] B) {K c : ℝ} (hK : 0 ≤ K)
    (hinv : ∀ y, ‖F.symm y‖ ≤ K * ‖y‖)
    (hdefect : ∀ x y, ‖F (x * y) - F x * F y‖ ≤ c * ‖x‖ * ‖y‖)
    (x y : A) : ‖transportedMul F x y - x * y‖ ≤ (K * c) * ‖x‖ * ‖y‖ := by
  rw [transportedMul_sub_eq]
  calc
    ‖F.symm (F x * F y - F (x * y))‖ ≤ K * ‖F x * F y - F (x * y)‖ := hinv _
    _ ≤ K * (c * ‖x‖ * ‖y‖) := by
      apply mul_le_mul_of_nonneg_left _ hK
      simpa only [norm_sub_rev] using hdefect x y
    _ = (K * c) * ‖x‖ * ‖y‖ := by ring

/-- A correction intertwines the transported product and the original one;
its inverse intertwines them in the opposite direction. -/
theorem inverse_correction_mul (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y) (x y : A) :
    L.symm (x * y) = transportedMul F (L.symm x) (L.symm y) := by
  apply L.injective
  rw [L.apply_symm_apply, hL, L.apply_symm_apply, L.apply_symm_apply]

/-- The map `F ∘ L⁻¹` is multiplicative after correction. -/
theorem correctedMap_mul (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y) (x y : A) :
    F (L.symm (x * y)) = F (L.symm x) * F (L.symm y) := by
  rw [inverse_correction_mul F L hL, map_transportedMul]

/-- Bijective multiplicativity ensures the corrected map preserves the unit;
unit preservation of the original linear maps need not be assumed. -/
theorem correctedMap_one (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y) :
    F (L.symm 1) = 1 := by
  obtain ⟨x, hx⟩ := (L.symm.trans F).surjective (1 : B)
  have h := correctedMap_mul F L hL 1 x
  change F (L.symm x) = 1 at hx
  simpa only [one_mul, hx, mul_one] using h.symm

/-- The genuine algebra equivalence resulting from a correction of the
transported product. Its underlying map is exactly `F ∘ L⁻¹`. -/
def correctedAlgEquiv (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y) : A ≃ₐ[ℂ] B :=
  AlgEquiv.ofLinearEquiv (L.symm.trans F) (correctedMap_one F L hL)
    (correctedMap_mul F L hL)

@[simp] theorem correctedAlgEquiv_apply (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x y, L (transportedMul F x y) = L x * L y) (x : A) :
    correctedAlgEquiv F L hL x = F (L.symm x) := rfl

end

end KadisonKastler

end OAI
