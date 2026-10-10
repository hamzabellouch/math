import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {E Y : Type*}
variable [AddCommGroup E] [Module ℝ E]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def spreadingRescale (δ : ℝ) (S : E →ₗ[ℝ] Y) : E →ₗ[ℝ] Y :=
  (1 - δ)⁻¹ • S

@[simp] theorem spreadingRescale_apply (δ : ℝ) (S : E →ₗ[ℝ] Y) (x : E) :
    spreadingRescale δ S x = (1 - δ)⁻¹ • S x := rfl

theorem norm_spreadingRescale (δ : ℝ) (S : E →ₗ[ℝ] Y)
    (hδ : δ < 1) (x : E) :
    ‖spreadingRescale δ S x‖ = (1 - δ)⁻¹ * ‖S x‖ := by
  have hd : 0 < 1 - δ := sub_pos.mpr hδ
  rw [spreadingRescale_apply, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]

theorem spreadingRescale_bounds (p : Seminorm ℝ E) (S : E →ₗ[ℝ] Y)
    (δ : ℝ) (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (happrox : ∀ x, |‖S x‖ - p x| ≤ δ * p x) :
    ∀ x, p x ≤ ‖spreadingRescale δ S x‖ ∧
      ‖spreadingRescale δ S x‖ ≤ ((1 + δ) / (1 - δ)) * p x := by
  intro x
  have hd : 0 < 1 - δ := sub_pos.mpr hδ1
  have hdinv : 0 ≤ (1 - δ)⁻¹ := inv_nonneg.mpr hd.le
  obtain ⟨hl, hu⟩ := abs_le.mp (happrox x)
  have hlower : (1 - δ) * p x ≤ ‖S x‖ := by linarith
  have hupper : ‖S x‖ ≤ (1 + δ) * p x := by linarith
  rw [norm_spreadingRescale δ S hδ1 x]
  constructor
  · calc
      p x = (1 - δ)⁻¹ * ((1 - δ) * p x) := by
        rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
      _ ≤ (1 - δ)⁻¹ * ‖S x‖ := mul_le_mul_of_nonneg_left hlower hdinv
  · calc
      (1 - δ)⁻¹ * ‖S x‖ ≤ (1 - δ)⁻¹ * ((1 + δ) * p x) :=
        mul_le_mul_of_nonneg_left hupper hdinv
      _ = ((1 + δ) / (1 - δ)) * p x := by
        rw [div_eq_mul_inv]
        ring

theorem spreading_errorParameter (η : ℝ) (hη : 0 < η) :
    0 ≤ η / (2 + η) ∧ η / (2 + η) < 1 ∧
      (1 + η / (2 + η)) / (1 - η / (2 + η)) = 1 + η := by
  have hden : 0 < 2 + η := by linarith
  have hδ0 : 0 ≤ η / (2 + η) := div_nonneg hη.le hden.le
  have hδ1 : η / (2 + η) < 1 := (div_lt_one hden).mpr (by linarith)
  have hd : 0 < 1 - η / (2 + η) := sub_pos.mpr hδ1
  refine ⟨hδ0, hδ1, ?_⟩
  apply (div_eq_iff hd.ne').mpr
  have hcancel : η / (2 + η) * (2 + η) = η := div_mul_cancel₀ η hden.ne'
  nlinarith

theorem exists_spreading_normalizedMap (p : Seminorm ℝ E) (S : E →ₗ[ℝ] Y)
    (η : ℝ) (hη : 0 < η)
    (happrox : ∀ x, |‖S x‖ - p x| ≤ (η / (2 + η)) * p x) :
    ∃ T : E →ₗ[ℝ] Y, ∀ x, p x ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + η) * p x := by
  obtain ⟨hδ0, hδ1, hratio⟩ := spreading_errorParameter η hη
  refine ⟨spreadingRescale (η / (2 + η)) S, ?_⟩
  intro x
  simpa only [hratio] using
    spreadingRescale_bounds p S (η / (2 + η)) hδ0 hδ1 happrox x

end MarkovSuperreflexivity

end

end OAI
