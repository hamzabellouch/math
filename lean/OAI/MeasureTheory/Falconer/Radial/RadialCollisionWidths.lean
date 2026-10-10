import OAI.MeasureTheory.Falconer.Radial.RadialCollisionMass
import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles

namespace OAI

/-! # Fixed-width radial collision tests at nearby dyadic depths -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialCollisionMass_mono (μ : Measure (Space d)) (p : Space d × Space d)
    {δ δ' : ℝ} (h : δ ≤ δ') : radialCollisionMass μ δ p ≤ radialCollisionMass μ δ' p :=
  measure_mono (fun _ hy => hy.trans h)

theorem dyadic_width_rounding (C : ℝ) :
    ∃ J : ℕ, ∀ n : ℕ, J ≤ n → C/(2:ℝ)^n ≤ 1/(2:ℝ)^(n-J) := by
  obtain ⟨J,hJ⟩ := Regularization.fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) C
  have hC : C ≤ (2:ℝ)^J := by simpa only [Real.rpow_one] using hJ J le_rfl
  refine ⟨J,fun n hn => ?_⟩
  have he : 1/(2:ℝ)^(n-J) = (2:ℝ)^J/(2:ℝ)^n := by
    conv_rhs => rw [show n = J+(n-J) by omega,pow_add]
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right hC (by positivity)

theorem radialCollisionMass_fixed_width (μ : Measure (Space d)) (C : ℝ) :
    ∃ J : ℕ, ∀ n : ℕ, J ≤ n → ∀ p : Space d × Space d,
      radialCollisionMass μ (C/(2:ℝ)^n) p ≤ radialCollisionMass μ (1/(2:ℝ)^(n-J)) p := by
  obtain ⟨J,hJ⟩ := dyadic_width_rounding C
  exact ⟨J,fun n hn p => radialCollisionMass_mono μ p (hJ n hn)⟩

end Falconer

end OAI
