import OAI.MeasureTheory.Falconer.Geometry.CommonProjectionConfiguration

namespace OAI

/-! A single weak constant controls every loss from selecting the common
projection bases and restricting to their intersection. -/
namespace Falconer

 theorem common_projection_losses {W : ℝ} (hW : 1 ≤ W) :
    let ρ := W⁻¹
    let Z := 64*W^6
    0 < ρ ∧ ρ ≤ 1 ∧ 1 ≤ Z ∧ W ≤ Z ∧ W*(8/ρ^4) ≤ Z ∧
      64/ρ^6 = Z ∧ 0 < ρ^4/8 ∧ (ρ^4/8)⁻¹ ≤ Z := by
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hρ : 0 < W⁻¹ := inv_pos.mpr hWpos
  have hρ1 : W⁻¹ ≤ 1 := (inv_le_one₀ hWpos).2 hW
  have h6 : 1 ≤ W^6 := one_le_pow₀ hW
  have hW6 : W ≤ W^6 := by simpa only [pow_one] using pow_le_pow_right₀ hW (show 1 ≤ (6:ℕ) by omega)
  have hW5 : W^5 ≤ W^6 := pow_le_pow_right₀ hW (by omega)
  have hW4 : W^4 ≤ W^6 := pow_le_pow_right₀ hW (by omega)
  have he4 : 8/(W⁻¹)^4 = 8*W^4 := by field_simp
  have he6 : 64/(W⁻¹)^6 = 64*W^6 := by field_simp
  have hei : ((W⁻¹)^4/8)⁻¹ = 8*W^4 := by field_simp
  refine ⟨hρ,hρ1,by nlinarith,by nlinarith,?_,he6,by positivity,?_⟩
  · rw [he4]
    have he : W*(8*W^4) = 8*W^5 := by ring
    rw [he]
    nlinarith
  · rw [hei]
    nlinarith

 theorem common_projection_direction_count {ρ : ℝ} (hρ : 0 < ρ)
    (I J : Finset ℝ) (hcount : (ρ^6/64)*(I.card:ℝ) ≤ (J.card:ℝ)) :
    (I.card:ℝ) ≤ (64/ρ^6)*(J.card:ℝ) := by
  have hh := mul_le_mul_of_nonneg_left hcount (show 0 ≤ 64/ρ^6 by positivity)
  have he : (64/ρ^6)*((ρ^6/64)*(I.card:ℝ)) = (I.card:ℝ) := by field_simp
  rwa [he] at hh

end Falconer

end OAI
