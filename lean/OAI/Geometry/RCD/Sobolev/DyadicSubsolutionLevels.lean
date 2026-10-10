import OAI.Geometry.RCD.Coordinates.NormalizedLevelAlgebra

namespace OAI

/-! # A middle level for the potential term in the dyadic iteration -/

namespace RegularPointCoordinates

theorem dyadic_middle_level_bounds {R : ℝ} (hR : 0 < R) (i : ℕ) :
    let j := 1-(2^i:ℝ)⁻¹
    let h := 1-(2^(i+1):ℝ)⁻¹
    let k := (j+h)/2
    j < k ∧ k < h ∧ (h-k)⁻¹^2 = 16*4^i ∧ k/(k-j) ≤ 4*4^i := by
  dsimp only
  have hh := dyadic_level_gap_bounds hR i
  have hp : (0:ℝ) < 2^i := by positivity
  have hge : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
  have hgap : (1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹) = 1/(2*2^i) := by
    rw [pow_succ]
    field_simp
    ring
  have hhalf : (1-(2^(i+1):ℝ)⁻¹)-((1-(2^i:ℝ)⁻¹)+(1-(2^(i+1):ℝ)⁻¹))/2 = 1/(4*2^i) := by
    calc
      _ = ((1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹))/2 := by ring
      _ = (1/(2*2^i))/2 := by rw [hgap]
      _ = _ := by ring
  have hhalf' : ((1-(2^i:ℝ)⁻¹)+(1-(2^(i+1):ℝ)⁻¹))/2-(1-(2^i:ℝ)⁻¹) = 1/(4*2^i) := by
    linarith only [hhalf]
  refine ⟨by linarith [hh.2.1],by linarith [hh.2.1],?_,?_⟩
  · rw [hhalf]
    have hf : (4:ℝ)^i = (2^i:ℝ)^2 := by rw [show (4:ℝ) = 2*2 by norm_num,mul_pow,pow_two]
    rw [hf]
    field_simp
    ring
  · rw [hhalf']
    have hk1 : ((1-(2^i:ℝ)⁻¹)+(1-(2^(i+1):ℝ)⁻¹))/2 ≤ 1 := by
      have h0 : 0 ≤ (2^(i+1):ℝ)⁻¹ := by positivity
      have h1 : 0 ≤ (2^i:ℝ)⁻¹ := by positivity
      linarith
    calc
      _ ≤ 1/(1/(4*2^i)) := div_le_div_of_nonneg_right hk1 (by positivity)
      _ = 4*(2^i:ℝ) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
        (by norm_num : (2:ℝ) ≤ 4) i) (by norm_num)

end RegularPointCoordinates

end OAI
