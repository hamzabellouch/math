import OAI.Probability.RadialTransition.KacVariational

namespace OAI

noncomputable section
open Set
namespace RadialTransition

lemma sqrt_grid_exists {R₀ R W : ℝ} (hR₀ : 2 ≤ R₀) (hW : 0 ≤ W)
    (hrange : 16*(W+1)^2*R₀ ≤ R) :
    ∃ q : ℕ, 0 < q ∧ 1 ≤ (q:ℝ)/4 ∧ (q:ℝ)/4 ≤ R ∧
      R₀/((q:ℝ)/4) ≤ 2*Real.sqrt (R₀/R) ∧
      (q:ℝ)/R ≤ 4*Real.sqrt (R₀/R) ∧ W*(q:ℝ)/R ≤ 1 := by
  have hW1 : 0 < W+1 := by linarith
  have hfactor : 1 ≤ 16*(W+1)^2 := by nlinarith [sq_nonneg W]
  have hRge : R₀ ≤ R := (le_mul_of_one_le_left (by linarith : 0 ≤ R₀) hfactor).trans hrange
  have hR : 0 < R := by linarith
  let z := Real.sqrt (R₀/R)
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z^2 = R₀/R := Real.sq_sqrt (div_nonneg (by linarith) hR.le)
  have hzR : z^2*R = R₀ := by rw [hzsq]; field_simp
  have hz1 : z ≤ 1 := by
    have hh : z^2 ≤ 1 := by rw [hzsq]; exact (div_le_one hR).mpr hRge
    nlinarith
  have hwz : 4*(W+1)*z ≤ 1 := by
    have hh : 16*(W+1)^2*z^2 ≤ 1 := by
      apply (mul_le_mul_iff_left₀ hR).mp
      nlinarith [hrange]
    nlinarith [mul_nonneg hW1.le hz, sq_nonneg (4*(W+1)*z)]
  let x := Real.sqrt (R₀*R)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hxsq : x^2 = R₀*R := Real.sq_sqrt (mul_nonneg (by linarith) hR.le)
  have hx2 : 2 ≤ x := by nlinarith
  have hxR : x ≤ R := by nlinarith [mul_le_mul_of_nonneg_right hRge hR.le]
  have hxz : x = R*z := by nlinarith [sq_nonneg (x-R*z)]
  let q := ⌊4*x⌋₊
  have hqle : (q:ℝ) ≤ 4*x := Nat.floor_le (by positivity)
  have hqgt : 4*x < (q:ℝ)+1 := Nat.lt_floor_add_one (4*x)
  have hq1 : 1 ≤ (q:ℝ)/4 := by linarith
  have hq : 0 < q := by exact_mod_cast (show (0:ℝ) < q by linarith)
  have hqx : x/2 ≤ (q:ℝ)/4 := by linarith
  have hq0 : 0 < (q:ℝ)/4 := by linarith
  refine ⟨q, hq, hq1, ?_, ?_, ?_, ?_⟩
  · linarith
  · apply (div_le_iff₀ hq0).mpr
    have hh := mul_le_mul_of_nonneg_left hqx (show 0 ≤ 2*z by positivity)
    nlinarith
  · apply (div_le_iff₀ hR).mpr
    nlinarith
  · apply (div_le_iff₀ hR).mpr
    have hh := mul_le_mul_of_nonneg_left hqle hW
    have hh' := mul_le_mul_of_nonneg_left hwz hR.le
    nlinarith [mul_nonneg hR.le hz]

end RadialTransition
end

end OAI
