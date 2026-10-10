import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticScale

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem positive_frequency_sqrt_normalization {R d s v : ℝ}
    (hR : 0 < R) (hd : 0 < d) (hs : 0 < s) (hv : 0 < v) :
    (Real.sqrt (R*d))⁻¹ = (Real.sqrt s)⁻¹ * (Real.sqrt v)⁻¹ *
      (Real.sqrt (R/(s*v/d)))⁻¹ := by
  rw [Real.sqrt_div hR.le, Real.sqrt_div (mul_pos hs hv).le,
    Real.sqrt_mul hs.le, Real.sqrt_mul hR.le]
  have hd' := (Real.sqrt_pos.mpr hd).ne'
  have hs' := (Real.sqrt_pos.mpr hs).ne'
  have hv' := (Real.sqrt_pos.mpr hv).ne'
  have hR' := (Real.sqrt_pos.mpr hR).ne'
  field_simp

theorem positive_frequency_square_cutoff_le {d s v B : ℕ}
    (hd : 0 < d) (hs : 0 < s) (hv : 0 < v) {R : ℝ} (hR : 0 < R)
    (hB : R*d ≤ (B : ℝ)) :
    ⌊Real.sqrt (R / ((s : ℝ)*v/d))⌋₊ ≤ B := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hBpos : (0 : ℝ) < B := (mul_pos hR hd').trans_le hB
  have hB1 : (1 : ℝ) ≤ B := by
    exact_mod_cast (show 1 ≤ B by exact_mod_cast hBpos)
  have hsv : (1 : ℝ) ≤ (s : ℝ)*v := by exact_mod_cast Nat.mul_pos hs hv
  have hquot : R / ((s : ℝ)*v/d) = R*d/((s : ℝ)*v) := by field_simp
  have hN : Real.sqrt (R / ((s : ℝ)*v/d)) ≤ B := by
    apply (Real.sqrt_le_left hBpos.le).mpr
    rw [hquot]
    apply (div_le_iff₀ (mul_pos hs' hv')).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsv (sq_nonneg (B : ℝ))]
  exact_mod_cast (Nat.floor_le (Real.sqrt_nonneg _)).trans hN

end Ostmann.QuadraticCenter

end

end OAI
