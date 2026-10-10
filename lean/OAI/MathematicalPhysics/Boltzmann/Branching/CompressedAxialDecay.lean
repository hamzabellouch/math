import OAI.MathematicalPhysics.Boltzmann.Jets.JetSupersolutions
import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles

namespace OAI

/-! # Uniform axial decay of the compressed core amplitude on bounded scales -/

noncomputable section

open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem S_mul_sq_le_four (x : ℝ) : S x*x^2 ≤ 4 := by
  have hc : |x| ≤ 2*Real.cosh x := by
    have h₁ : |x| ≤ Real.exp |x| :=
      (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)).trans (Real.add_one_le_exp |x|)
    linarith [JetAxialEntropy.cosh_lower x]
  have h := mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr (Real.cosh_pos x).le)
  have hb : |x| * (Real.cosh x)⁻¹ ≤ 2 := by
    simpa only [mul_assoc,mul_inv_cancel₀ (Real.cosh_pos x).ne',mul_one] using h
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ |x| * (Real.cosh x)⁻¹)
    (by norm_num : (0:ℝ) ≤ 2)).mpr hb
  simpa only [mul_pow,sq_abs,S,mul_comm,show (2:ℝ)^2 = 4 by norm_num] using hs

theorem compressed_axial_decay {K α γ μ t M Z ζ : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 < γ) (hμ : 0 < μ)
    (ht : 0 ≤ t) (hM : μ ≤ M) (hZ : 0 < Z) (hζ : Z ≤ |ζ|) :
    compressed K α γ μ t ζ ≤ 4*K*M/(γ^2*Z^2) := by
  have hMpos : 0 < M := hμ.trans_le hM
  have hζ0 : ζ ≠ 0 := abs_pos.mp (hZ.trans_le hζ)
  have hx : 0 < (γ*ζ/μ)^2 := sq_pos_of_ne_zero (div_ne_zero (mul_ne_zero hγ.ne' hζ0) hμ.ne')
  have hs : S (γ*ζ/μ) ≤ 4/(γ*ζ/μ)^2 :=
    (le_div_iff₀ hx).mpr (S_mul_sq_le_four _)
  have hden : μ ≤ μ+t*α*γ*S (γ*ζ/μ) := by
    exact le_add_of_nonneg_right (mul_nonneg
      (mul_nonneg (mul_nonneg ht hα) hγ.le) (S_pos _).le)
  calc
    _ ≤ K*S (γ*ζ/μ)/μ := div_le_div_of_nonneg_left
      (mul_nonneg hK (S_pos _).le) hμ hden
    _ ≤ K*(4/(γ*ζ/μ)^2)/μ := by gcongr
    _ = 4*K*μ/(γ^2*ζ^2) := by field_simp
    _ ≤ 4*K*M/(γ^2*Z^2) := by
      apply div_le_div₀
      · positivity
      · exact mul_le_mul_of_nonneg_left hM (by positivity)
      · positivity
      · exact mul_le_mul_of_nonneg_left
          (by simpa only [sq_abs] using (sq_le_sq₀ hZ.le (abs_nonneg ζ)).mpr hζ) (sq_nonneg γ)

end BoltzmannNonuniqueness.JetCoreDensity

end

end OAI
