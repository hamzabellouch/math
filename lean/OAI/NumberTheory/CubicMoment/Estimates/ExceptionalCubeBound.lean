import OAI.NumberTheory.CubicMoment.Estimates.ExceptionalBenchmark

namespace OAI

/-! An exceptional conductor forces the actual cube factor to be small
when the full frequency has norm at most Y^(1+η). -/
noncomputable section
namespace CubicFirstMoment

lemma cube_factor_exceptional_bound {Y p q δ η σ x : ℝ}
    (hY : 1 ≤ Y) (hx : 0 ≤ x) (hsize : η+3*δ ≤ 3*σ)
    (hconductor : 1-3*δ ≤ p+2*q)
    (hfrequency : x^3*(Y^p*(Y^q)^2) ≤ Y^(1+η)) : x ≤ Y^σ := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hσ : (Y^σ)^3 = Y^(3*σ) := by
    rw [← Real.rpow_natCast (Y^σ) 3,← Real.rpow_mul hYp.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hq : (Y^q)^2 = Y^(2*q) := by
    rw [← Real.rpow_natCast (Y^q) 2,← Real.rpow_mul hYp.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have heq : (Y^σ)^3*(Y^p*(Y^q)^2) = Y^(3*σ+p+2*q) := by
    rw [hσ,hq,← Real.rpow_add hYp,← Real.rpow_add hYp]
    congr 1
    ring
  have hbound : Y^(1+η) ≤ (Y^σ)^3*(Y^p*(Y^q)^2) := by
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  have hprod : 0 < Y^p*(Y^q)^2 := mul_pos (Real.rpow_pos_of_pos hYp _)
    (sq_pos_of_pos (Real.rpow_pos_of_pos hYp _))
  have hcube : x^3 ≤ (Y^σ)^3 := (mul_le_mul_iff_left₀ hprod).mp
    (by simpa only [mul_comm] using hfrequency.trans hbound)
  exact (pow_le_pow_iff_left₀ hx (Real.rpow_nonneg hYp.le _) (by norm_num : (3:ℕ) ≠ 0)).mp hcube

lemma moment_constant_saving_mono {A B C D ν μ : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hCD : C ≤ D) (hB : 1 ≤ B) (hμν : μ ≤ ν) :
    C*A*B^(-ν) ≤ D*A*B^(-μ) := by
  exact mul_le_mul (mul_le_mul_of_nonneg_right hCD hA)
    (Real.rpow_le_rpow_of_exponent_le hB (by linarith))
    (Real.rpow_nonneg (by linarith) _) (mul_nonneg (hC.trans hCD) hA)

end CubicFirstMoment

end

end OAI
