import OAI.NumberTheory.CubicMoment.Estimates.ModelOverlapBound
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! Elementary powers and logarithmic absorption for model overlap. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma negative_sixth_square_scale {x : ℝ} (hx : 0 < x) :
    (x^(-1/6:ℝ))^2*x*x = x^(5/3:ℝ) := by
  calc
    _ = (x^(-1/6:ℝ))^2*x^2 := by ring
    _ = _ := by
      rw [←Real.rpow_natCast (x^(-1/6:ℝ)) 2,←Real.rpow_mul hx.le,
        ←Real.rpow_natCast x 2,←Real.rpow_add hx]
      norm_num

lemma model_overlap_scale {A L : ℝ} (hA : 0 < A) (hL : 0 < L)
    (M Q C₁ C₂ n z D : ℝ) (d a : ℕ) :
    (cStar*A^(-1/6:ℝ)*L^(-1/6:ℝ))^2*
      ((C₁*L*(M*A*z^d))*(n*(18*(Q*A)/D)*(C₂*L*z^a))) =
      (cStar^2*C₁*n*18*Q*C₂)*M*A^(5/3:ℝ)*L^(5/3:ℝ)*z^(d+a)/D := by
  calc
    _ = (cStar^2*C₁*n*18*Q*C₂)*M*
        ((A^(-1/6:ℝ))^2*A*A)*((L^(-1/6:ℝ))^2*L*L)*z^(d+a)/D := by
      rw [pow_add]
      ring
    _ = _ := by rw [negative_sixth_square_scale hA,negative_sixth_square_scale hL]

lemma norm_le_bilinear_of_square {x : ℂ} {C A L z : ℝ}
    (hC : 0 ≤ C) (hA : 0 < A) (hL : 0 < L) (hz : 0 < z) (k : ℕ)
    (h : ‖x‖^2 ≤ C*A^(5/3:ℝ)*L^(5/3:ℝ)/z^(2*k)) :
    ‖x‖ ≤ Real.sqrt C*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k := by
  have hp (t : ℝ) (ht : 0 < t) : (t^(5/6:ℝ))^2 = t^(5/3:ℝ) := by
    rw [←Real.rpow_natCast (t^(5/6:ℝ)) 2,←Real.rpow_mul ht.le]
    norm_num
  have he : (Real.sqrt C*A^(5/6:ℝ)*L^(5/6:ℝ)/z^k)^2 =
      C*A^(5/3:ℝ)*L^(5/3:ℝ)/z^(2*k) := by
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hC,hp A hA,hp L hL]
    simp only [←pow_mul,Nat.mul_comm]
  rw [←he] at h
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mp h

lemma overlap_power_log_saving {c : ℝ} (hc : 0 < c) (a k : ℕ) :
    ∀ᶠ L : ℝ in atTop, (1+Real.log L)^a/L^c ≤ 1/(1+Real.log L)^(2*k) := by
  filter_upwards [negative_power_log_saving hc (a+2*k),eventually_ge_atTop (1:ℝ)] with L h hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log L := by linarith [Real.log_nonneg hL]
  calc
    _ = (1+Real.log L)^a*L^(-c) := by rw [Real.rpow_neg hLp.le]; ring
    _ ≤ (1+Real.log L)^a*(1/(1+Real.log L)^(a+2*k)) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hz.le _)
    _ = _ := by rw [pow_add]; field_simp

end CubicFirstMoment

end

end OAI
