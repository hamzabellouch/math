import OAI.Geometry.RCD.Coordinates.NormalizedLevelAlgebra

namespace OAI

/-! # Dyadic space-time cutoffs for the heat level iteration -/

noncomputable section
namespace RegularPointCoordinates

def parabolicDyadicTime (τ R : ℝ) (i : ℕ) : ℝ :=
  τ+R^2/4*(1-(2^i:ℝ)⁻¹)

theorem parabolicDyadicTime_bounds {τ R : ℝ} (hR : 0 < R) (i : ℕ) :
    τ ≤ parabolicDyadicTime τ R i ∧
    parabolicDyadicTime τ R i < parabolicDyadicTime τ R (i+1) ∧
    parabolicDyadicTime τ R (i+1) < τ+R^2 ∧
    parabolicDyadicTime τ R i ≤ τ+R^2/4 := by
  have hk := dyadic_level_gap_bounds hR i
  have hRp : 0 < R^2/4 := by positivity
  have hn : 0 ≤ (2^(i+1):ℝ)⁻¹ := by positivity
  have hn' : 0 ≤ (2^i:ℝ)⁻¹ := by positivity
  dsimp only [parabolicDyadicTime]
  refine ⟨by nlinarith only [hk.1,hRp],by nlinarith only [hk.2.1,hRp],?_,?_⟩
  · nlinarith only [mul_nonneg hRp.le hn,hRp]
  · nlinarith only [mul_nonneg hRp.le hn']

theorem parabolic_dyadic_coefficient {τ R : ℝ} (hR : 0 < R) (i : ℕ) :
    let Q := (parabolicDyadicTime τ R (i+1)-parabolicDyadicTime τ R i)⁻¹+
      5*(((R/2+R/(4*2^i))-(R/2+R/(4*2^(i+1))))⁻¹)^2
    R^2*Q ≤ 328*4^i ∧ 2*R^2*Q+1 ≤ 657*4^i ∧
      R^2*Q*(((1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹))⁻¹)^2 ≤ 1312*16^i := by
  intro Q
  have hp : (0:ℝ) < 2^i := by positivity
  have hn : (2^i:ℝ) ≠ 0 := hp.ne'
  have hf : (4:ℝ)^i = (2^i:ℝ)^2 := by
    rw [show (4:ℝ) = 2*2 by norm_num,mul_pow,pow_two]
  have hr : (R/2+R/(4*2^i))-(R/2+R/(4*2^(i+1))) = R/(8*2^i) := by
    rw [pow_succ]
    field_simp
    ring
  have ht : parabolicDyadicTime τ R (i+1)-parabolicDyadicTime τ R i = R^2/(8*2^i) := by
    simp only [parabolicDyadicTime,pow_succ]
    field_simp
    ring
  have heq : R^2*Q = 8*2^i+320*4^i := by
    dsimp only [Q]
    rw [hr,ht,hf]
    field_simp
    ring
  have h24 : (2:ℝ)^i ≤ 4^i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
  have h4 : (1:ℝ) ≤ 4^i := one_le_pow₀ (by norm_num)
  have hQ : R^2*Q ≤ 328*4^i := by rw [heq]; nlinarith only [h24]
  refine ⟨hQ,by nlinarith only [hQ,h4],?_⟩
  rw [(dyadic_level_gap_bounds hR i).2.2.1]
  have hh := mul_le_mul_of_nonneg_right hQ (by positivity : (0:ℝ)≤4*4^i)
  have h16 : (16:ℝ)^i = 4^i*4^i := by rw [← mul_pow]; norm_num
  rw [h16]
  nlinarith only [hh]

theorem parabolic_normalized_identity {W V J C d a b c α : ℝ}
    (hW : 0 < W) (hV : 0 < V) (hJ : 0 ≤ J)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hα : 0 < α) (i : ℕ) :
    (C*V^(-α)*(d*b^i)*J*((a*c^i/W)*J)^α)/(W*V) =
      (C*d*a^α)*(b*c^α)^i*(J/(W*V))^(1+α) := by
  by_cases hJ0 : J = 0
  · simp only [hJ0,mul_zero,zero_div,Real.zero_rpow hα.ne',
      Real.zero_rpow (by linarith : 1+α≠0)]
  have hJp : 0 < J := lt_of_le_of_ne hJ (Ne.symm hJ0)
  have hr : ((a*c^i/W)*J)^α = a^α*(c^α)^i*J^α/W^α := by
    rw [show (a*c^i/W)*J = (a*c^i*J)/W by ring,
      Real.div_rpow (by positivity) hW.le,
      Real.mul_rpow (by positivity) hJ,
      Real.mul_rpow ha.le (pow_nonneg hc.le _),← Real.rpow_pow_comm hc.le]
  rw [hr,Real.rpow_add (div_pos hJp (mul_pos hW hV)),Real.rpow_one,
    Real.div_rpow hJ (mul_pos hW hV).le,Real.mul_rpow hW.le hV.le,
    Real.rpow_neg hV.le,mul_pow]
  field_simp

end RegularPointCoordinates

end

end OAI
