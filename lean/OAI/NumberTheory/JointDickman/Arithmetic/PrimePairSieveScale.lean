import OAI.NumberTheory.JointDickman.Arithmetic.PrimePairSieveProduct

namespace OAI

/-! # Choosing the finite sieve cutoff for prime pairs -/
namespace JointDickman
open Filter
open scoped Topology

theorem primePair_sieve_scale : ∀ᶠ X : ℝ in atTop, ∃ Z : ℕ,
    3 ≤ Z ∧ Real.log X/8 ≤ Real.log Z ∧
      2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) ≤ X/(Real.log X)^2 := by
  have hpower := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).eventually_ge_atTop 4
  have hsmall := (log_power_div_power_tendsto_zero 2 (by norm_num : (0:ℝ) < 1/4)).const_mul 6
  simp only [mul_zero] at hsmall
  filter_upwards [hpower,Real.tendsto_log_atTop.eventually_ge_atTop (8*Real.log 2),
    hsmall.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)),eventually_ge_atTop (2:ℝ)]
    with X hp hl he hX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  let Z : ℕ := ⌊X^(1/4:ℝ)⌋₊
  have hZle : (Z:ℝ) ≤ X^(1/4:ℝ) := Nat.floor_le (by positivity)
  have hZlt : X^(1/4:ℝ) < (Z:ℝ)+1 := Nat.lt_floor_add_one _
  have hZ3 : 3 ≤ Z := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ X^(1/4:ℝ))).mpr
    norm_num
    linarith
  have hZhalf : X^(1/4:ℝ)/2 ≤ (Z:ℝ) := by linarith
  have hlogZ : Real.log X/8 ≤ Real.log Z := by
    have hh := Real.log_le_log (by positivity : 0 < X^(1/4:ℝ)/2) hZhalf
    rw [Real.log_div (by positivity) (by norm_num),Real.log_rpow hX0] at hh
    linarith
  refine ⟨Z,hZ3,hlogZ,?_⟩
  have hpow3 : (X^(1/4:ℝ))^3 = X^(3/4:ℝ) := by
    rw [←Real.rpow_mul_natCast hX0.le]
    norm_num
  have hpowle : X^(1/4:ℝ) ≤ X^(3/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hpoly : 2*(Z+1:ℝ)*(Z:ℝ)^2+(Z+1:ℝ) ≤ 6*X^(3/4:ℝ) := by
    have hZ0 : (0:ℝ) ≤ Z := Nat.cast_nonneg _
    have hh : (Z:ℝ)+1 ≤ 2*X^(1/4:ℝ) := by linarith
    calc
      _ ≤ 2*(2*X^(1/4:ℝ))*(X^(1/4:ℝ))^2+2*X^(1/4:ℝ) := by gcongr
      _ = 4*X^(3/4:ℝ)+2*X^(1/4:ℝ) := by rw [←hpow3]; ring
      _ ≤ _ := by linarith
  have he' : 6*(Real.log X)^2 ≤ X^(1/4:ℝ) := by
    apply (div_le_one (by positivity : 0 < X^(1/4:ℝ))).mp
    simpa only [Real.rpow_two,mul_div_assoc] using he
  have hmul : X^(1/4:ℝ)*X^(3/4:ℝ) = X := by rw [←Real.rpow_add hX0]; norm_num
  apply hpoly.trans
  apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
  have hh := mul_le_mul_of_nonneg_right he' (Real.rpow_nonneg hX0.le (3/4))
  rw [hmul] at hh
  nlinarith

end JointDickman

end OAI
