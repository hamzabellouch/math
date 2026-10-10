import OAI.NumberTheory.CubicMoment.Estimates.UniformCoreBlockMoment

namespace OAI

/-! Elementary eventual scales for restoring the actual common factors. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma stopped_common_cutoff {b : ℝ} (hb : (2:ℝ)^24 ≤ b) :
    65536*(b/2)^(1/4:ℝ) ≤ b := by
  have hb1 : 1 ≤ b := (by norm_num : (1:ℝ) ≤ 2^24).trans hb
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have he : ((2:ℝ)^24)^(3/4:ℝ) = (2:ℝ)^18 := by
    rw [←Real.rpow_natCast (2:ℝ) 24,←Real.rpow_mul (by norm_num)]
    norm_num
  have hpow : (65536:ℝ) ≤ b^(3/4:ℝ) := by
    calc
      _ ≤ (2:ℝ)^18 := by norm_num
      _ = ((2:ℝ)^24)^(3/4:ℝ) := he.symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hb (by norm_num)
  calc
    _ ≤ b^(3/4:ℝ)*b^(1/4:ℝ) := mul_le_mul hpow
      (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)) (by positivity) (by positivity)
    _ = b := by rw [←Real.rpow_add hbp]; norm_num

lemma stopped_common_eventual_scales {κ : ℝ} (hκ : 0 < κ) (k : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ b : ℝ, X^κ ≤ b →
      2 < b ∧ 65536*(b/2)^(1/4:ℝ) ≤ b ∧
        b^(-(1/32:ℝ)) ≤ 1/(Real.log X)^k := by
  filter_upwards [(tendsto_rpow_atTop hκ).eventually_ge_atTop ((2:ℝ)^24),
    negative_power_log_saving (show 0 < κ/32 by positivity) k,
    eventually_ge_atTop (Real.exp 1)] with X hbig hdecay hX
  intro b hb
  have hcut := hbig.trans hb
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL : 0 < Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at hh
    linarith
  refine ⟨lt_of_lt_of_le (by norm_num : (2:ℝ) < 2^24) hcut,stopped_common_cutoff hcut,?_⟩
  have ht := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXp κ) hb
    (show -(1/32:ℝ) ≤ 0 by norm_num)
  rw [←Real.rpow_mul hXp.le] at ht
  have he : κ*(-(1/32:ℝ)) = -(κ/32) := by ring
  rw [he] at ht
  exact (ht.trans hdecay).trans (one_div_le_one_div_of_le (pow_pos hL k)
    (pow_le_pow_left₀ hL.le (by linarith) k))

end CubicFirstMoment

end

end OAI
