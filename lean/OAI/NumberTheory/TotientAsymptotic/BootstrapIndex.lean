import OAI.NumberTheory.TotientAsymptotic.BootstrapPointwise

namespace OAI

/-! A concrete strictly smaller dyadic index for the counting bootstrap. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def bootstrapIndex (J : ℕ) : ℕ := ⌊(J:ℝ)^(41/50:ℝ)⌋₊

lemma bootstrap_index_bounds : ∀ᶠ J : ℕ in atTop,
    1 ≤ bootstrapIndex J ∧ bootstrapIndex J < J ∧
    Real.log (bootstrapIndex J:ℝ) ≤ (41/50:ℝ)*Real.log J ∧
    Real.exp ((Real.log ((2:ℝ)^J))^(81/100:ℝ)) ≤ (2:ℝ)^(bootstrapIndex J) := by
  have ht : Tendsto (fun J : ℕ => (J:ℝ)^(1/100:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (3:ℝ)),eventually_ge_atTop (2:ℕ)] with J hJp hJ
  have hJ1 : (1:ℝ) < J := by exact_mod_cast (show 1 < J by omega)
  have hJ0 : (0:ℝ) < J := by linarith
  have h9 : 1 ≤ (J:ℝ)^(81/100:ℝ) := Real.one_le_rpow hJ1.le (by norm_num)
  have hprod : (J:ℝ)^(81/100:ℝ)*(J:ℝ)^(1/100:ℝ)=(J:ℝ)^(41/50:ℝ) := by
    rw [← Real.rpow_add hJ0]
    norm_num
  have h3 : 3*(J:ℝ)^(81/100:ℝ) ≤ (J:ℝ)^(41/50:ℝ) := by
    rw [← hprod]
    nlinarith only [mul_le_mul_of_nonneg_left hJp (by positivity : 0 ≤ (J:ℝ)^(81/100:ℝ))]
  have hKlo : 2*(J:ℝ)^(81/100:ℝ) ≤ (bootstrapIndex J:ℝ) := by
    have hf := Nat.sub_one_lt_floor ((J:ℝ)^(41/50:ℝ))
    change (J:ℝ)^(41/50:ℝ)-1 < (bootstrapIndex J:ℝ) at hf
    linarith
  have hK1 : 1 ≤ bootstrapIndex J := by
    have hh : (1:ℝ) ≤ bootstrapIndex J := by linarith
    exact_mod_cast hh
  have hK0 : (0:ℝ) < bootstrapIndex J := by exact_mod_cast (show 0 < bootstrapIndex J by omega)
  have hKhi : (bootstrapIndex J:ℝ) ≤ (J:ℝ)^(41/50:ℝ) := Nat.floor_le (by positivity)
  have hKlt : bootstrapIndex J < J := by
    have hh : (J:ℝ)^(41/50:ℝ) < J := by
      calc
        _ < (J:ℝ)^(1:ℝ) := Real.rpow_lt_rpow_of_exponent_lt hJ1 (by norm_num)
        _ = _ := Real.rpow_one _
    exact_mod_cast hKhi.trans_lt hh
  refine ⟨hK1,hKlt,?_,?_⟩
  · have hh := Real.log_le_log hK0 hKhi
    rwa [Real.log_rpow hJ0] at hh
  · have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog21 : Real.log (2:ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hlog : Real.log ((2:ℝ)^J) ≤ J := by
      rw [Real.log_pow]
      nlinarith only [mul_le_mul_of_nonneg_left hlog21 hJ0.le]
    have hpow : (Real.log ((2:ℝ)^J))^(81/100:ℝ) ≤ (J:ℝ)^(81/100:ℝ) :=
      Real.rpow_le_rpow (Real.log_nonneg (one_le_pow₀ (by norm_num))) hlog (by norm_num)
    have hb : (Real.log ((2:ℝ)^J))^(81/100:ℝ) ≤ (bootstrapIndex J:ℝ)*Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlog2 hK0.le]
    calc
      _ ≤ Real.exp ((bootstrapIndex J:ℝ)*Real.log 2) := Real.exp_le_exp.mpr hb
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]

end TotientAsymptotic

end

end OAI
