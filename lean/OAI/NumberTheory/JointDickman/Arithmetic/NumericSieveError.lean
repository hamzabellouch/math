import OAI.NumberTheory.JointDickman.Amplification.NumericAdditionBound

namespace OAI

/-! # Negligibility of the large-addition sieve remainder -/

namespace JointDickman
open Filter
open scoped Topology

/-- At separated powers, the explicit polynomial sieve remainder is
smaller than every fixed power of B, uniformly in the allowed lag. -/
theorem numeric_sieve_scaled_error_tendsto {g a : ℝ} (ha : 0 < a) (hga : g < a) (D : ℝ) :
    Tendsto (fun B : ℝ => 32*B^(D+2)*Real.exp (3*B^g-B^a)) atTop (𝓝 0) := by
  have hp := (power_div_power_tendsto_zero hga).const_mul 3
  have hl := (log_power_div_power_tendsto_zero 1 ha).const_mul (D+2)
  have hc := (power_div_power_tendsto_zero ha).const_mul (Real.log 32)
  have hq : Tendsto (fun B : ℝ =>
      3*(B^g/B^a)-1+(D+2)*(Real.log B/B^a)+Real.log 32/B^a) atTop (𝓝 (-1)) := by
    simpa only [Real.rpow_one,Real.rpow_zero,one_div,mul_zero,zero_sub,sub_zero,
      add_zero,mul_one,mul_inv_rev,div_eq_mul_inv,one_mul] using ((hp.sub_const 1).add hl).add hc
  have he := hq.neg_mul_atTop (by norm_num : (-1 : ℝ) < 0) (tendsto_rpow_atTop ha)
  have hlim := Real.tendsto_exp_atBot.comp he
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  dsimp
  have hBa := (Real.rpow_pos_of_pos hB a).ne'
  have hident : (3*(B^g/B^a)-1+(D+2)*(Real.log B/B^a)+Real.log 32/B^a)*B^a =
      Real.log 32+(D+2)*Real.log B+(3*B^g-B^a) := by field_simp; ring
  rw [hident,Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 32)]
  simp only [Real.rpow_def_of_pos hB]
  congr 2
  congr 1
  ring

theorem numeric_sieve_remainder_small {g a : ℝ} (ha : 0 < a) (hga : g < a) (D : ℝ) :
    ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (W : ℝ), 0 < j → (j : ℝ) ≤ (B : ℝ)^2 →
      Real.exp ((B : ℝ)^a)/4 ≤ W →
      4*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W ≤
        (B : ℝ)^(-D)/(j : ℝ) := by
  have hlim := (numeric_sieve_scaled_error_tendsto ha hga D).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with B hsmall hB
  intro j W hj hjB hW
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hW0 : 0 < W := (by positivity : 0 < Real.exp ((B : ℝ)^a)/4).trans_le hW
  let E := Real.exp ((B : ℝ)^g)
  have hE1 : 1 ≤ E := Real.one_le_exp_iff.mpr (Real.rpow_nonneg hB0.le _)
  have hZ : (numericAdditionSieveCutoff B g : ℝ) ≤ E := Nat.floor_le (Real.exp_pos _).le
  have herr : 4*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W ≤
      32*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a) := by
    calc
      _ ≤ (4*(2*E)*E^2)/(Real.exp ((B : ℝ)^a)/4) := by
        apply div_le_div₀ (by positivity) _ (by positivity) hW
        gcongr
        linarith only [hZ,hE1]
      _ = _ := by
        dsimp only [E]
        rw [Real.exp_sub,show (3 : ℝ)*(B : ℝ)^g = (B : ℝ)^g+2*(B : ℝ)^g by ring,
          Real.exp_add,show Real.exp (2*(B : ℝ)^g) = Real.exp ((B : ℝ)^g)^2 by
            simpa only [Nat.cast_ofNat] using Real.exp_nat_mul ((B : ℝ)^g) 2]
        ring
  have hpow : (B : ℝ)^(D+2) = (B : ℝ)^D*(B : ℝ)^2 := by
    rw [Real.rpow_add hB0,Real.rpow_two]
  have hepos : 0 ≤ 32*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a) := by positivity
  have hmul : (32*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a))*(j : ℝ)*(B : ℝ)^D ≤ 1 := by
    calc
      _ ≤ (32*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a))*(B : ℝ)^2*(B : ℝ)^D := by gcongr
      _ = 32*(B : ℝ)^(D+2)*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a) := by rw [hpow]; ring
      _ ≤ 1 := hsmall
  have hmain : 32*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a) ≤ (B : ℝ)^(-D)/(j : ℝ) := by
    rw [Real.rpow_neg hB0.le]
    apply (le_div_iff₀ hj0).mpr
    rw [inv_eq_one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hB0 D)).mpr hmul
  exact herr.trans hmain

end JointDickman

end OAI
