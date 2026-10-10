import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleCounting

namespace OAI

noncomputable section
namespace Ostmann.Characters.InitialCharacterScale
open Filter

def gapThreshold (A ρ C H : ℝ) : ℝ := 2*(A+bulkCountCost ρ+C+2*H+4)

theorem repeated_scalar_absorption {ρ C H K A BD : ℝ}
    (hρ : 0 < ρ) (_hC : 0 ≤ C) (hH : 0 ≤ H) (_hK : 0 ≤ K)
    (hBD : gapThreshold A ρ C H ≤ BD) (k R : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ r : ℕ, r ≤ R →
      K*Real.exp (-initialGap BD k L/2)*(1/(ρ*L))^(2*wordSize k L)*
        Real.exp (C*(wordSize k L : ℝ))*
        ((2*wordSize k L+r : ℕ) : ℝ)^(2*wordSize k L+r)*Real.exp (H*L) ≤
      (1/2)*Real.exp (-A*(wordSize k L : ℝ)) := by
  have ht := wordSize_tendsto k
  filter_upwards [tuple_count_bound_eventually hρ k R,
    (Real.tendsto_exp_atTop.comp ht).eventually_ge_atTop K,
    ht.eventually_ge_atTop 1,eventually_ge_atTop (2 : ℝ)] with L hcount hfixed hm1 hL
  intro r hr
  let m := wordSize k L
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (depthScale k) := Real.log_nonneg (one_le_depthScale k)
  have hLm : L ≤ 2*(m : ℝ) := by
    have hf := (wordSize_bounds k (by linarith : 0 ≤ L)).1
    have hz := mul_le_mul_of_nonneg_right (one_le_depthScale k) (by linarith : 0 ≤ L)
    change depthScale k*L-1 < (m : ℝ) at hf
    nlinarith
  calc
    _ = K*Real.exp (-initialGap BD k L/2)*
        ((1/(ρ*L))^(2*m)*((2*m+r : ℕ) : ℝ)^(2*m+r))*
        Real.exp (C*(m : ℝ))*Real.exp (H*L) := by ring
    _ ≤ Real.exp (m : ℝ)*Real.exp (-initialGap BD k L/2)*
        Real.exp ((bulkCountCost ρ+2*Real.log (depthScale k))*(m : ℝ))*
        Real.exp (C*(m : ℝ))*Real.exp ((2*H)*(m : ℝ)) := by
      have hHL : Real.exp (H*L) ≤ Real.exp ((2*H)*(m : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hLm hH])
      have hcount' := hcount r hr
      change K ≤ Real.exp (m : ℝ) at hfixed
      gcongr
    _ ≤ Real.exp (-(A+1)*(m : ℝ)) := by
      repeat rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hBd := mul_le_mul_of_nonneg_right hBD hm
      dsimp only [gapThreshold] at hBd
      unfold initialGap
      change _ ≤ -(A+1)*(wordSize k L : ℝ)
      dsimp [m] at hm hBd ⊢
      nlinarith [mul_nonneg hlog hm]
    _ ≤ _ := by
      have hhalf : Real.exp (-(m : ℝ)) ≤ (1/2 : ℝ) := by
        have hh : (2 : ℝ) ≤ Real.exp (m : ℝ) := by
          have he := Real.add_one_le_exp (m : ℝ)
          change 1 ≤ (m : ℝ) at hm1
          linarith
        simpa only [one_div, ← Real.exp_neg] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hh
      have he : Real.exp (-(A+1)*(m : ℝ)) = Real.exp (-(m : ℝ))*Real.exp (-A*(m : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hhalf (Real.exp_pos _).le

end Ostmann.Characters.InitialCharacterScale

end

end OAI
