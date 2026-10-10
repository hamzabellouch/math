import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.InitialCharacterScale
open Filter

def bulkCountCost (ρ : ℝ) : ℝ := 2*|Real.log (3/ρ)|+1

theorem tuple_count_bound_eventually {ρ : ℝ} (hρ : 0 < ρ) (k R : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ r : ℕ, r ≤ R →
      (1/(ρ*L))^(2*wordSize k L)*((2*wordSize k L+r : ℕ) : ℝ)^(2*wordSize k L+r) ≤
        Real.exp ((bulkCountCost ρ+2*Real.log (depthScale k))*(wordSize k L : ℝ)) := by
  filter_upwards [fixed_power_eventually k R, (wordSize_tendsto k).eventually_ge_atTop (R : ℝ),
    (wordSize_tendsto k).eventually_ge_atTop 1, eventually_ge_atTop (1 : ℝ)]
    with L hpow hmR hm1 hL
  intro r hr
  let m := wordSize k L
  have hLpos : 0 < L := by linarith
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hupper : (m : ℝ) ≤ depthScale k*L := (wordSize_bounds k hLpos.le).2
  have hnle : ((2*m+r : ℕ) : ℝ) ≤ 3*(m : ℝ) := by
    have hr' : (r : ℝ) ≤ R := by exact_mod_cast hr
    push_cast
    change (R : ℝ) ≤ m at hmR
    linarith
  have hbase : (1/(ρ*L))*(3*(m : ℝ)) ≤ (3/ρ)*depthScale k := by
    have he : (1/(ρ*L))*(3*(m : ℝ)) = (3*(m : ℝ))/(ρ*L) := by ring
    rw [he]
    apply (div_le_iff₀ (mul_pos hρ hLpos)).mpr
    have hid : (3/ρ)*depthScale k*(ρ*L)=3*(depthScale k*L) := by field_simp
    rw [hid]
    linarith
  have hbaseexp : (1/(ρ*L))*(3*(m : ℝ)) ≤
      Real.exp (|Real.log (3/ρ)|+Real.log (depthScale k)) := by
    apply hbase.trans
    rw [Real.exp_add, Real.exp_log (depthScale_pos k)]
    apply mul_le_mul_of_nonneg_right _ (depthScale_pos k).le
    calc
      3/ρ = Real.exp (Real.log (3/ρ)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_abs_self _)
  have hpoly : (3*(m : ℝ))^r ≤ Real.exp (m : ℝ) := by
    apply le_trans _ hpow
    exact pow_le_pow_right₀ (by change 1 ≤ (wordSize k L : ℝ) at hm1; linarith) hr
  calc
    _ ≤ (1/(ρ*L))^(2*m)*(3*(m : ℝ))^(2*m+r) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hnle _) (by positivity)
    _ = ((1/(ρ*L))*(3*(m : ℝ)))^(2*m)*(3*(m : ℝ))^r := by
      rw [pow_add, mul_pow]
      ring
    _ ≤ (Real.exp (|Real.log (3/ρ)|+Real.log (depthScale k)))^(2*m)*Real.exp (m : ℝ) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hbaseexp _) hpoly (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      dsimp only [bulkCountCost, m]
      push_cast
      ring

end Ostmann.Characters.InitialCharacterScale

end

end OAI
