import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryCompensationNormalizationBudget
open Filter

def occurrenceCount (l : ℕ) : ℕ := 4*l*2^l

theorem occurrenceCount_mono {l k : ℕ} (hl : l ≤ k) :
    occurrenceCount l ≤ occurrenceCount k := by
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 hl) (Nat.pow_le_pow_right (by norm_num) hl)

theorem pattern_cost_exp (N : ℕ) (L : ℝ) :
    (2:ℝ)^(N*N)*(2:ℝ)^N*(Real.exp L)^N =
      Real.exp (((N:ℝ)^2+N)*Real.log 2+N*L) := by
  conv_lhs => rw [show (2:ℝ)=Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]
  congr 1
  push_cast
  ring

theorem eventually_pattern_normalization_budget {k : ℕ} (hk : 0 < k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ L : ℝ in atTop, ∀l : ℕ, l ≤ k →
      (2:ℝ)^(occurrenceCount l*occurrenceCount l)*(2:ℝ)^occurrenceCount l*
        (max 1 (Real.exp L))^occurrenceCount l ≤
      Real.exp ((8*k/Conclusion.bulkScale k)*(2:ℝ)^l*Conclusion.bulkSize k L+
        ρ*Conclusion.bulkSize k L) := by
  let A : ℝ := (((occurrenceCount k:ℕ):ℝ)^2+occurrenceCount k)*Real.log 2
  have hz : 0 < Conclusion.bulkScale k := by unfold Conclusion.bulkScale; positivity
  filter_upwards [(Conclusion.bulkSize_tendsto_atTop hk).eventually_ge_atTop (A/ρ),
    (Conclusion.bulkSize_tendsto_atTop hk).eventually_ge_atTop 2,
    eventually_ge_atTop (0:ℝ)] with L hA hm hL
  intro l hl
  have hA' : A ≤ ρ*(Conclusion.bulkSize k L:ℝ) := by
    have := (div_le_iff₀ hρ).mp hA
    nlinarith
  have hLm : Conclusion.bulkScale k*L ≤ 2*(Conclusion.bulkSize k L:ℝ) := by
    linarith [(Conclusion.bulkSize_bounds k hL).1]
  have hLdiv : L ≤ 2*(Conclusion.bulkSize k L:ℝ)/Conclusion.bulkScale k :=
    (le_div_iff₀ hz).mpr (by nlinarith)
  have hn : (occurrenceCount l:ℝ) ≤ occurrenceCount k := by
    exact_mod_cast occurrenceCount_mono hl
  have hln : (l:ℝ) ≤ k := by exact_mod_cast hl
  have hn0 : 0 ≤ (occurrenceCount l:ℝ) := by positivity
  have hkn0 : 0 ≤ (occurrenceCount k:ℝ) := by positivity
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfixed : ((occurrenceCount l:ℝ)^2+occurrenceCount l)*Real.log 2 ≤ A := by
    dsimp [A]
    apply mul_le_mul_of_nonneg_right _ hlog
    nlinarith
  have hlinear : (occurrenceCount l:ℝ)*L ≤
      (8*k/Conclusion.bulkScale k)*(2:ℝ)^l*Conclusion.bulkSize k L := by
    calc
      _ ≤ (4*(k:ℝ)*(2:ℝ)^l)*L := by
        simp only [occurrenceCount,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hln (by norm_num)) (by positivity)) hL
      _ ≤ (4*(k:ℝ)*(2:ℝ)^l)*(2*(Conclusion.bulkSize k L:ℝ)/Conclusion.bulkScale k) :=
        mul_le_mul_of_nonneg_left hLdiv (by positivity)
      _ = _ := by ring
  rw [max_eq_right (Real.one_le_exp_iff.mpr hL),pattern_cost_exp]
  apply Real.exp_le_exp.mpr
  linarith

theorem occurrence_coefficient_le_one {k : ℕ} (hk : 2 ≤ k) :
    8*(k:ℝ)/Conclusion.bulkScale k ≤ 1 := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hpow : (8:ℝ) ≤ (k:ℝ)^3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hk' 3
    norm_num at h ⊢
    exact h
  have hz : 0 < Conclusion.bulkScale k := by unfold Conclusion.bulkScale; positivity
  apply (div_le_iff₀ hz).mpr
  simp only [one_mul,Conclusion.bulkScale]
  nlinarith [mul_le_mul_of_nonneg_right hpow (show 0 ≤ (k:ℝ) by positivity)]

theorem eventually_pattern_normalization_universal {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀l : ℕ, l ≤ k →
      (2:ℝ)^(occurrenceCount l*occurrenceCount l)*(2:ℝ)^occurrenceCount l*
        (max 1 (Real.exp L))^occurrenceCount l ≤
      Real.exp (2*(2:ℝ)^l*Conclusion.bulkSize k L) := by
  filter_upwards [eventually_pattern_normalization_budget (by omega : 0 < k)
    (by norm_num : (0:ℝ) < 1)] with L hL
  intro l hl
  apply (hL l hl).trans
  apply Real.exp_le_exp.mpr
  have hr : (1:ℝ) ≤ (2:ℝ)^l := one_le_pow₀ (by norm_num)
  have hc := mul_le_mul_of_nonneg_right (occurrence_coefficient_le_one hk)
    (show 0 ≤ (2:ℝ)^l*(Conclusion.bulkSize k L:ℝ) by positivity)
  have hm := mul_le_mul_of_nonneg_right hr (show 0 ≤ (Conclusion.bulkSize k L:ℝ) by positivity)
  nlinarith

end Ostmann.Arithmetic.HistoryCompensationNormalizationBudget

end

end OAI
