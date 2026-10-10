import OAI.Probability.SignedSweeps.HoleEntropy

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

def clippedBudget (τ : ℝ) (a h : ℕ) : ℝ :=
  max 0 (τ * h * Real.log a - (h : ℝ) * Real.log ((a : ℝ) / h))

@[simp] lemma clippedBudget_zero (τ : ℝ) (a : ℕ) : clippedBudget τ a 0 = 0 := by
  simp [clippedBudget]

lemma remainderBudget_eq_clippedBudget (κ : ℝ) (d l : ℕ) :
    remainderBudget κ d l = clippedBudget (coefficient κ d) (2 ^ d) l := by
  by_cases hl : l = 0 <;> simp [remainderBudget, clippedBudget, hl]

lemma clippedBudget_mono {τ τ' : ℝ} (hτ : τ ≤ τ') {a h : ℕ} (ha : 1 ≤ a) :
    clippedBudget τ a h ≤ clippedBudget τ' a h := by
  apply max_le_max le_rfl
  apply sub_le_sub_right
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hτ (by positivity))
    (Real.log_nonneg (by exact_mod_cast ha))

lemma clippedBudget_le_unclipped {κ τ : ℝ} (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    {a : ℕ} (ha : 0 < a) (h : ℕ) :
    clippedBudget τ a h ≤
      τ * h * Real.log a - (h : ℝ) * Real.log ((a : ℝ) / h) +
        (a : ℝ) ^ (1 - κ) * Real.log a := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hal : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
  have he : 0 ≤ (a : ℝ) ^ (1 - κ) * Real.log a :=
    mul_nonneg (Real.rpow_nonneg hap.le _) hal
  have hτ : 0 ≤ τ := hκ.trans hκτ
  unfold clippedBudget
  by_cases hf : 0 ≤ τ * h * Real.log a - (h : ℝ) * Real.log ((a : ℝ) / h)
  · rw [max_eq_right hf]
    linarith
  · rw [max_eq_left (le_of_not_ge hf)]
    have hh0 : h ≠ 0 := by intro hh; subst h; simp at hf
    have hhp : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero hh0
    have hlog : Real.log (h : ℝ) ≤ (1 - κ) * Real.log a := by
      have hb : τ * Real.log a < Real.log ((a : ℝ) / h) := by
        nlinarith
      rw [Real.log_div hap.ne' hhp.ne'] at hb
      nlinarith [mul_nonneg (sub_nonneg.mpr hκτ) hal]
    have hh : (h : ℝ) ≤ (a : ℝ) ^ (1 - κ) := by
      rw [Real.rpow_def_of_pos hap, ← Real.exp_log hhp]
      exact Real.exp_le_exp.mpr (by simpa [mul_comm] using hlog)
    have hd : Real.log ((a : ℝ) / h) ≤ Real.log a := by
      rw [Real.log_div hap.ne' hhp.ne']
      have hhl : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hh0)
      linarith
    have ht : 0 ≤ τ * h * Real.log a := by positivity
    have h₁ := mul_le_mul_of_nonneg_left hd hhp.le
    have h₂ := mul_le_mul_of_nonneg_right hh hal
    linarith

lemma line_budgets_le {κ τ : ℝ} (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    {s m l : ℕ} (hs : 0 < s) (hm : 0 < m) (z : Fin l → Fin s × Fin m) :
    (∑ j : Fin m, clippedBudget τ s (occupancy (fun i => (z i).2) j).val) +
      (∑ j : Fin s, clippedBudget τ m (occupancy (fun i => (z i).1) j).val) ≤
      τ * l * Real.log ((s * m : ℕ) : ℝ) - holeLineEntropy z +
        (m : ℝ) * (s : ℝ) ^ (1 - κ) * Real.log s +
        (s : ℝ) * (m : ℝ) ^ (1 - κ) * Real.log m := by
  classical
  have hc := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
    clippedBudget_le_unclipped hκ hκτ hs (occupancy (fun i => (z i).2) j).val)
  have hr := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) =>
    clippedBudget_le_unclipped hκ hκτ hm (occupancy (fun i => (z i).1) j).val)
  refine (add_le_add hc hr).trans_eq ?_
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Nat.cast_sum, occupancy_sum]
  simp only [holeLineEntropy, occupancyEntropy, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hs.ne' : (s : ℝ) ≠ 0)
      (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0)]
  ring

lemma clippedBudget_growth {τ : ℝ} (hτ : 0 ≤ τ) {a h H : ℕ}
    (ha : 0 < a) (hhH : h ≤ H) (hHa : H ≤ a) :
    clippedBudget τ a H ≤ clippedBudget τ a h +
      (τ * Real.log a + 1) * ((H : ℝ) - h) := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hl : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
  have hΔ : (0 : ℝ) ≤ (H : ℝ) - h := by exact_mod_cast (sub_nonneg.mpr (show (h : ℝ) ≤ H by exact_mod_cast hhH))
  have hcost : 0 ≤ (τ * Real.log a + 1) * ((H : ℝ) - h) := by positivity
  by_cases hH0 : H = 0
  · have : h = 0 := by omega
    subst H; subst h; simp
  have hHp : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH0
  have hHle : (H : ℝ) ≤ a := by exact_mod_cast hHa
  have hLH : 0 ≤ Real.log ((a : ℝ) / H) :=
    Real.log_nonneg ((le_div_iff₀ hHp).mpr (by simpa using hHle))
  unfold clippedBudget
  apply max_le
  · exact add_nonneg (le_max_left _ _) hcost
  by_cases hh0 : h = 0
  · subst h
    simp only [Nat.cast_zero, mul_zero, zero_mul, sub_self, max_self, sub_zero, zero_add]
    nlinarith [mul_nonneg hHp.le hLH]
  have hhp : (0 : ℝ) < h := by exact_mod_cast Nat.pos_of_ne_zero hh0
  have hentropy : (h : ℝ) * Real.log ((a : ℝ) / h) -
      (H : ℝ) * Real.log ((a : ℝ) / H) ≤ (H : ℝ) - h := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos hHp hhp)
    have hm := mul_le_mul_of_nonneg_left hlog hhp.le
    have heq : (h : ℝ) * ((H : ℝ) / h - 1) = (H : ℝ) - h := by
      field_simp
    rw [heq] at hm
    have hratio : Real.log ((a : ℝ) / h) =
        Real.log ((a : ℝ) / H) + Real.log ((H : ℝ) / h) := by
      simp only [Real.log_div hap.ne' hhp.ne', Real.log_div hap.ne' hHp.ne',
        Real.log_div hHp.ne' hhp.ne']
      ring
    rw [hratio]
    nlinarith [mul_nonneg hΔ hLH]
  have hb := le_max_right 0
    (τ * h * Real.log a - (h : ℝ) * Real.log ((a : ℝ) / h))
  nlinarith

end SignedSweeps
end

end OAI
