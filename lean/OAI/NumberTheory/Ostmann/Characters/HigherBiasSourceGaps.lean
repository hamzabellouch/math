import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.InitialCharacterScale
open Filter

def gapSchedule (BD : ℝ) (k : ℕ) (L : ℝ) : ℕ → ℝ
  | 0 => initialGap BD k L
  | j+1 => (2 : ℝ)^j * initialGap BD k L +
      (4 : ℝ)^(j+1) * Real.sqrt (wordSize k L : ℝ)

@[simp] theorem gapSchedule_zero (BD : ℝ) (k : ℕ) (L : ℝ) :
    gapSchedule BD k L 0 = initialGap BD k L := rfl

@[simp] theorem gapSchedule_one (BD : ℝ) (k : ℕ) (L : ℝ) :
    gapSchedule BD k L 1 = initialGap BD k L +
      4 * Real.sqrt (wordSize k L : ℝ) := by
  simp [gapSchedule]

theorem gapSchedule_of_pos (BD : ℝ) (k : ℕ) (L : ℝ) {j : ℕ} (hj : 0 < j) :
    gapSchedule BD k L j = (2 : ℝ)^(j-1) * initialGap BD k L +
      (4 : ℝ)^j * Real.sqrt (wordSize k L : ℝ) := by
  cases j with
  | zero => omega
  | succ j => simp [gapSchedule]

theorem gapSchedule_succ (BD : ℝ) (k : ℕ) (L : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    gapSchedule BD k L (j+1) = 2 * gapSchedule BD k L j +
      2 * (4 : ℝ)^j * Real.sqrt (wordSize k L : ℝ) := by
  cases j with
  | zero => omega
  | succ j => simp only [gapSchedule, pow_succ]; ring

theorem initialGap_ge_wordSize {BD : ℝ} (hBD : 1 ≤ BD) (k : ℕ) (L : ℝ) :
    (wordSize k L : ℝ) ≤ initialGap BD k L := by
  have hz := Real.log_nonneg (one_le_depthScale k)
  have hA : 1 ≤ BD + 20 * Real.log (depthScale k) := by linarith
  simpa only [initialGap, one_mul] using
    mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg (α := ℝ) (wordSize k L))

theorem gapSchedule_ge_wordSize {BD : ℝ} (hBD : 1 ≤ BD) (k : ℕ) (L : ℝ) (j : ℕ) :
    (wordSize k L : ℝ) ≤ gapSchedule BD k L j := by
  have hm := initialGap_ge_wordSize hBD k L
  have hg : 0 ≤ initialGap BD k L := (Nat.cast_nonneg _).trans hm
  cases j with
  | zero => exact hm
  | succ j =>
    have hp : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hp hg
    have hs : 0 ≤ (4 : ℝ)^(j+1) * Real.sqrt (wordSize k L : ℝ) := by positivity
    dsimp only [gapSchedule]
    nlinarith

theorem gapSchedule_nonneg {BD : ℝ} (hBD : 1 ≤ BD) (k : ℕ) (L : ℝ) (j : ℕ) :
    0 ≤ gapSchedule BD k L j :=
  (Nat.cast_nonneg _).trans (gapSchedule_ge_wordSize hBD k L j)

theorem gapSchedule_le_linear {BD : ℝ} (hBD : 1 ≤ BD) (k : ℕ)
    {L : ℝ} (hL : 1 ≤ L) {j : ℕ} (hj : j ≤ k) :
    gapSchedule BD k L j ≤
      ((2 : ℝ)^k + (4 : ℝ)^k) *
        (BD + 20 * Real.log (depthScale k)) * depthScale k * L := by
  have hz := one_le_depthScale k
  have hA : 1 ≤ BD + 20 * Real.log (depthScale k) := by
    have := Real.log_nonneg hz
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hm := (wordSize_bounds k hL0).2
  have hm1 : (1 : ℝ) ≤ (wordSize k L : ℝ) := by
    have hh : 1 ≤ wordSize k L := by
      apply (Nat.one_le_floor_iff _).mpr
      nlinarith
    exact_mod_cast hh
  have hs : Real.sqrt (wordSize k L : ℝ) ≤ initialGap BD k L :=
    (Real.sqrt_le_self_iff.mpr (Or.inr hm1)).trans (initialGap_ge_wordSize hBD k L)
  have hg0 : 0 ≤ initialGap BD k L := (Nat.cast_nonneg _).trans (initialGap_ge_wordSize hBD k L)
  have hg : initialGap BD k L ≤
      (BD + 20 * Real.log (depthScale k)) * depthScale k * L := by
    simpa only [initialGap, mul_assoc] using mul_le_mul_of_nonneg_left hm (by linarith :
      0 ≤ BD + 20 * Real.log (depthScale k))
  have hp2 : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  have hp4 : (0 : ℝ) ≤ 4^k := by positivity
  have hred : gapSchedule BD k L j ≤ ((2 : ℝ)^k + (4 : ℝ)^k) * initialGap BD k L := by
    cases j with
    | zero =>
      dsimp only [gapSchedule]
      nlinarith [mul_le_mul_of_nonneg_right hp2 hg0, mul_nonneg hp4 hg0]
    | succ j =>
      have h2 : (2 : ℝ)^j ≤ 2^k := pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : (4 : ℝ)^(j+1) ≤ 4^k := pow_le_pow_right₀ (by norm_num) hj
      have ht2 := mul_le_mul_of_nonneg_right h2 hg0
      have ht4 := mul_le_mul h4 hs (Real.sqrt_nonneg _) hp4
      dsimp only [gapSchedule]
      nlinarith
  calc
    _ ≤ ((2 : ℝ)^k + (4 : ℝ)^k) * initialGap BD k L := hred
    _ ≤ ((2 : ℝ)^k + (4 : ℝ)^k) *
        ((BD + 20 * Real.log (depthScale k)) * depthScale k * L) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by ring

theorem eventually_gapSchedule_le_exp (k : ℕ) {BD α : ℝ}
    (hBD : 1 ≤ BD) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∀ u : ℝ, α * L - 1 ≤ u → ∀ j : ℕ, j ≤ k →
      0 ≤ gapSchedule BD k L j ∧ gapSchedule BD k L j ≤ Real.exp u / 10 := by
  let C := ((2 : ℝ)^k + (4 : ℝ)^k) *
    (BD + 20 * Real.log (depthScale k)) * depthScale k
  have hdom := (tendsto_exp_mul_div_rpow_atTop 1 α hα).eventually_gt_atTop
    (10 * Real.exp 1 * C)
  filter_upwards [hdom, eventually_ge_atTop (1 : ℝ)] with L hdom hL
  intro u hu j hj
  refine ⟨gapSchedule_nonneg hBD k L j, ?_⟩
  have hLpos : 0 < L := by linarith
  have hbound : (10 * Real.exp 1 * C) * L < Real.exp (α * L) := by
    simp only [Real.rpow_one] at hdom
    exact (lt_div_iff₀ hLpos).mp hdom
  have hlinear : gapSchedule BD k L j ≤ C * L := gapSchedule_le_linear hBD k hL hj
  calc
    _ ≤ C * L := hlinear
    _ ≤ Real.exp (α * L - 1) / 10 := by
      rw [Real.exp_sub]
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).mpr
      apply (le_div_iff₀ (Real.exp_pos 1)).mpr
      nlinarith
    _ ≤ Real.exp u / 10 := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hu) (by norm_num)

end Ostmann.Characters.InitialCharacterScale

end

end OAI
