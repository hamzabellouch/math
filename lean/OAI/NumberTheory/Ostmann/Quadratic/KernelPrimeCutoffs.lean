import OAI.NumberTheory.Ostmann.Quadratic.KernelAnalyticParameters

namespace OAI

/-! # Actual integer cutoffs for the quadratic split-prime argument -/

namespace Ostmann

noncomputable def kernelConductorCutoff (η L : ℝ) : ℕ := ⌈4 * Real.exp (2 * η * L)⌉₊
noncomputable def kernelSplitCutoff (η L : ℝ) : ℕ := ⌊Real.exp ((1 / 2 - 5 * η) * L)⌋₊
noncomputable def kernelDivisorCutoff (L : ℝ) : ℕ := ⌈Real.sqrt L⌉₊

theorem kernelConductorCutoff_bounds (η L : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L) :
    2 ≤ kernelConductorCutoff η L ∧
      2 * η * L ≤ Real.log (4 * (kernelConductorCutoff η L : ℝ)) ∧
      Real.log (4 * (kernelConductorCutoff η L : ℝ)) ≤ 2 * η * L + Real.log 20 := by
  let t := 2 * η * L
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have he1 := Real.one_le_exp ht
  have hc : 4 * Real.exp t ≤ (kernelConductorCutoff η L : ℝ) := Nat.le_ceil _
  have hcl : (kernelConductorCutoff η L : ℝ) < 4 * Real.exp t + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hq : (2 : ℝ) ≤ kernelConductorCutoff η L := by linarith
  have hpos : 0 < 4 * (kernelConductorCutoff η L : ℝ) := by linarith
  refine ⟨by exact_mod_cast hq, ?_, ?_⟩
  · apply (Real.le_log_iff_exp_le hpos).mpr
    change Real.exp t ≤ _
    linarith
  · have he : 4 * (kernelConductorCutoff η L : ℝ) ≤ 20 * Real.exp t := by linarith
    have hl := Real.log_le_log hpos he
    rw [Real.log_mul (by norm_num : (20 : ℝ) ≠ 0) (Real.exp_ne_zero t), Real.log_exp] at hl
    simpa only [t, add_comm] using hl

theorem kernelConductorCutoff_covers (η L : ℝ) (d : ℤ)
    (hd : (d.natAbs : ℝ) ≤ Real.exp (2 * η * L)) :
    4 * d.natAbs ≤ kernelConductorCutoff η L := by
  have hc : 4 * Real.exp (2 * η * L) ≤ (kernelConductorCutoff η L : ℝ) := Nat.le_ceil _
  have hh : (4 : ℝ) * d.natAbs ≤ kernelConductorCutoff η L := by linarith
  exact_mod_cast hh

theorem kernelDivisorCutoff_bounds (L : ℝ) (hL : 0 < L) :
    0 < kernelDivisorCutoff L ∧ Real.sqrt L ≤ kernelDivisorCutoff L ∧
      (kernelDivisorCutoff L : ℝ) ≤ Real.sqrt L + 1 := by
  have hlo : Real.sqrt L ≤ (kernelDivisorCutoff L : ℝ) := Nat.le_ceil _
  have hhi : (kernelDivisorCutoff L : ℝ) < Real.sqrt L + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg L)
  have hp : (0 : ℝ) < kernelDivisorCutoff L := (Real.sqrt_pos.mpr hL).trans_le hlo
  exact ⟨by exact_mod_cast hp, hlo, hhi.le⟩

theorem kernelSplitCutoff_bounds (η L : ℝ) (hη : η ≤ 1 / 1000) (hL : 100 ≤ L) :
    0 < kernelSplitCutoff η L ∧
      (12 / 25 : ℝ) * L ≤ Real.log (kernelSplitCutoff η L : ℝ) := by
  let a := 1 / 2 - 5 * η
  have hL0 : 0 ≤ L := by linarith
  have ha : (99 / 200 : ℝ) ≤ a := by dsimp [a]; linarith
  have haL : (99 / 200 : ℝ) * L ≤ a * L := mul_le_mul_of_nonneg_right ha hL0
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he2 : (2 : ℝ) ≤ Real.exp (a * L) := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mp
    linarith
  have hf : Real.exp (a * L) < (kernelSplitCutoff η L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hhalf : Real.exp (a * L) / 2 ≤ (kernelSplitCutoff η L : ℝ) := by linarith
  have hp : (0 : ℝ) < kernelSplitCutoff η L :=
    (div_pos (Real.exp_pos _) (by norm_num)).trans_le hhalf
  refine ⟨by exact_mod_cast hp, ?_⟩
  have hl := Real.log_le_log (div_pos (Real.exp_pos (a * L)) (by norm_num)) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hl
  linarith

theorem kernelSplitCutoff_log_lower (η L : ℝ) (hη : η ≤ 1 / 1000) (hL : 100 ≤ L) :
    (1 / 2 - 5 * η) * L - 1 ≤ Real.log (kernelSplitCutoff η L : ℝ) := by
  let t := (1 / 2 - 5 * η) * L
  have hηL := mul_le_mul_of_nonneg_right hη (show 0 ≤ L by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he2 : (2 : ℝ) ≤ Real.exp t := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mp
    dsimp [t]
    linarith
  have hf : Real.exp t < (kernelSplitCutoff η L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hhalf : Real.exp t / 2 ≤ (kernelSplitCutoff η L : ℝ) := by linarith
  have hl := Real.log_le_log (div_pos (Real.exp_pos t) (by norm_num)) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hl
  change t - 1 ≤ _
  linarith

end Ostmann

end OAI
