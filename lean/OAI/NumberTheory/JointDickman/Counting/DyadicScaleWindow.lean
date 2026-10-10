import OAI.NumberTheory.JointDickman.Amplification.GeometricDyadicPartition

namespace OAI

/-! # Concrete dyadic indices in the manuscript's scale window -/

namespace JointDickman
open Finset

noncomputable def dyadicBoxLower (B : ℕ) (T : ℝ) : ℕ :=
  ⌊((B : ℝ)+Real.log T)/Real.log 2⌋₊-1

noncomputable def dyadicBoxUpper (B : ℕ) (T : ℝ) : ℕ :=
  ⌈(2*(B : ℝ)+Real.log T)/Real.log 2⌉₊+1

theorem dyadic_scale_window {B : ℕ} (hB : 30 ≤ B) {T : ℝ} (hT : 1 ≤ T)
    (hlogT : Real.log T ≤ (B : ℝ)/10) :
    dyadicBoxLower B T ≤ dyadicBoxUpper B T ∧
    (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      (k : ℝ)*Real.log 2 ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) ∧
      Real.log (Real.exp ((k : ℝ)*Real.log 2)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) ∧
    (∀ c : ℝ, 0 < c → (B : ℝ) ≤ Real.log c → Real.log c ≤ 2*B →
      2 ≤ (c*T)/(2 : ℝ)^(dyadicBoxLower B T) ∧
      (c*T)/(2 : ℝ)^(dyadicBoxUpper B T) ≤ 1) := by
  have hBr : (30 : ℝ) ≤ B := by exact_mod_cast hB
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    simpa only [show (2 : ℝ)-1 = 1 by norm_num] using Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  let v := ((B : ℝ)+Real.log T)/Real.log 2
  let w := (2*(B : ℝ)+Real.log T)/Real.log 2
  have hv : (1 : ℝ) ≤ v := by
    apply (le_div_iff₀ hl2).mpr
    nlinarith
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hvw : v ≤ w := by dsimp [v,w]; gcongr; linarith
  have hf1 : 1 ≤ ⌊v⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ v)).mpr (by simpa only [Nat.cast_one] using hv)
  have hL : dyadicBoxLower B T+1 = ⌊v⌋₊ := Nat.sub_add_cancel hf1
  have hU : dyadicBoxUpper B T = ⌈w⌉₊+1 := rfl
  have hfloor := Nat.floor_le (show 0 ≤ v by linarith)
  have hfloor' := Nat.lt_floor_add_one v
  have hceil := Nat.le_ceil w
  have hceil' := Nat.ceil_lt_add_one hw
  have hfv : (⌊v⌋₊ : ℝ)*Real.log 2 ≤ (B : ℝ)+Real.log T := by
    have hm := mul_le_mul_of_nonneg_right hfloor hl2.le
    simpa only [v,div_mul_cancel₀ _ hl2.ne'] using hm
  have hfv' : (B : ℝ)+Real.log T-Real.log 2 < (⌊v⌋₊ : ℝ)*Real.log 2 := by
    have hm := mul_lt_mul_of_pos_right hfloor' hl2
    dsimp only [v] at hm
    rw [div_mul_cancel₀ _ hl2.ne'] at hm
    nlinarith
  have hcw : 2*(B : ℝ)+Real.log T ≤ (dyadicBoxUpper B T : ℝ)*Real.log 2 := by
    have hm := mul_le_mul_of_nonneg_right hceil hl2.le
    dsimp only [w] at hm
    rw [div_mul_cancel₀ _ hl2.ne'] at hm
    rw [hU,Nat.cast_add,Nat.cast_one]
    nlinarith
  have hcw' : (dyadicBoxUpper B T : ℝ)*Real.log 2 < 2*(B : ℝ)+Real.log T+2*Real.log 2 := by
    have hm := mul_lt_mul_of_pos_right hceil' hl2
    dsimp only [w] at hm
    rw [add_mul,div_mul_cancel₀ _ hl2.ne',one_mul] at hm
    rw [hU,Nat.cast_add,Nat.cast_one]
    nlinarith
  have hLU : dyadicBoxLower B T ≤ dyadicBoxUpper B T := by
    have hh := (Nat.floor_mono hvw).trans (Nat.floor_le_ceil w)
    dsimp only [dyadicBoxLower,dyadicBoxUpper]
    exact (Nat.sub_le _ _).trans (hh.trans (Nat.le_succ _))
  refine ⟨hLU,?_,?_⟩
  · intro k hk
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    obtain ⟨hnL,hnU⟩ := mem_Ico.mp hn
    have hlo : ⌊v⌋₊ ≤ n+1 := by rw [← hL]; omega
    have hhi : n+1 ≤ dyadicBoxUpper B T := by omega
    have hlo' : (⌊v⌋₊ : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast hlo
    have hhi' : ((n+1 : ℕ) : ℝ) ≤ dyadicBoxUpper B T := by exact_mod_cast hhi
    have hlo'' := mul_le_mul_of_nonneg_right hlo' hl2.le
    have hhi'' := mul_le_mul_of_nonneg_right hhi' hl2.le
    have hlog : Real.log (Real.exp (((n+1 : ℕ) : ℝ)*Real.log 2)/T) =
        ((n+1 : ℕ) : ℝ)*Real.log 2-Real.log T := by
      rw [Real.log_div (Real.exp_pos _).ne' hTpos.ne',Real.log_exp]
    simp only [Int.cast_natCast]
    rw [hlog]
    constructor <;> constructor <;> nlinarith
  · intro c hc hclo hchi
    have hct := mul_pos hc hTpos
    have hlogct : Real.log (c*T) = Real.log c+Real.log T := Real.log_mul hc.ne' hTpos.ne'
    constructor
    · apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
      have hh : (2 : ℝ)^(dyadicBoxLower B T+1) ≤ c*T := by
        rw [← exp_nat_log_two,← Real.exp_log hct]
        apply Real.exp_le_exp.mpr
        rw [hlogct,hL]
        exact hfv.trans (by linarith)
      simpa only [pow_succ,mul_comm] using hh
    · apply (div_le_one (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
      rw [← exp_nat_log_two,← Real.exp_log hct]
      apply Real.exp_le_exp.mpr
      rw [hlogct]
      exact (show Real.log c+Real.log T ≤ 2*(B : ℝ)+Real.log T by linarith).trans hcw

end JointDickman

end OAI
