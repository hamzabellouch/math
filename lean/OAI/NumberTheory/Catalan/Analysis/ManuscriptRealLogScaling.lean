import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

namespace OAI

namespace InternalCatalan

theorem manuscript_rat_log_scaling_Ico (s : ℚ)
    (hlo : (2 : ℚ) ^ (-100 : ℤ) ≤ s)
    (hhi : s ≤ (2 : ℚ) ^ (100 : ℤ)) :
    ∃ m : ℤ, ∃ y : ℚ,
      s = (2 : ℚ) ^ m * y ∧ y ∈ Set.Ico (1 : ℚ) 2 ∧ |m| ≤ 100 := by
  have htwo : (1 : ℚ) < 2 := by norm_num
  have htwopos : (0 : ℚ) < 2 := by norm_num
  have hs : 0 < s := lt_of_lt_of_le (zpow_pos htwopos (-100 : ℤ)) hlo
  obtain ⟨m, hmlo, hmhi⟩ := exists_mem_Ico_zpow hs htwo
  have hpow : (0 : ℚ) < 2 ^ m := zpow_pos htwopos m
  have hmupper : m ≤ (100 : ℤ) :=
    (zpow_le_zpow_iff_right₀ htwo).mp (le_trans hmlo hhi)
  have hmlowerStrict : (-100 : ℤ) < m + 1 :=
    (zpow_lt_zpow_iff_right₀ htwo).mp (lt_of_le_of_lt hlo hmhi)
  have hmlower : (-100 : ℤ) ≤ m := by omega
  refine ⟨m, s / (2 : ℚ) ^ m, ?_, ?_, abs_le.mpr ⟨hmlower, hmupper⟩⟩
  · exact (mul_div_cancel₀ s (ne_of_gt hpow)).symm
  · constructor
    · apply (le_div_iff₀ hpow).mpr
      simpa only [one_mul] using hmlo
    · apply (div_lt_iff₀ hpow).mpr
      simpa only [zpow_add₀ (ne_of_gt htwopos), zpow_one, mul_comm] using hmhi

theorem manuscript_rat_log_scaling (s : ℚ)
    (hlo : (2 : ℚ) ^ (-100 : ℤ) ≤ s)
    (hhi : s ≤ (2 : ℚ) ^ (100 : ℤ)) :
    ∃ m : ℤ, ∃ y : ℚ,
      s = (2 : ℚ) ^ m * y ∧ y ∈ Set.Icc (1 : ℚ) 2 ∧ |m| ≤ 100 := by
  obtain ⟨m, y, hnorm, hy, hm⟩ := manuscript_rat_log_scaling_Ico s hlo hhi
  exact ⟨m, y, hnorm, ⟨hy.1, hy.2.le⟩, hm⟩

theorem manuscript_real_log_scaling (s : ℝ)
    (hlo : (2 : ℝ) ^ (-100 : ℤ) ≤ s)
    (hhi : s ≤ (2 : ℝ) ^ (100 : ℤ)) :
    ∃ m : ℤ, ∃ y : ℝ,
      s = (2 : ℝ) ^ m * y ∧ y ∈ Set.Icc (1 : ℝ) 2 ∧ |(m : ℝ)| ≤ 100 := by
  have htwo : (1 : ℝ) < 2 := by norm_num
  have htwopos : (0 : ℝ) < 2 := by norm_num
  have hs : 0 < s := lt_of_lt_of_le (zpow_pos htwopos (-100 : ℤ)) hlo
  obtain ⟨m, hmlo, hmhi⟩ := exists_mem_Ico_zpow hs htwo
  have hpow : (0 : ℝ) < 2 ^ m := zpow_pos htwopos m
  have hmupper : m ≤ (100 : ℤ) :=
    (zpow_le_zpow_iff_right₀ htwo).mp (le_trans hmlo hhi)
  have hmlowerStrict : (-100 : ℤ) < m + 1 :=
    (zpow_lt_zpow_iff_right₀ htwo).mp (lt_of_le_of_lt hlo hmhi)
  have hmlower : (-100 : ℤ) ≤ m := by omega
  have hmabs : |m| ≤ (100 : ℤ) := abs_le.mpr ⟨hmlower, hmupper⟩
  have hmreal : |(m : ℝ)| ≤ 100 := by exact_mod_cast hmabs
  refine ⟨m, s / (2 : ℝ) ^ m, ?_, ?_, hmreal⟩
  · exact (mul_div_cancel₀ s (ne_of_gt hpow)).symm
  · constructor
    · apply (le_div_iff₀ hpow).mpr
      simpa only [one_mul] using hmlo
    · apply le_of_lt
      apply (div_lt_iff₀ hpow).mpr
      simpa only [zpow_add₀ (ne_of_gt htwopos), zpow_one, mul_comm] using hmhi

theorem manuscript_rat_real_log_scaling (s : ℚ)
    (hlo : (2 : ℝ) ^ (-100 : ℤ) ≤ (s : ℝ))
    (hhi : (s : ℝ) ≤ (2 : ℝ) ^ (100 : ℤ)) :
    ∃ m : ℤ, ∃ y : ℚ,
      (s : ℝ) = (2 : ℝ) ^ m * (y : ℝ) ∧
      (y : ℝ) ∈ Set.Icc (1 : ℝ) 2 ∧ |(m : ℝ)| ≤ 100 := by
  have hloRat : (2 : ℚ) ^ (-100 : ℤ) ≤ s := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_zpow, Rat.cast_ofNat] using hlo
  have hhiRat : s ≤ (2 : ℚ) ^ (100 : ℤ) := by
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_zpow, Rat.cast_ofNat] using hhi
  obtain ⟨m, y, hnorm, hy, hm⟩ := manuscript_rat_log_scaling s hloRat hhiRat
  refine ⟨m, y, ?_, ?_, ?_⟩
  · have h := congrArg (fun q : ℚ => (q : ℝ)) hnorm
    simpa only [Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat] using h
  · constructor
    · have h := (Rat.cast_le (K := ℝ)).mpr hy.1
      simpa only [Rat.cast_one] using h
    · have h := (Rat.cast_le (K := ℝ)).mpr hy.2
      simpa only [Rat.cast_ofNat] using h
  · exact_mod_cast hm

end InternalCatalan

end OAI
