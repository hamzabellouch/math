import OAI.NumberTheory.Ostmann.ZeroDensity.DensityAllZeros
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityNearCritical

namespace OAI

/-! # The actual Montgomery–Inoue zero-density input

The detector, fourth moment and large sieve prove the separated bound. Jensen
counts retain every analytic multiplicity when passing to the full enumeration.
This discharges the instance of Montgomery, *Zeros of L-functions* (1969),
Theorem 1, recorded in Inoue (2021), Lemma 1, needed by the main proof.
-/

namespace Ostmann

open scoped BigOperators

 theorem density_ten_to_thirteen_logs (L : ℝ) (hL : Real.log 2 ≤ L) :
    L ^ 10 ≤ (Real.log 2)⁻¹ ^ 3 * L ^ 13 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp := pow_le_pow_left₀ hl.le hL 3
  calc
    L ^ 10 = (Real.log 2)⁻¹ ^ 3 * ((Real.log 2) ^ 3 * L ^ 10) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl.ne', one_pow, one_mul]
    _ ≤ (Real.log 2)⁻¹ ^ 3 * (L ^ 3 * L ^ 10) := by gcongr
    _ = _ := by ring

 theorem publishedComplexZeroDensity : PublishedComplexZeroDensity actualCharacterZeros := by
  obtain ⟨C1, hC1, hnear⟩ := density_near_critical_family
  obtain ⟨C2, hC2, hfar⟩ := density_all_zero_count
  refine ⟨C1 + C2 * (Real.log 2)⁻¹ ^ 3, by positivity, ?_⟩
  intro Q hQ T σ hT hσ hσ1 F hF
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 1 < (Q : ℝ) ^ 2 * T := by nlinarith
  have hlogB : 0 < Real.log ((Q : ℝ) ^ 2 * T) := Real.log_pos hB
  have hL : Real.log 2 ≤ Real.log ((Q : ℝ) * T) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hL0 : 0 ≤ Real.log ((Q : ℝ) * T) := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hL
  by_cases hn : σ ≤ 1 / 2 + 1 / Real.log ((Q : ℝ) ^ 2 * T)
  · exact (hnear Q hQ T σ hT hσ hσ1 hn F hF).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity) :
        C1 ≤ C1 + C2 * (Real.log 2)⁻¹ ^ 3) (by positivity)) (by positivity))
  · have hs : 1 / 2 < σ := by
      have hi : 0 < 1 / Real.log ((Q : ℝ) ^ 2 * T) := by positivity
      linarith
    have hb4 : 4 ≤ (Q : ℝ) ^ 2 * T := by
      by_contra hh
      have hle : (Q : ℝ) ^ 2 * T ≤ 4 := le_of_lt (lt_of_not_ge hh)
      have hlog : Real.log ((Q : ℝ) ^ 2 * T) ≤ 2 := by
        have h := Real.log_le_log (by linarith) hle
        have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
          have hp := Real.log_pow (2 : ℝ) 2
          norm_num at hp
          exact hp
        rw [h4] at h
        have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have hi : (1 / 2 : ℝ) ≤ 1 / Real.log ((Q : ℝ) ^ 2 * T) :=
        (le_div_iff₀ hlogB).mpr (by linarith)
      apply hn
      linarith
    have hg : 1 / Real.log ((Q : ℝ) ^ 2 * T) ≤ σ - 1 / 2 := by linarith
    have hf := hfar Q hQ T σ hT hb4 hs hσ1 hg F hF
    have ha := density_ten_to_thirteen_logs (Real.log ((Q : ℝ) * T)) hL
    calc
      _ ≤ C2 * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
          (Real.log ((Q : ℝ) * T)) ^ 10 := hf
      _ ≤ C2 * ((Q : ℝ) ^ 2 * T) ^ densityTargetExponent σ *
          ((Real.log 2)⁻¹ ^ 3 * (Real.log ((Q : ℝ) * T)) ^ 13) := by
        exact mul_le_mul_of_nonneg_left ha (by positivity)
      _ = (C2 * (Real.log 2)⁻¹ ^ 3) * ((Q : ℝ) ^ 2 * T) ^ (3 * (1 - σ) / (2 - σ)) *
          (Real.log ((Q : ℝ) * T)) ^ 13 := by unfold densityTargetExponent; ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hC1.le) (by positivity)) (by positivity)

end Ostmann

end OAI
