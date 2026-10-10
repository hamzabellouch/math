import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace OAI

/-! The explicit expanding-array scales in the bounded velocity detector.
The diffusion loss is summable even though the number of addresses grows. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector

def expansion (D : ℝ) : ℝ := 4 * D

def initialRadius (ν D K : ℝ) : ℝ :=
  1024 * 3000 * (1 + ν) * expansion D * (K * D + 2)

def radius (ν D K : ℝ) (n : ℕ) : ℝ := initialRadius ν D K * expansion D ^ n

def duration (ν D K : ℝ) (n : ℕ) : ℝ :=
  16 * radius ν D K (n + 1) * (K * D ^ (n + 1) + 2)

theorem initialRadius_pos {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) :
    0 < initialRadius ν D K := by
  have hD' : 0 < D := by linarith
  unfold initialRadius expansion
  positivity

theorem expansion_ge_four {D : ℝ} (hD : 1 ≤ D) : 4 ≤ expansion D := by
  unfold expansion
  linarith

theorem radius_pos {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (n : ℕ) :
    0 < radius ν D K n := by
  unfold radius
  exact mul_pos (initialRadius_pos hν hD hK)
    (pow_pos (lt_of_lt_of_le (by norm_num) (expansion_ge_four hD)) n)

theorem radius_grows {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (n : ℕ) :
    2 * radius ν D K n ≤ radius ν D K (n + 1) := by
  have he := expansion_ge_four hD
  have hr := (radius_pos hν hD hK n).le
  have hid : radius ν D K (n + 1) = expansion D * radius ν D K n := by
    simp only [radius, pow_succ]
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_right (by linarith) hr

theorem duration_ratio {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (n : ℕ) :
    duration ν D K n / radius ν D K n ^ 2 =
      (16 * expansion D / initialRadius ν D K) *
        (K * D * (1 / 4 : ℝ) ^ n + 2 * (expansion D)⁻¹ ^ n) := by
  have hr := (initialRadius_pos hν hD hK).ne'
  have he : expansion D ≠ 0 := ne_of_gt (by linarith [expansion_ge_four hD])
  have hpow : (D / expansion D) ^ n = (1 / 4 : ℝ) ^ n := by
    congr 1
    unfold expansion
    field_simp [ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hD)]
  rw [← hpow, div_pow, inv_pow]
  unfold duration radius
  rw [pow_succ, pow_succ]
  field_simp [hr, he]

theorem duration_ratio_le {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (n : ℕ) :
    duration ν D K n / radius ν D K n ^ 2 ≤
      (16 * expansion D / initialRadius ν D K) * (K * D + 2) * (1 / 4 : ℝ) ^ n := by
  rw [duration_ratio hν hD hK]
  have he : 0 < expansion D := by linarith [expansion_ge_four hD]
  have hi : (expansion D)⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa only [one_div] using
      (inv_le_inv₀ he (by norm_num)).mpr (expansion_ge_four hD)
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr he.le) hi n
  have hc : 0 ≤ 16 * expansion D / initialRadius ν D K := by
    exact div_nonneg (by positivity) (initialRadius_pos hν hD hK).le
  have htwo : 2 * (expansion D)⁻¹ ^ n ≤ 2 * (1 / 4 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  have hsum : K * D * (1 / 4 : ℝ) ^ n + 2 * (expansion D)⁻¹ ^ n ≤
      K * D * (1 / 4 : ℝ) ^ n + 2 * (1 / 4 : ℝ) ^ n := by linarith
  calc
    _ ≤ (16 * expansion D / initialRadius ν D K) *
        (K * D * (1 / 4 : ℝ) ^ n + 2 * (1 / 4 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hsum hc
    _ = _ := by ring

theorem diffusion_loss_term_bound {ν D K : ℝ}
    (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (n : ℕ) :
    ν * 3000 * (duration ν D K n / radius ν D K n ^ 2) ≤
      (ν / (1 + ν) / 64) * (1 / 4 : ℝ) ^ n := by
  have he : expansion D ≠ 0 := ne_of_gt (by linarith [expansion_ge_four hD])
  have hD' : 0 < D := by linarith
  have hk : K * D + 2 ≠ 0 := by positivity
  have hn : 1 + ν ≠ 0 := by positivity
  calc
    _ ≤ ν * 3000 * ((16 * expansion D / initialRadius ν D K) *
        (K * D + 2) * (1 / 4 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left (duration_ratio_le hν hD hK n) (by positivity)
    _ = _ := by
      unfold initialRadius
      field_simp [he, hk, hn]
      ring

theorem diffusion_loss_summable {ν D K : ℝ}
    (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) :
    Summable (fun n => ν * 3000 * (duration ν D K n / radius ν D K n ^ 2)) := by
  have hg : Summable (fun n : ℕ => (ν / (1 + ν) / 64) * (1 / 4 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).mul_left _
  apply hg.of_nonneg_of_le
  · intro n
    unfold duration
    have hr := radius_pos hν hD hK (n + 1)
    have hD' : 0 < D := by linarith
    positivity
  · exact diffusion_loss_term_bound hν hD hK

theorem total_stage_loss_le {ν D K : ℝ}
    (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) :
    (∑' n, ν * 3000 * (duration ν D K n / radius ν D K n ^ 2)) ≤
      ν / (1 + ν) / 48 := by
  have hg : Summable (fun n : ℕ => (ν / (1 + ν) / 64) * (1 / 4 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).mul_left _
  calc
    _ ≤ ∑' n : ℕ, (ν / (1 + ν) / 64) * (1 / 4 : ℝ) ^ n :=
      (diffusion_loss_summable hν hD hK).tsum_le_tsum
        (diffusion_loss_term_bound hν hD hK) hg
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)]
      ring

theorem initial_loss_lt {ν D K : ℝ}
    (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) :
    ν * 3000 / initialRadius ν D K ^ 2 < 1 / 48 := by
  have he := expansion_ge_four hD
  have hk : 2 ≤ K * D + 2 := by nlinarith
  have hR : 1024 * 3000 * (1 + ν) ≤ initialRadius ν D K := by
    unfold initialRadius
    nlinarith [mul_nonneg (show 0 ≤ 1024 * 3000 * (1 + ν) by positivity)
      (show 0 ≤ expansion D * (K * D + 2) - 1 by nlinarith)]
  have hr := initialRadius_pos hν hD hK
  apply (div_lt_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith [sq_nonneg (ν - 1), sq_nonneg (initialRadius ν D K - 1024 * 3000 * (1 + ν))]

theorem total_diffusion_loss_lt {ν D K : ℝ}
    (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) :
    ν * 3000 / initialRadius ν D K ^ 2 +
      (∑' n, ν * 3000 * (duration ν D K n / radius ν D K n ^ 2)) < 1 / 24 := by
  have hi := initial_loss_lt hν hD hK
  have hs := total_stage_loss_le hν hD hK
  have hr : ν / (1 + ν) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  linarith

end ForcedComputation.ExpandingDetector

end

end OAI
