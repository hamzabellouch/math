import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic
import OAI.Probability.FreeIsing.Gaussian.ComponentSignalAttenuation

namespace OAI

noncomputable section
namespace Problem367

theorem half_path_cut_admissible {n m : ℕ} (hn : 8 ≤ n) (hm : n / 2 ≤ m) :
    let k := m / 2 - 1
    let L := m - m / 2
    k + 1 + L = m ∧
      (n : ℝ) / 8 - 1 ≤ (k + 1 : ℕ) ∧ (n : ℝ) / 8 ≤ (L : ℝ) := by
  dsimp only
  have hk : m / 2 - 1 + 1 = m / 2 := by omega
  rw [hk]
  refine ⟨by omega, ?_, ?_⟩
  · have hround : n ≤ 8 * (m / 2) + 8 := by omega
    have hr : (n : ℝ) ≤ 8 * (m / 2 : ℕ) + 8 := by exact_mod_cast hround
    linarith
  · have hround : n ≤ 8 * (m - m / 2) := by omega
    have hr : (n : ℝ) ≤ 8 * (m - m / 2 : ℕ) := by exact_mod_cast hround
    linarith

def criticalNoiseEta (d : ℕ) (beta : ℝ) : ℝ :=
  min (ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (Real.log ((d : ℝ) - 1) / 8)

def criticalNoiseLengthConstant (beta : ℝ) : ℝ :=
  max 8 (32 * Real.log 2 / ComponentSignalAttenuation.lossCoefficient (Real.tanh beta))

def criticalNoiseTailBase (d : ℕ) : ℝ := ((d : ℝ) - 1) ^ (1 / 16 : ℝ)

theorem criticalNoise_constants_positive {d : ℕ} {beta : ℝ}
    (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) :
    0 < criticalNoiseEta d beta ∧ 0 < criticalNoiseLengthConstant beta ∧
      1 < criticalNoiseTailBase d ∧ 0 < 1 / (2 * ((d : ℝ) - 1)) := by
  have hb1 : 1 < (d : ℝ) - 1 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hθ : 0 < Real.tanh beta := by
    by_contra h
    have hz := le_antisymm (not_lt.mp h) (tanh_nonneg_of_beta_nonneg hb)
    simp [hz] at hcritical
  have hγ := ComponentSignalAttenuation.lossCoefficient_pos hθ (Real.tanh_lt_one beta)
  refine ⟨lt_min (div_pos hγ (by norm_num))
    (div_pos (Real.log_pos hb1) (by norm_num)), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · exact Real.one_lt_rpow hb1 (by norm_num)
  · have : 0 < (d : ℝ) - 1 := zero_lt_one.trans hb1
    positivity

theorem criticalNoise_length_admissible {d n : ℕ} {beta ω : ℝ}
    (_hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : criticalNoiseLengthConstant beta / ω ≤ (n : ℝ)) :
    8 ≤ n ∧ 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) * (ω * ((n : ℝ) / 4)) := by
  have hθ : 0 < Real.tanh beta := by
    by_contra h
    have hz := le_antisymm (not_lt.mp h) (tanh_nonneg_of_beta_nonneg hb)
    simp [hz] at hcritical
  have hγ := ComponentSignalAttenuation.lossCoefficient_pos hθ (Real.tanh_lt_one beta)
  have hlarge := (div_le_iff₀ hω).mp hn
  have hlow : (8 : ℝ) ≤ criticalNoiseLengthConstant beta := le_max_left _ _
  have hmul := mul_le_mul_of_nonneg_left hω1 (Nat.cast_nonneg n : (0 : ℝ) ≤ _)
  have hnR : (8 : ℝ) ≤ n := by nlinarith
  refine ⟨by exact_mod_cast hnR, ?_⟩
  have hfrac : 32 * Real.log 2 / ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) ≤
      (n : ℝ) * ω := (le_max_right _ _).trans hlarge
  have h := (div_le_iff₀ hγ).mp hfrac
  nlinarith

theorem criticalNoise_threshold_eq (d : ℕ) (beta ω : ℝ) (n : ℕ) :
    Real.exp (-(criticalNoiseEta d beta * ω) * ((n : ℝ) / 4)) =
      Real.exp (-((criticalNoiseEta d beta / 4) * ω) * n) := by congr 1; ring

theorem criticalNoise_tail_eq {d : ℕ} (hd : 3 ≤ d) (n : ℕ) :
    Real.exp (-(((d : ℝ) - 1) ^ (((n : ℝ) / 4) / 4)) /
      (2 * ((d : ℝ) - 1))) =
      Real.exp (-(1 / (2 * ((d : ℝ) - 1))) * criticalNoiseTailBase d ^ n) := by
  have hb : 0 ≤ (d : ℝ) - 1 := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hp : ((d : ℝ) - 1) ^ (((n : ℝ) / 4) / 4) = criticalNoiseTailBase d ^ n := by
    rw [show ((n : ℝ) / 4) / 4 = (1 / 16 : ℝ) * n by ring,
      Real.rpow_mul hb, Real.rpow_natCast]
    rfl
  rw [hp]
  congr 1
  ring

end Problem367

end

end OAI
