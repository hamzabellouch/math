import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.SquareInterval

namespace OAI

open Matrix

namespace CurrentKS.Schedule
open CurrentKS.RationalRoot

def penaltyParameter (N : ℕ) (ν : ℚ) : ℚ := upperSqrt ν ν/(200*N)

lemma penaltyParameter_interval {N : ℕ} (hN : 0 < N) {ν : ℚ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) :
    Real.sqrt (ν:ℝ)/(200*N) ≤ (penaltyParameter N ν:ℝ) ∧
      (penaltyParameter N ν:ℝ) ≤ Real.sqrt (ν:ℝ)/(100*N) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hνr : (0:ℝ) < ν := by exact_mod_cast hν
  have hνr1 : (ν:ℝ) ≤ 1 := by exact_mod_cast hν1
  have hs := upperSqrt_spec ν ν hν hν.le hν1
  have hself : (ν:ℝ) ≤ Real.sqrt (ν:ℝ) := by
    nlinarith [Real.sq_sqrt hνr.le,Real.sqrt_nonneg (ν:ℝ)]
  have hup : (upperSqrt ν ν:ℝ) ≤ 2*Real.sqrt (ν:ℝ) := by linarith
  simp only [penaltyParameter,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast]
  refine ⟨div_le_div_of_nonneg_right hs.1 (by positivity),?_⟩
  have hh := div_le_div_of_nonneg_right hup (show (0:ℝ) ≤ 200*N by positivity)
  convert hh using 1
  ring

lemma penaltyParameter_pos_le {N : ℕ} (hN : 0 < N) {ν : ℚ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) :
    0 < penaltyParameter N ν ∧ penaltyParameter N ν ≤ 1 := by
  have hh := penaltyParameter_interval hN hν hν1
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hνr : (0:ℝ) < ν := by exact_mod_cast hν
  have hp : (0:ℝ) < penaltyParameter N ν :=
    (div_pos (Real.sqrt_pos.mpr hνr) (by positivity)).trans_le hh.1
  have hu : (penaltyParameter N ν:ℝ) ≤ 1 := by
    apply hh.2.trans
    apply (div_le_one (by positivity)).mpr
    have hs := Real.sqrt_le_one.mpr (show (ν:ℝ) ≤ 1 by exact_mod_cast hν1)
    linarith
  exact ⟨by exact_mod_cast hp,by exact_mod_cast hu⟩

lemma penaltyParameter_strip {N : ℕ} (hN : 0 < N) {ν : ℚ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) :
    1/(40000*(N:ℚ)^2) ≤ (penaltyParameter N ν)^2/ν ∧
      (penaltyParameter N ν)^2/ν ≤ 1/(10000*(N:ℚ)^2) := by
  have hh := penaltyParameter_interval hN hν hν1
  have hp := penaltyParameter_pos_le hN hν hν1
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hνr : (0:ℝ) < ν := by exact_mod_cast hν
  have hp' : (0:ℝ) ≤ penaltyParameter N ν := by exact_mod_cast hp.1.le
  have hlo := sq_le_sq₀ (by positivity : (0:ℝ) ≤ Real.sqrt (ν:ℝ)/(200*N)) hp' |>.mpr hh.1
  have hhi := sq_le_sq₀ hp' (by positivity : (0:ℝ) ≤ Real.sqrt (ν:ℝ)/(100*N)) |>.mpr hh.2
  rw [div_pow,Real.sq_sqrt hνr.le] at hlo hhi
  have hlo' : 1/(40000*(N:ℝ)^2) ≤ (penaltyParameter N ν:ℝ)^2/(ν:ℝ) := by
    apply (le_div_iff₀ hνr).mpr
    convert hlo using 1
    ring
  have hhi' : (penaltyParameter N ν:ℝ)^2/(ν:ℝ) ≤ 1/(10000*(N:ℝ)^2) := by
    apply (div_le_iff₀ hνr).mpr
    convert hhi using 1
    ring
  constructor
  · apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,
      Rat.cast_pow,Rat.cast_natCast] using hlo'
  · apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,
      Rat.cast_pow,Rat.cast_natCast] using hhi'

end CurrentKS.Schedule

end OAI
