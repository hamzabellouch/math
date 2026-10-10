import OAI.Probability.SATComputability.PoissonBlockBound
import OAI.Probability.SATComputability.CandidateSurvival

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

noncomputable def dyadicLevel (j : ℕ) : ℝ := ((2 : ℝ)^j)⁻¹
def dyadicTruncation (j : ℕ) : ℕ := j+122
def dyadicMultiplicity (j : ℕ) : ℕ := 2*(j+122)*2^((j+1)/2)
def dyadicBlock (j : ℕ) : ℕ := 32*dyadicTruncation j*dyadicMultiplicity j

theorem dyadicLevel_pos (j : ℕ) : 0 < dyadicLevel j := by
  unfold dyadicLevel
  positivity

theorem dyadicLevel_le_one (j : ℕ) : dyadicLevel j ≤ 1 := by
  unfold dyadicLevel
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem dyadic_truncation_error (j : ℕ) :
    Real.exp 60 / (2 : ℝ)^(dyadicTruncation j) ≤ dyadicLevel j/4 := by
  have he : Real.exp 60 ≤ (2 : ℝ)^120 := by
    calc
      _ = (Real.exp 1)^60 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (4 : ℝ)^60 := pow_le_pow_left₀ (Real.exp_pos 1).le
        (Real.exp_one_lt_three.le.trans (by norm_num : (3 : ℝ) ≤ 4)) 60
      _ = _ := by norm_num
  have hden : (2 : ℝ)^(dyadicTruncation j) = (2 : ℝ)^j * (2 : ℝ)^122 := by
    rw [dyadicTruncation, pow_add]
  rw [dyadicLevel, hden]
  apply (div_le_iff₀ (by positivity)).mpr
  field_simp
  nlinarith

theorem dyadic_multiplicity_pos (j : ℕ) : 0 < dyadicMultiplicity j := by
  unfold dyadicMultiplicity
  positivity

theorem dyadic_replacement_error (j : ℕ) :
    (dyadicTruncation j : ℝ) / (dyadicMultiplicity j : ℝ)^2 ≤ dyadicLevel j/4 := by
  have hp : j ≤ (j+1)/2*2 := by omega
  have hpow : (2 : ℝ)^j ≤ ((2 : ℝ)^((j+1)/2))^2 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hp
  have hL : (1 : ℝ) ≤ j+122 := by exact_mod_cast (show 1 ≤ j+122 by omega)
  have hmul : (4 : ℝ)*((j:ℝ)+122)*(2:ℝ)^j ≤
      (2*((j:ℝ)+122)*(2:ℝ)^((j+1)/2))^2 := by
    have hprod := mul_le_mul_of_nonneg_left hpow
      (show (0 : ℝ) ≤ 4*((j:ℝ)+122) by positivity)
    have hrest := mul_nonneg
      (show (0 : ℝ) ≤ (j:ℝ)+122-1 by linarith)
      (show (0 : ℝ) ≤ 4*((j:ℝ)+122)*((2:ℝ)^((j+1)/2))^2 by positivity)
    nlinarith
  unfold dyadicTruncation dyadicMultiplicity dyadicLevel
  push_cast
  apply (div_le_iff₀ (by positivity)).mpr
  rw [show (2^j : ℝ)⁻¹ / 4 * (2*((j:ℝ)+122)*2^((j+1)/2))^2 =
      (2*((j:ℝ)+122)*2^((j+1)/2))^2 / (4*2^j) by field_simp]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem dyadic_block_kills {n : ℕ} [NeZero n]
    (U : Finset (DeletionCandidate n)) (j : ℕ) (rate : ℝ≥0)
    (hrate : (1 : ℝ)/8 ≤ rate)
    (hq : dyadicLevel j ≤ poissonKillProbability U 2 60) :
    dyadicLevel j/4 ≤ poissonKillProbability U 3 (rate*dyadicBlock j) := by
  apply poisson_two_to_three_block U (dyadic_multiplicity_pos j)
    (show 0 < dyadicTruncation j by unfold dyadicTruncation; omega) hq
    (dyadic_truncation_error j) (dyadic_replacement_error j)
  simp only [dyadicBlock, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_mul,
    Nat.cast_ofNat, NNReal.coe_ofNat]
  have h := mul_le_mul_of_nonneg_right hrate
    (show (0 : ℝ) ≤ 32*(dyadicTruncation j : ℝ)*dyadicMultiplicity j by positivity)
  nlinarith

def dyadicBin {n : ℕ} [NeZero n] (j : ℕ) (U : Finset (DeletionCandidate n)) : Prop :=
  U.Nonempty ∧ dyadicLevel j ≤ poissonKillProbability U 2 60 ∧
    poissonKillProbability U 2 60 ≤ 2*dyadicLevel j

theorem dyadic_bin_occupation {n : ℕ} [NeZero n]
    (rate : ℝ≥0) (hrate : (1 : ℝ)/8 ≤ rate) (j M : ℕ)
    (U : Finset (DeletionCandidate n)) :
    (∑ t ∈ Finset.range M, (candidateBlock (rate*t) 3 U).expect
      (fun V => if dyadicBin j V then 1 else 0)) ≤
        4*(dyadicBlock j : ℝ)/dyadicLevel j := by
  classical
  have h := candidateBlock_occupation rate 3 (dyadicBlock j) M (dyadicBin j)
    (show 0 < dyadicLevel j/4 by positivity [dyadicLevel_pos j])
    (fun V hV => ⟨hV.1, dyadic_block_kills V j rate hrate hV.2.1⟩) U
  convert h using 1
  ring

end FixedClauseThreshold.Computability

end OAI
