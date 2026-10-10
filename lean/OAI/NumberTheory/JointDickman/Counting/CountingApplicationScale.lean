import OAI.NumberTheory.JointDickman.Counting.CountingModelEnvelope
import Mathlib.Topology.Instances.Nat

namespace OAI

/-! # The scales used to apply the counting model -/
namespace JointDickman
open Filter
open scoped Topology

noncomputable def countingSmoothingLength (B : ℕ) : ℕ := ⌊(B : ℝ)^(1/10 : ℝ)⌋₊
noncomputable def countingMajorDenominator (B : ℕ) : ℕ := ⌈(B : ℝ)^(2/5 : ℝ)⌉₊

theorem countingSmoothingLength_tendsto : Tendsto countingSmoothingLength atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/10)).comp
    tendsto_natCast_atTop_atTop)

theorem countingSmoothingLength_div_tendsto :
    Tendsto (fun B => (countingSmoothingLength B : ℝ)/(amplificationMultiplier B : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun B => by positivity)
    (fun B => div_le_div_of_nonneg_right
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg B) _)) (Nat.cast_nonneg _))
    (power_div_amplificationMultiplier (by norm_num : (1/10 : ℝ) < 8/25))

theorem countingMajorDenominator_valid : ∀ᶠ B : ℕ in atTop,
    0 < countingMajorDenominator B ∧ (B : ℝ)^(2/5 : ℝ) ≤ countingMajorDenominator B ∧
      amplificationMultiplier B*countingMajorDenominator B ≤ B := by
  have hp₀ := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7/25)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hp : ∀ᶠ B : ℕ in atTop, (2 : ℝ) ≤ (B : ℝ)^(7/25 : ℝ) := hp₀
  filter_upwards [amplificationMultiplier_comparable,hp,eventually_ge_atTop 1] with B hT hp hB
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0 : ℝ) < B := by linarith
  have hq := Nat.le_ceil ((B : ℝ)^(2/5 : ℝ))
  have hqpos : 0 < countingMajorDenominator B := by
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos hBp _
  refine ⟨hqpos,hq,?_⟩
  have hqhi : (countingMajorDenominator B : ℝ) ≤ 2*(B : ℝ)^(2/5 : ℝ) := by
    have hf := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg B) (2/5 : ℝ))
    have hone := Real.one_le_rpow hBr (by norm_num : (0 : ℝ) ≤ 2/5)
    dsimp [countingMajorDenominator]
    linarith
  have hmul : (B : ℝ)^(8/25 : ℝ)*(B : ℝ)^(2/5 : ℝ) = (B : ℝ)^(18/25 : ℝ) := by
    rw [← Real.rpow_add hBp]
    norm_num
  have hpow : (B : ℝ)^(18/25 : ℝ)*(B : ℝ)^(7/25 : ℝ) = B := by
    rw [← Real.rpow_add hBp]
    norm_num
  have hh : (amplificationMultiplier B : ℝ)*countingMajorDenominator B ≤ B := calc
    _ ≤ (B : ℝ)^(8/25 : ℝ)*(2*(B : ℝ)^(2/5 : ℝ)) :=
      mul_le_mul hT.2.2 hqhi (Nat.cast_nonneg _) (by positivity)
    _ = 2*(B : ℝ)^(18/25 : ℝ) := by rw [← hmul]; ring
    _ ≤ (B : ℝ)^(18/25 : ℝ)*(B : ℝ)^(7/25 : ℝ) := by
      calc
        _ = (B : ℝ)^(18/25 : ℝ)*2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (Nat.cast_nonneg B) (18/25 : ℝ))
    _ = B := hpow
  exact_mod_cast hh

theorem counting_block_scale {A : ℕ} (hA : 0 < A) : ∀ᶠ B : ℕ in atTop,
    (1/(2*(A : ℝ)))*amplificationMultiplier B ≤ ((amplificationMultiplier B/A : ℕ) : ℝ) ∧
      amplificationMultiplier B ≤ A*amplificationMultiplier B ∧
      ((A : ℝ)/2)*(B : ℝ)^(0.32 : ℝ) ≤ A*amplificationMultiplier B ∧
      (A*amplificationMultiplier B : ℕ) ≤ (A : ℝ)*(B : ℝ)^(0.32 : ℝ) ∧
      A*amplificationMultiplier B ≤ B^2 := by
  have ht : Tendsto amplificationMultiplier atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8/25)).comp
      tendsto_natCast_atTop_atTop)
  filter_upwards [amplificationMultiplier_comparable,ht.eventually_ge_atTop (2*A),
    amplification_block_size_le_square A] with B hT hlarge hsquare
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hlarge' : 2*(A : ℝ) ≤ amplificationMultiplier B := by exact_mod_cast hlarge
  have hdiv : (amplificationMultiplier B : ℝ)/(2*(A : ℝ)) ≤ (amplificationMultiplier B/A : ℕ) := by
    have hfloor : (amplificationMultiplier B : ℝ) < ((amplificationMultiplier B/A : ℕ) : ℝ)*A+A := by
      have hh := Nat.lt_mul_div_succ (amplificationMultiplier B) hA
      have hh' : (amplificationMultiplier B : ℝ) < (A : ℝ)*((amplificationMultiplier B/A : ℕ)+1) := by exact_mod_cast hh
      nlinarith
    apply (div_le_iff₀ (by positivity : 0 < 2*(A : ℝ))).mpr
    nlinarith
  refine ⟨?_,?_,?_,?_,hsquare⟩
  · simpa only [one_div_mul_eq_div] using hdiv
  · nlinarith
  · have hh := mul_le_mul_of_nonneg_left hT.2.1 hAr.le
    convert hh using 1
    · norm_num; ring
  · have hh := mul_le_mul_of_nonneg_left hT.2.2 hAr.le
    convert hh using 1 <;> norm_num

end JointDickman

end OAI
