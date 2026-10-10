import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzCommutatorSampling
import OAI.MathematicalPhysics.DefocusingNLS.Linear.LatticeMomentAlgebra

namespace OAI

/-! # Uniform polynomial moments of the actual sampled profile -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem one_add_pow_le_commutator (N : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ N ≤ 2 ^ N * (1 + r * (2 + r) ^ N) := by
  have hpow : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  by_cases h : r ≤ 1
  · exact (pow_le_pow_left₀ (by positivity) (by linarith) N).trans
      (le_mul_of_one_le_right (by positivity) (by
        nlinarith [mul_nonneg hr (pow_nonneg (by linarith : 0 ≤ 2 + r) N)]))
  · have hr1 : 1 ≤ r := (lt_of_not_ge h).le
    calc
      _ ≤ (2 + r) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ ≤ r * (2 + r) ^ N := le_mul_of_one_le_left (by positivity) hr1
      _ ≤ 1 + r * (2 + r) ^ N := by linarith
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hpow

theorem exists_schwartzPolynomialMoment_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (N : ℕ) (K : 𝓢(E, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L →
      Summable (latticeMomentMass L N (schwartzLatticeCoefficient L K)) ∧
      (∑' n, latticeMomentMass L N (schwartzLatticeCoefficient L K) n) ≤ C := by
  obtain ⟨B, hB, hb⟩ := exists_schwartzTorusSample_norm_bound a k ha1 hk K
  obtain ⟨D, hD, hd⟩ := exists_schwartzCommutator_sampling_bound N K
  refine ⟨2 ^ N * (expandingEmbeddingBound a k * B + D), by
    unfold expandingEmbeddingBound
    positivity, ?_⟩
  intro L hL
  have hplain := summable_norm_expandingFourierCoefficient a k L ha ha1 hk hL
    (schwartzTorusSample a k L ha1 hk hL K)
  have hbplain := tsum_norm_expandingFourierCoefficient_le a k L ha ha1 hk hL
    (schwartzTorusSample a k L ha1 hk hL K)
  simp_rw [schwartzTorusSample_coefficient a k L ha1 hk hL K] at hplain hbplain
  have hp := hbplain.trans (mul_le_mul_of_nonneg_left (hb L hL) (Real.sqrt_nonneg _))
  obtain ⟨hcomm, hbcomm⟩ := hd L hL
  have hterm (n : frequencyLattice) : latticeMomentMass L N (schwartzLatticeCoefficient L K) n ≤
      2 ^ N * (‖schwartzLatticeCoefficient L K n‖ + expandingCommutatorMoment L N (schwartzLatticeCoefficient L K) n) := by
    have h := mul_le_mul_of_nonneg_right
      (one_add_pow_le_commutator N (‖n‖ / L) (div_nonneg (norm_nonneg _) (by linarith)))
      (norm_nonneg (schwartzLatticeCoefficient L K n))
    dsimp only [latticeMomentMass, latticeMomentWeight, expandingCommutatorMoment]
    convert h using 1; ring
  have hsum := (hplain.add hcomm).mul_left ((2 : ℝ) ^ N)
  have hs := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (le_trans zero_le_one (latticeMomentWeight_one_le L hL N n)) (norm_nonneg _)) hterm hsum
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, 2 ^ N * (‖schwartzLatticeCoefficient L K n‖ + expandingCommutatorMoment L N (schwartzLatticeCoefficient L K) n) := hs.tsum_le_tsum hterm hsum
    _ = 2 ^ N * ((∑' n, ‖schwartzLatticeCoefficient L K n‖) + ∑' n, expandingCommutatorMoment L N (schwartzLatticeCoefficient L K) n) := by
      rw [tsum_mul_left, hplain.tsum_add hcomm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hp hbcomm) (by positivity)

end DefocusingNLS

end OAI
