import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzTorusSampling
import Mathlib.Analysis.Real.Pi.Bounds

namespace OAI

/-! # A summable bound for Schwartz samples on bounded radius intervals -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem schwartz_scaled_squared_decay (K : 𝓢(E, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (L : ℝ), 1 ≤ L → L ≤ M → ∀ n : frequencyLattice,
      ‖K (L⁻¹ • (n : E))‖ ^ 2 ≤ D * ((1 + ‖n‖ ^ 2) ^ (12 : ℕ))⁻¹ := by
  let C := SchwartzMap.seminorm ℝ 0 0 (weightedSchwartzKernel 12 K)
  have hC : 0 ≤ C := apply_nonneg _ _
  refine ⟨M ^ (24 : ℕ) * C ^ 2, by positivity, fun L hL hLM n => ?_⟩
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let x := L⁻¹ • (n : E)
  have hx : L * ‖x‖ = ‖n‖ := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hLp, Submodule.norm_coe,
      ← mul_assoc, mul_inv_cancel₀ hLp.ne', one_mul]
  have hbase : 1 + ‖n‖ ^ 2 ≤ M ^ 2 * (1 + ‖x‖ ^ 2) := by
    have hsq : L ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hLp.le hLM 2
    have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖x‖)
    have hx2 := congrArg (fun r : ℝ => r ^ 2) hx
    rw [mul_pow] at hx2
    nlinarith [sq_nonneg (M - 1)]
  have hb : (1 + ‖x‖ ^ 2) ^ (6 : ℕ) * ‖K x‖ ≤ C := by
    have h := SchwartzMap.norm_le_seminorm ℝ (weightedSchwartzKernel 12 K) x
    rw [weightedSchwartzKernel_norm] at h
    norm_num at h
    exact h
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + ‖x‖ ^ 2) ^ (6 : ℕ) * ‖K x‖) hb 2
  have hs' : (1 + ‖x‖ ^ 2) ^ (12 : ℕ) * ‖K x‖ ^ 2 ≤ C ^ 2 := by nlinarith [hs]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖n‖ ^ 2) hbase 12
  have hp' : (1 + ‖n‖ ^ 2) ^ (12 : ℕ) ≤ M ^ (24 : ℕ) * (1 + ‖x‖ ^ 2) ^ (12 : ℕ) := by
    simpa only [mul_pow, ← pow_mul, show 2 * 12 = 24 by norm_num] using hp
  apply (le_mul_inv_iff₀ (by positivity : 0 < (1 + ‖n‖ ^ 2) ^ (12 : ℕ))).mpr
  calc
    _ ≤ M ^ (24 : ℕ) * ((1 + ‖x‖ ^ 2) ^ (12 : ℕ) * ‖K x‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hp' (sq_nonneg ‖K x‖)]
    _ ≤ M ^ (24 : ℕ) * C ^ 2 := mul_le_mul_of_nonneg_left hs' (pow_nonneg hMp.le _)

theorem weightedSchwartzKernel_norm_sq (s : ℝ) (K : 𝓢(E, ℂ)) (x : E) :
    ‖weightedSchwartzKernel s K x‖ ^ 2 = (1 + ‖x‖ ^ 2) ^ s * ‖K x‖ ^ 2 := by
  rw [weightedSchwartzKernel_norm, mul_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  norm_num

theorem schwartzTorusSample_local_bound (a k M : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (hM : 1 ≤ M) (K : 𝓢(E, ℂ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (L : ℝ) (hL : 1 ≤ L), L ≤ M → ∀ n : frequencyLattice,
      ‖schwartzTorusSample a k L ha1 hk hL K n‖ ^ 2 ≤
        D * ((1 + ‖n‖ ^ 2) ^ (12 : ℕ))⁻¹ := by
  obtain ⟨D₀, hD₀, hb₀⟩ := schwartz_scaled_squared_decay (weightedSchwartzKernel (6 - a) K) M hM
  obtain ⟨D₁, hD₁, hb₁⟩ := schwartz_scaled_squared_decay (weightedSchwartzKernel k K) M hM
  refine ⟨D₀ + D₁, add_nonneg hD₀ hD₁, fun L hL hLM n => ?_⟩
  let x := L⁻¹ • (n : E)
  have hx : ‖x‖ = ‖n‖ / L := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (lt_of_lt_of_le zero_lt_one hL),
      Submodule.norm_coe, div_eq_inv_mul]
  have hlo : (L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) ≤ (1 + ‖x‖ ^ 2) ^ (6 - a) := by
    rw [hx]
    exact Real.rpow_le_rpow (by positivity)
      (add_le_add (Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)) le_rfl) (by linarith)
  have hhi : (‖n‖ / L) ^ (2 * k) ≤ (1 + ‖x‖ ^ 2) ^ k := by
    rw [hx]
    calc
      _ = ((‖n‖ / L) ^ (2 : ℕ)) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hvol : ((2 * Real.pi * L) ^ (12 : ℕ))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    apply one_le_pow₀
    nlinarith [Real.pi_gt_three]
  have hcoef : ‖schwartzTorusSample a k L ha1 hk hL K n‖ ^ 2 ≤
      ‖weightedSchwartzKernel (6 - a) K x‖ ^ 2 + ‖weightedSchwartzKernel k K x‖ ^ 2 := by
    change ‖weightedSchwartzLatticeCoefficient a k L K n‖ ^ 2 ≤ _
    rw [weightedSchwartzLatticeCoefficient_norm_sq a k L hL,
      weightedSchwartzKernel_norm_sq, weightedSchwartzKernel_norm_sq]
    calc
      _ ≤ ((1 + ‖x‖ ^ 2) ^ (6 - a) + (1 + ‖x‖ ^ 2) ^ k) * ‖K x‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact (mul_le_mul_of_nonneg_left (add_le_add hlo hhi) (by positivity)).trans
          (mul_le_of_le_one_left (by positivity) hvol)
      _ = _ := by ring
  exact hcoef.trans (by simpa only [add_mul] using add_le_add (hb₀ L hL hLM n) (hb₁ L hL hLM n))

end DefocusingNLS

end OAI
