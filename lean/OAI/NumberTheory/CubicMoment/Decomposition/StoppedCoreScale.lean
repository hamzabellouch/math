import OAI.NumberTheory.CubicMoment.Estimates.LowHeightLogScale

namespace OAI

/-! Scalar logarithmic absorption for the pointwise stopped-core sieve.
The power saving is measured at the coefficient length; its comparison
with the outer length is retained explicitly. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_core_cutoff {L : ℝ} (hL : 0 < L) (k : ℕ) :
    ((L^(4*(k+2)))/5832)^(-(1/4:ℝ)) = (5832:ℝ)^(1/4:ℝ)/L^(k+2) := by
  rw [Real.div_rpow (pow_nonneg hL.le _) (by norm_num : (0:ℝ) ≤ 5832),
    ←Real.rpow_natCast L (4*(k+2)),←Real.rpow_mul hL.le]
  have he : ((4*(k+2):ℕ):ℝ)*(-(1/4:ℝ)) = -((k+2:ℕ):ℝ) := by push_cast; ring
  rw [he,Real.rpow_neg hL.le,Real.rpow_natCast,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 5832)]
  field_simp

lemma stopped_large_core_scale {N L I C H : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hC : 0 ≤ C)
    (k : ℕ) (hcount : I ≤ C*L^2)
    (hpower : N^(-(1/20000:ℝ))*L^(k+2) ≤ H) :
    I*(N*((L^(4*(k+2)))/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*N ≤
      C*((5832:ℝ)^(1/4:ℝ)+H)*N^2/L^k := by
  have hmid : I*(N*((L^(4*(k+2)))/5832)^(-(1/4:ℝ)))*N ≤
      C*(5832:ℝ)^(1/4:ℝ)*N^2/L^k := by
    rw [stopped_core_cutoff hL k]
    calc
      _ ≤ (C*L^2)*(N*((5832:ℝ)^(1/4:ℝ)/L^(k+2)))*N := by gcongr
      _ = _ := by rw [pow_add]; field_simp
  have hp : N^(2-1/20000:ℝ)*L^2 ≤ H*N^2/L^k := by
    simpa only [Real.rpow_two,Nat.add_comm k 2] using
      (rpow_log_saving hN hL k 2 (p := 2) (s := 1/20000) hpower)
  have hmul : N^(1-1/20000:ℝ)*N = N^(2-1/20000:ℝ) := by
    nth_rw 2 [←Real.rpow_one N]
    rw [←Real.rpow_add hN]
    norm_num
  have hlarge : I*N^(1-1/20000:ℝ)*N ≤ C*H*N^2/L^k := by
    calc
      _ ≤ (C*L^2)*N^(1-1/20000:ℝ)*N := by gcongr
      _ = C*(N^(2-1/20000:ℝ)*L^2) := by rw [←hmul]; ring
      _ ≤ C*(H*N^2/L^k) := mul_le_mul_of_nonneg_left hp hC
      _ = _ := by ring
  calc
    _ = I*(N*((L^(4*(k+2)))/5832)^(-(1/4:ℝ)))*N+I*N^(1-1/20000:ℝ)*N := by ring
    _ ≤ C*(5832:ℝ)^(1/4:ℝ)*N^2/L^k+C*H*N^2/L^k := add_le_add hmid hlarge
    _ = _ := by ring

lemma stopped_length_log_power {X N κ : ℝ}
    (hX : 1 ≤ X) (hN : X^κ ≤ N) (k : ℕ) :
    N^(-(1/20000:ℝ))*(Real.log X)^(k+2) ≤
      X^(-(κ/20000))*(1+Real.log X)^(k+2) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXp κ) hN
    (by norm_num : -(1/20000:ℝ) ≤ 0)
  rw [←Real.rpow_mul hXp.le] at hp
  have he : κ*(-(1/20000:ℝ)) = -(κ/20000) := by ring
  rw [he] at hp
  exact mul_le_mul hp
    (pow_le_pow_left₀ (Real.log_nonneg hX) (by linarith) _)
    (pow_nonneg (Real.log_nonneg hX) _) (Real.rpow_nonneg hXp.le _)

end CubicFirstMoment

end

end OAI
