import OAI.NumberTheory.CubicMoment.Estimates.CoreIndexLogCount
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily

namespace OAI

/-! Explicit logarithmic choices for the low-height noncube moment. -/
noncomputable section
namespace CubicFirstMoment

lemma rpow_log_saving {N L H p s : ℝ} (hN : 0 < N) (hL : 0 < L)
    (k d : ℕ) (hlog : N^(-s)*L^(k+d) ≤ H) :
    N^(p-s)*L^d ≤ H*N^p/L^k := by
  apply (le_div_iff₀ (pow_pos hL k)).mpr
  rw [sub_eq_add_neg,Real.rpow_add hN]
  rw [pow_add] at hlog
  have hp := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hN.le p)
  nlinarith only [hp]

lemma logarithmic_core_cutoff {L : ℝ} (hL : 0 < L) (k : ℕ) :
    ((5832*L^(4*(k+2)))/5832)^(-(1/4:ℝ)) = 1/L^(k+2) := by
  rw [show (5832*L^(4*(k+2)))/5832 = L^(4*(k+2)) by ring,
    ←Real.rpow_natCast,←Real.rpow_mul hL.le]
  have he : ((4*(k+2):ℕ):ℝ)*(-(1/4:ℝ)) = -((k+2:ℕ):ℝ) := by push_cast; ring
  rw [he,Real.rpow_neg hL.le,Real.rpow_natCast,one_div]

lemma low_height_small_core_log_scale {N L T H : ℝ}
    (hN : 0 < N) (hL : 1 ≤ L) (k d : ℕ)
    (hT : L^(4*(k+2)+d+k) ≤ T)
    (hlog : N^(-(1:ℝ))*L^(4*(k+2)+d+k) ≤ H) :
    N*(1+N/T)*(5832*L^(4*(k+2)))*L^d ≤
      5832*(H+1)*N^2/L^k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hTp : 0 < T := (pow_pos hLp _).trans_le hT
  have ha : N*L^(4*(k+2)+d) ≤ H*N^2/L^k := by
    have hh := rpow_log_saving hN hLp k (4*(k+2)+d)
      (p := 2) (s := 1) (by simpa only [Nat.add_comm k] using hlog)
    norm_num at hh
    exact hh
  have hb : N^2/T*L^(4*(k+2)+d) ≤ N^2/L^k := by
    apply (le_div_iff₀ (pow_pos hLp k)).mpr
    calc
      _ = N^2*L^(4*(k+2)+d+k)/T := by rw [pow_add]; ring
      _ ≤ N^2 := (div_le_iff₀ hTp).mpr (mul_le_mul_of_nonneg_left hT (sq_nonneg N))
  have hab := add_le_add ha hb
  calc
    _ = 5832*(N*L^(4*(k+2)+d)+N^2/T*L^(4*(k+2)+d)) := by rw [pow_add]; ring
    _ ≤ 5832*(H*N^2/L^k+N^2/L^k) := mul_le_mul_of_nonneg_left hab (by norm_num)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
