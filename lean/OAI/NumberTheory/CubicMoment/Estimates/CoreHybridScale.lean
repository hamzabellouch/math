import OAI.NumberTheory.CubicMoment.Estimates.SmallBHeightPowers

namespace OAI

/-! Numerical comparisons for the ordinary/large-core split. -/
noncomputable section
namespace CubicFirstMoment

lemma core_ordinary_range {N D : ℝ} (hN : 65536 ≤ N) (hD : 0 ≤ D)
    (hsmall : D ≤ N^(1/1000:ℝ)) : (8*D)^2 ≤ N := by
  have hN1 : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hp := pow_le_pow_left₀ hD hsmall 2
  rw [←Real.rpow_natCast (N^(1/1000:ℝ)) 2,←Real.rpow_mul hNp.le] at hp
  norm_num only [Nat.cast_ofNat,mul_comm (1/1000:ℝ),show (2:ℝ)*(1/1000) = 1/500 by norm_num] at hp
  have hroot : N^(1/500:ℝ) ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hs : 64 ≤ Real.sqrt N := by
    have hb := Real.sqrt_le_sqrt hN
    norm_num at hb
    linarith
  have hsq := Real.sq_sqrt hNp.le
  have hd : D^2 ≤ Real.sqrt N := hp.trans hroot
  nlinarith

lemma core_large_range {N D : ℝ} (hN : 1 ≤ N)
    (hD : N^(1/1000:ℝ) ≤ D) :
    N^(2*(1/10000):ℝ)*(N/D^(1/3:ℝ)+N^(23/24:ℝ)) ≤
      2*N^(1-1/20000:ℝ) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hlow : (N^(1/1000:ℝ))^(1/3:ℝ) ≤ D^(1/3:ℝ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hNp.le _) hD (by norm_num)
  rw [←Real.rpow_mul hNp.le] at hlow
  norm_num only [show (1/1000:ℝ)*(1/3) = 1/3000 by norm_num] at hlow
  have hratio : N/D^(1/3:ℝ) ≤ N^(1-1/3000:ℝ) := by
    calc
      _ ≤ N/N^(1/3000:ℝ) := div_le_div_of_nonneg_left hNp.le (Real.rpow_pos_of_pos hNp _) hlow
      _ = _ := by nth_rw 1 [←Real.rpow_one N]; rw [←Real.rpow_sub hNp]
  calc
    _ ≤ N^(2*(1/10000):ℝ)*(N^(1-1/3000:ℝ)+N^(23/24:ℝ)) := by gcongr
    _ = N^(2*(1/10000)+(1-1/3000):ℝ)+N^(2*(1/10000)+23/24:ℝ) := by
      rw [mul_add,←Real.rpow_add hNp,←Real.rpow_add hNp]
    _ ≤ N^(1-1/20000:ℝ)+N^(1-1/20000:ℝ) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
        (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
