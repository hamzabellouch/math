import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

theorem numeric_witness_scale_geometry {Z L s v d R : ℝ}
    (hZ : 2 ≤ Z) (hL : 1 ≤ L) (hs : 1 ≤ s) (hv : 1 ≤ v) (hd : 1 ≤ d)
    (hsL : s ≤ L^4) (hvL : v ≤ L) (hdL : d ≤ L)
    (hLZ : L ≤ Z^(1/50:ℝ)) (hRlo : Z^10 ≤ R) (hRhi : R ≤ Z^13) :
    let N := Real.sqrt (R/(s*v/d))
    let Y := N/d
    0 < Y ∧ Y^2 = R/(s*v*d) ∧ Z ≤ Y ∧ Real.log Y ≤ 7*Real.log Z ∧
      s*v*d ≤ Z^(3/25:ℝ) := by
  intro N Y
  have hZp : 0 < Z := by linarith
  have hspos : 0 < s := by linarith
  have hvpos : 0 < v := by linarith
  have hdpos : 0 < d := by linarith
  have hRpos : 0 < R := (pow_pos hZp 10).trans_le hRlo
  have hNpos : 0 < N := Real.sqrt_pos.mpr (by positivity)
  have hYpos : 0 < Y := div_pos hNpos hdpos
  have hSone : 1 ≤ s*v*d := by
    calc
      1 = 1*1*1 := by norm_num
      _ ≤ s*v*d := by gcongr
  have hSpos : 0 < s*v*d := by positivity
  have hN2 : N^2 = R/(s*v/d) := Real.sq_sqrt (by positivity)
  have hY2 : Y^2 = R/(s*v*d) := by
    change (N/d)^2 = _
    rw [div_pow,hN2]
    field_simp
  have hSL : s*v*d ≤ L^6 := by
    calc
      _ ≤ L^4*L*L := by gcongr
      _ = L^6 := by ring
  have hL6 : L^6 ≤ Z^(3/25:ℝ) := by
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ L) hLZ 6
    have he : (Z^(1/50:ℝ))^6 = Z^(3/25:ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hZp.le]
      norm_num
    rwa [he] at hp
  have hS : s*v*d ≤ Z^(3/25:ℝ) := hSL.trans hL6
  have hS8 : s*v*d ≤ Z^8 := by
    apply hS.trans
    convert Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Z)
      (by norm_num : (3/25:ℝ) ≤ 8) using 1
    norm_num
  have hZ2S : Z^2*(s*v*d) ≤ R := by
    calc
      _ ≤ Z^2*Z^8 := mul_le_mul_of_nonneg_left hS8 (sq_nonneg _)
      _ = Z^10 := by ring
      _ ≤ R := hRlo
  have hZY : Z ≤ Y := by
    have hh : Z^2 ≤ R/(s*v*d) := (le_div_iff₀ hSpos).mpr hZ2S
    rw [← hY2] at hh
    nlinarith
  have hYsqR : Y^2 ≤ R := by rw [hY2]; exact div_le_self hRpos.le hSone
  have hlog := Real.log_le_log (sq_pos_of_pos hYpos) (hYsqR.trans hRhi)
  rw [Real.log_pow,Real.log_pow] at hlog
  norm_num at hlog
  have hlogZ : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  exact ⟨hYpos,hY2,hZY,by linarith,hS⟩

end Ostmann.QuadraticCenter

end

end OAI
