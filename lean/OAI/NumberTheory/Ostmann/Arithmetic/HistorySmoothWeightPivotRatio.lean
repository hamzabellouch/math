import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCutoff
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPivot

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic

theorem pivot_numerator_ratio_le (s v : ℤ) (H u p G T Δ E WH Wu : ℝ)
    (hs : s ≠ 0) (hH : 0 < H) (hu : 0 < u) (hp : 0 < p)
    (hv : |(v:ℝ)| ≤ Real.exp E)
    (hlogH : Real.log H ≤ G + T + Δ + WH)
    (hlogu : T - Wu ≤ Real.log u) (hlogp : G - 1 ≤ Real.log p) :
    |(v:ℝ) * H / ((s:ℝ) * u * p)| ≤ Real.exp (E + Δ + WH + Wu + 1) := by
  have hs1 : (1:ℝ) ≤ |(s:ℝ)| := by exact_mod_cast Int.one_le_abs hs
  have hspos : 0 < |(s:ℝ)| := lt_of_lt_of_le zero_lt_one hs1
  have hHs : H ≤ Real.exp (G + T + Δ + WH) := (Real.log_le_iff_le_exp hH).mp hlogH
  have hus : Real.exp (T - Wu) ≤ u := (Real.le_log_iff_exp_le hu).mp hlogu
  have hps : Real.exp (G - 1) ≤ p := (Real.le_log_iff_exp_le hp).mp hlogp
  have hden : Real.exp (T - Wu) * Real.exp (G - 1) ≤ |(s:ℝ)| * u * p := by
    calc
      _ ≤ u * p := mul_le_mul hus hps (Real.exp_pos _).le hu.le
      _ ≤ _ := by nlinarith [mul_pos hu hp]
  rw [abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos hH,abs_of_pos hu,abs_of_pos hp]
  calc
    _ ≤ (Real.exp E * Real.exp (G + T + Δ + WH)) /
        (Real.exp (T - Wu) * Real.exp (G - 1)) :=
      div_le_div₀ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        (mul_le_mul hv hHs hH.le (Real.exp_pos _).le)
        (mul_pos (Real.exp_pos _) (Real.exp_pos _)) hden
    _ = _ := by
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_sub]
      congr 1
      ring

end Ostmann.Arithmetic

end

end OAI
