import OAI.MeasureTheory.Falconer.Fourier.UniformSymbolScale
import OAI.MeasureTheory.Falconer.Angular.ActualFullCircleStationary

namespace OAI

namespace PlanarFalconer

 theorem sourceSymbolScale_dyadic (N : ℕ) (sig : ℝ) (L : ℕ) :
    sourceSymbolScale N sig L =
      max ((2:ℝ)^((N:ℝ)*sig)) ((2:ℝ)^((L:ℝ)-49*(N:ℝ)*sig)) := by
  unfold sourceSymbolScale
  rw [mul_max_of_nonneg _ _ (by positivity),mul_one]
  congr 1
  · exact (Real.rpow_natCast_mul (by norm_num) N sig).symm
  · rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),← Real.rpow_natCast]
    rw [← mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring

 theorem sourceSymbolScale_far_square {sig L₀ : ℝ} (hsig : 0 ≤ sig)
    (N L : ℕ) (hL : (L:ℝ) ≤ L₀) (hL₀ : 10*sig*(N:ℝ) ≤ L₀) :
    sourceSymbolScale N sig L^2 ≤ (2:ℝ)^(2*L₀)*((2:ℝ)^N)^(-18*sig) := by
  have hn : 0 ≤ (N:ℝ)*sig := mul_nonneg (Nat.cast_nonneg _) hsig
  have hbase : sourceSymbolScale N sig L ≤ (2:ℝ)^(L₀-9*(N:ℝ)*sig) := by
    rw [sourceSymbolScale_dyadic]
    apply max_le
    · apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      nlinarith
    · apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      nlinarith
  apply (pow_le_pow_left₀ (sourceSymbolScale_pos N sig L).le hbase 2).trans_eq
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

 theorem actual_far_stationary_slack {sig L₀ Λ : ℝ} (hsig : 0 ≤ sig)
    (N L : ℕ) (hL : (L:ℝ) ≤ L₀) (hL₀ : 10*sig*(N:ℝ) ≤ L₀)
    (hΛ : (2:ℝ)^(2*L₀) ≤ Λ) :
    ((2:ℝ)^N)^(18*sig) ≤ Λ ∧
      sourceSymbolScale N sig L^2/Λ ≤ ((2:ℝ)^N)^(-18*sig) := by
  have hΛpos : 0 < Λ := (by positivity : (0:ℝ) < (2:ℝ)^(2*L₀)).trans_le hΛ
  refine ⟨?_,(div_le_iff₀ hΛpos).mpr ?_⟩
  · apply le_trans _ hΛ
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    nlinarith [mul_nonneg (Nat.cast_nonneg N) hsig]
  · exact (sourceSymbolScale_far_square hsig N L hL hL₀).trans
      (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hΛ (by positivity : 0 ≤ ((2:ℝ)^N)^(-18*sig)))

 theorem far_bump_frequency {v h L₀ d s : ℝ} (hv : v-h = 2*L₀)
    (hd : 4*(2:ℝ)^(-h) ≤ d) (hs : 1/4 ≤ s) :
    (2:ℝ)^(2*L₀) ≤ (2:ℝ)^v*s*d := by
  have hdpos : 0 < d := (by positivity : 0 < 4*(2:ℝ)^(-h)).trans_le hd
  calc
    _ = (2:ℝ)^v*(1/4)*(4*(2:ℝ)^(-h)) := by
      rw [← hv,sub_eq_add_neg,Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hd
      (by positivity) (by positivity)

end PlanarFalconer

end OAI
