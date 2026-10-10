import OAI.NumberTheory.CubicMoment.Estimates.LowPoissonScale
import OAI.NumberTheory.CubicMoment.Estimates.LowHeightLogScale

namespace OAI

noncomputable section
namespace CubicFirstMoment

lemma low_poisson_tail_log_scale (k : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ A N : ℝ, 1 ≤ A → 1 ≤ N →
      N^(-1:ℝ) ≤ D*A^(2/3:ℝ)*N^(5/3:ℝ)/(1+Real.log N)^k := by
  obtain ⟨D,hD,hbound⟩ := log_power_normalization_bound k (by norm_num : (0:ℝ) < 1)
  refine ⟨D+1,by positivity,?_⟩
  intro A N hA hN
  have hL : 0 < 1+Real.log N := by linarith [Real.log_nonneg hN]
  have hbase : N^(-1:ℝ) ≤ D/(1+Real.log N)^k := by
    apply (le_div_iff₀ (pow_pos hL _)).mpr
    simpa only [neg_mul,one_mul] using hbound N hN
  have hprod : 1 ≤ A^(2/3:ℝ)*N^(5/3:ℝ) :=
    by
      have ha := Real.one_le_rpow hA (show (0:ℝ) ≤ 2/3 by norm_num)
      have hn := Real.one_le_rpow hN (show (0:ℝ) ≤ 5/3 by norm_num)
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hn)]
  apply hbase.trans
  apply le_trans ?_ (show D*A^(2/3:ℝ)*N^(5/3:ℝ)/(1+Real.log N)^k ≤
      (D+1)*A^(2/3:ℝ)*N^(5/3:ℝ)/(1+Real.log N)^k by gcongr; linarith)
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ D/(1+Real.log N)^k by positivity)
  convert hh using 1 <;> ring

end CubicFirstMoment

end

end OAI
