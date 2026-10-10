import OAI.Geometry.NodalSets.Waves.UniformActualWaveSize

namespace OAI

noncomputable section

namespace Yau.Geometry

open Filter
open scoped Topology

lemma half_scale_square {N : ℝ} (hN : 0 < N) : (N^(-1/2:ℝ))^2 = N⁻¹ := by
  rw [← Real.rpow_mul_natCast hN.le]
  norm_num
  exact Real.rpow_neg_one N

lemma inverse_le_half_scale {N : ℝ} (hN : 1 ≤ N) : N⁻¹ ≤ N^(-1/2:ℝ) := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)

lemma half_scale_eventually (L D delta : ℝ) (hd : 0 < delta) :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧ L*N^(-1/2:ℝ) ≤ delta ∧
      D*(L*N^(-1/2:ℝ)) < N^(-1/3:ℝ) := by
  have hsmall : Tendsto (fun N : ℝ ↦ L*N^(-1/2:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).const_mul L
  have hcut : Tendsto (fun N : ℝ ↦ (D*L)*N^(-1/6:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/6)).const_mul (D*L)
  filter_upwards [eventually_ge_atTop (1:ℝ),hsmall.eventually (gt_mem_nhds hd),
    hcut.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with N hN hs hc
  refine ⟨hN,hs.le,?_⟩
  have hp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have he : N^(-1/2:ℝ) = N^(-1/6:ℝ)*N^(-1/3:ℝ) := by
    rw [← Real.rpow_add hp]; norm_num
  rw [he]
  have hh := mul_lt_mul_of_pos_right hc (Real.rpow_pos_of_pos hp (-1/3:ℝ))
  simpa [mul_assoc] using hh

lemma main_scale_square {N : ℝ} (hN : 0 < N) : (N^(-5/12:ℝ))^2 = N^(-5/6:ℝ) := by
  rw [← Real.rpow_mul_natCast hN.le]
  norm_num

lemma inverse_le_main_scale {N : ℝ} (hN : 1 ≤ N) : N⁻¹ ≤ N^(-5/12:ℝ) := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)

lemma main_scale_eventually (L D delta : ℝ) (hd : 0 < delta) :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧ L*N^(-5/12:ℝ) ≤ delta ∧
      D*(L*N^(-5/12:ℝ)) < N^(-1/3:ℝ) := by
  have hsmall : Tendsto (fun N : ℝ ↦ L*N^(-5/12:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/12)).const_mul L
  have hcut : Tendsto (fun N : ℝ ↦ (D*L)*N^(-1/12:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/12)).const_mul (D*L)
  filter_upwards [eventually_ge_atTop (1:ℝ),hsmall.eventually (gt_mem_nhds hd),
    hcut.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with N hN hs hc
  refine ⟨hN,hs.le,?_⟩
  have hp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have he : N^(-5/12:ℝ) = N^(-1/12:ℝ)*N^(-1/3:ℝ) := by
    rw [← Real.rpow_add hp]; norm_num
  rw [he]
  have hh := mul_lt_mul_of_pos_right hc (Real.rpow_pos_of_pos hp (-1/3:ℝ))
  simpa [mul_assoc] using hh

lemma inverse_le_main_scale_square {N : ℝ} (hN : 1 ≤ N) : N⁻¹ ≤ N^(-5/6:ℝ) := by
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)

end Yau.Geometry

end

end OAI
