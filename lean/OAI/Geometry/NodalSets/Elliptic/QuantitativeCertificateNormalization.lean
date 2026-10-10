import OAI.Geometry.NodalSets.Hausdorff.SeedWindowNodalLower

namespace OAI

namespace Yau.Target
open scoped ENNReal
noncomputable section

theorem quantitative_certificate_window_ratio {n : ℕ} (hn : 0 < n)
    {L T M mu : ℝ} (hL : 0 < L) (hT : 0 < T) (hgain : 8*(n:ℝ)*L*T < M)
    (hmu : 0 < mu) (hupper : mu ≤ 2*seedEigenvalue n)
    {m : ℝ≥0∞} (hm : ENNReal.ofReal (M/L) ≤ m) :
    ENNReal.ofReal T < m / ENNReal.ofReal (Real.sqrt mu) := by
  have hs := Real.sqrt_pos.mpr hmu
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hs)))
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [← ENNReal.ofReal_mul hT.le]
  apply ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hT.le hs.le)).mpr ?_).trans_le hm
  apply (lt_div_iff₀ hL).mpr
  have hbound := mul_le_mul_of_nonneg_left (seed_window_sqrt_bound hn hupper) hT.le
  have hbound' := mul_le_mul_of_nonneg_right hbound hL.le
  nlinarith only [hbound',hgain]

end
end Yau.Target

end OAI
