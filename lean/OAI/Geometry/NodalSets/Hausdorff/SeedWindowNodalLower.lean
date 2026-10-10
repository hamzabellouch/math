import OAI.Geometry.NodalSets.Hausdorff.EnvelopeNodalGain

namespace OAI

namespace Yau.Target
open scoped ENNReal
noncomputable section

lemma seed_window_sqrt_bound {n : ℕ} (hn : 0 < n) {lam : ℝ}
    (hlam : lam ≤ 2*seedEigenvalue n) : Real.sqrt lam ≤ 8*(n:ℝ) := by
  have h : (1:ℝ) ≤ n := by exact_mod_cast hn
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · unfold seedEigenvalue at hlam
    nlinarith

lemma normalized_seed_window_nodal_lower {n : ℕ} (hn : 0 < n) {c I lam : ℝ}
    (hc : 0 ≤ c) (hI : 0 ≤ I) (hlam : 0 < lam) (hupper : lam ≤ 2*seedEigenvalue n)
    {M : ℝ≥0∞} (hM : ENNReal.ofReal (c*((n:ℝ)*I)) ≤ M) :
    ENNReal.ofReal (c*I/8) ≤ M / ENNReal.ofReal (Real.sqrt lam) := by
  have hsqrt := Real.sqrt_pos.mpr hlam
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hsqrt)))
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply (ENNReal.ofReal_le_ofReal ?_).trans hM
  have h := mul_le_mul_of_nonneg_left (seed_window_sqrt_bound hn hupper)
    (show 0 ≤ c*I/8 by positivity)
  nlinarith

end
end Yau.Target

end OAI
