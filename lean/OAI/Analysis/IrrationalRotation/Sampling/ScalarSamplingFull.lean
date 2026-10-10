import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingEstimates
import OAI.Analysis.IrrationalRotation.Analysis.ScalarRectangleDiscrepancy
import OAI.Analysis.IrrationalRotation.Analysis.ScalarBVDiscrepancy

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem SamplingPair.separated_pair {m : ℕ} {N₀ N : ℝ} {n n' : ℕ}
    (h : SamplingPair m N₀ N n n') (i j : ℤ)
    (hi : |i| ≤ (m ^ 300 : ℕ)) (hj : |j| ≤ (m ^ 300 : ℕ))
    (hij : (i, j) ≠ (0, 0)) :
    N * (m : ℝ)^1000 < |(i : ℝ) * n + (j : ℝ) * n'| := by
  apply h.separated i j hi hj
  by_cases hi0 : i = 0
  · exact Or.inr (fun hj0 => hij (by simp [hi0, hj0]))
  · exact Or.inl hi0

theorem rectangle_estimate {m : ℕ} (hm : 200 ≤ m) {N₀ N : ℝ} {n n' : ℕ}
    (h : SamplingPair m N₀ N n n') : RectangleEstimate m N₀ n n' 29 := by
  intro a b c d ha hab hb hc hcd hd
  have hr := ScalarRectangles.scalar_rectangles_ae m hm N₀ N h.N₀_pos h.N₀_le h.N_le
    n n' h.first_range.1 h.second_range.1 h.separated_pair
    a b c d ha hab hb hc hcd hd (Ico a b) (Ico c d) Ico_ae_eq_Icc Ico_ae_eq_Icc
  simpa [rectangleProbability, Real.rpow_neg (show (0 : ℝ) ≤ m by positivity), Real.rpow_ofNat, div_eq_mul_inv] using hr

theorem bv_estimate {m : ℕ} (hm : 200 ≤ m) {N₀ N : ℝ} {n n' : ℕ}
    (h : SamplingPair m N₀ N n n') : BVEstimate m N₀ n n' 29 := by
  intro f g hf hg
  have hr := ScalarRectangles.scalar_bv_discrepancy m hm N₀ N h.N₀_pos h.N₀_le h.N_le
    n n' h.first_range.1 h.second_range.1 h.separated_pair f g hf hg
  simpa [bvSize, Real.rpow_neg (show (0 : ℝ) ≤ m by positivity), Real.rpow_ofNat,
    div_eq_mul_inv] using hr

theorem full_scalar_sampling_estimates : ScalarSamplingEstimates := by
  refine ⟨all_kernel_estimates, all_marginal_estimates, 29, by norm_num,
    200, le_rfl, ?_⟩
  intro m hm N₀ N n n' h
  exact ⟨rectangle_estimate hm h, bv_estimate hm h⟩

end Invariant233.ScalarSampling

end

end OAI
