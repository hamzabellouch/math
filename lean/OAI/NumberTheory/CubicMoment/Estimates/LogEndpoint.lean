import OAI.NumberTheory.CubicMoment.Estimates.FourierCutoff

namespace OAI

/-!
# From logarithmic boundary distance to integer norm distance

This is the missing metric step between Fourier smoothing in log norm and
the summable endpoint kernel in the norm variable.
-/

noncomputable section

namespace CubicFirstMoment

private theorem sub_le_mul_log_sub {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    v-w ≤ v * (Real.log v - Real.log w) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hv hw)
  rw [inv_div, Real.log_div hv.ne' hw.ne'] at h
  have h' := mul_le_mul_of_nonneg_left h hv.le
  have he : v * (1 - w/v) = v-w := by field_simp
  rwa [he] at h'

theorem abs_sub_le_four_mul_log_distance {v w : ℝ}
    (hv : 0 < v) (hw : 0 < w) (hv4 : v ≤ 4) (hw4 : w ≤ 4) :
    |v-w| ≤ 4 * |Real.log v - Real.log w| := by
  have hord : ∀ {v w : ℝ}, 0 < v → 0 < w → v ≤ 4 → w ≤ v →
      |v-w| ≤ 4 * |Real.log v - Real.log w| := by
    intro v w hv hw hv4 hwv
    have hl : 0 ≤ Real.log v - Real.log w := sub_nonneg.mpr (Real.log_le_log hw hwv)
    rw [abs_of_nonneg (sub_nonneg.mpr hwv), abs_of_nonneg hl]
    exact (sub_le_mul_log_sub hv hw).trans (mul_le_mul_of_nonneg_right hv4 hl)
  rcases le_total w v with h | h
  · exact hord hv hw hv4 h
  · rw [abs_sub_comm v w, abs_sub_comm (Real.log v) (Real.log w)]
    exact hord hw hv hw4 h

private theorem reciprocal_sq_le_endpoint {h d r : ℝ}
    (hh : 0 < h) (hd : 0 ≤ d) (hr : 0 ≤ r) (hdis : d ≤ 4*h*r) :
    1 / (1+r)^2 ≤ 16 * (h^2 / (h+d)^2) := by
  rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos (by positivity))
    (sq_pos_of_pos (by positivity))]
  have hsum : h+d ≤ 4*h*(1+r) := by nlinarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ h+d) hsum 2
  nlinarith only [hs]

/-- On the fixed norm envelope, the Fourier boundary majorant is at most
an absolute constant times the summable integer endpoint kernel. -/
theorem log_boundary_le_endpoint {X T n b : ℝ}
    (hX : 0 < X) (hT : 0 < T) (hn : 0 < n) (hn4 : n ≤ 4*X)
    (hb : 0 < b) (hb4 : b ≤ 4) :
    1 / (1 + T*|Real.log (n/X) - Real.log b|)^2 ≤
      16 * endpointKernel (X/T) (n - b*X) := by
  have hdist := abs_sub_le_four_mul_log_distance (div_pos hn hX) hb
    ((div_le_iff₀ hX).mpr hn4) hb4
  have hid : |n - b*X| = X * |n/X-b| := by
    calc
      |n - b*X| = |X*(n/X-b)| := by congr 1; field_simp
      _ = |X| * |n/X-b| := abs_mul _ _
      _ = X * |n/X-b| := by rw [abs_of_pos hX]
  have hdis : |n-b*X| ≤ 4*(X/T)*(T*|Real.log (n/X)-Real.log b|) := by
    rw [hid]
    have he : 4*(X/T)*(T*|Real.log (n/X)-Real.log b|) =
        X*(4*|Real.log (n/X)-Real.log b|) := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hdist hX.le
  exact reciprocal_sq_le_endpoint (div_pos hX hT) (abs_nonneg _) (by positivity) hdis

end CubicFirstMoment

end

end OAI
