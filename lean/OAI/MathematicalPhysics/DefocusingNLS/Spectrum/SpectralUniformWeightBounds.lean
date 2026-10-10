import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralContinuousWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralUniformError

namespace OAI

/-! A positive limiting density supplies uniform coercivity of its nearby weights. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralUniform_positive_bounds (R : ℝ) (q : ℕ → ℝ → ℝ) (q₀ : ℝ → ℝ)
    (hq₀ : ContinuousOn q₀ (Icc 0 R)) (hp : ∀ r ∈ Icc 0 R, 0 < q₀ r)
    (hlim : TendstoUniformlyOn q q₀ atTop (Icc 0 R)) :
    ∃ c M : ℝ, 0 < c ∧ 0 ≤ M ∧
      (∀ r ∈ Icc 0 R, c ≤ q₀ r ∧ ‖q₀ r‖ ≤ M) ∧
      ∀ᶠ n in atTop, ∀ r ∈ Icc 0 R, c ≤ q n r ∧ ‖q n r‖ ≤ M := by
  obtain ⟨c,hc,hc₀⟩ := isCompact_Icc.exists_forall_le' hq₀ hp
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image hq₀.norm
  let M := max 0 B+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbn (r : ℝ) (hr : r ∈ Icc 0 R) : ‖q₀ r‖ ≤ B := hB ⟨r,hr,rfl⟩
  refine ⟨c/2,M,half_pos hc,hM,?_,?_⟩
  · intro r hr
    exact ⟨(half_le_self hc.le).trans (hc₀ r hr),
      (hbn r hr).trans (by dsimp [M]; linarith [le_max_right (0 : ℝ) B])⟩
  · have he := (Metric.tendstoUniformlyOn_iff.mp hlim) (min (c/2) 1)
      (lt_min (half_pos hc) zero_lt_one)
    filter_upwards [he] with n hn r hr
    have hd : ‖q n r-q₀ r‖ < min (c/2) 1 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hn r hr
    constructor
    · have hx := (le_abs_self (q₀ r-q n r)).trans (le_of_lt (by
        simpa only [Real.norm_eq_abs,abs_sub_comm] using hd))
      have hy := hc₀ r hr
      have hz := min_le_left (c/2) (1 : ℝ)
      linarith
    · have ht := norm_le_norm_sub_add (q n r) (q₀ r)
      have hz := min_le_right (c/2) (1 : ℝ)
      have hb := hbn r hr
      dsimp only [M]
      linarith [le_max_right (0 : ℝ) B]

end DefocusingNLS

end OAI
