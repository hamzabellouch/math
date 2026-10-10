import OAI.Analysis.CircleDomains.Sobolev.CompactMollifierSampling

namespace OAI

/-! Positive mollification approximates a continuous branch uniformly on
a compact set strictly inside its domain of continuity. -/

open Set Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem planarMollification_uniform_on_compact
    {u : EuclideanPlane → ℝ} (hu : AEStronglyMeasurable u volume)
    {K V : Set EuclideanPlane} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (hc : ContinuousOn u V) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K, |planarMollification u n x - u x| < ε := by
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  have huc := (hK.cthickening (r := r)).uniformContinuousOn_of_continuous (hc.mono hrV)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (half_pos hε)
  have hrad : ∀ᶠ n in atTop, (DeGiorgi.shrinkingBump (d := 2) n).rOut < min r δ :=
    (tendsto_order.mp tendsto_planarMollifier_radius).2 _ (lt_min hr hδ)
  filter_upwards [hrad] with n hn x hx
  have hb : ∀ y ∈ ball x (DeGiorgi.shrinkingBump (d := 2) n).rOut,
      dist (u y) (u x) ≤ ε / 2 := by
    intro y hy
    have hyx : dist y x < min r δ := (mem_ball.mp hy).trans hn
    exact (hd y (mem_cthickening_of_dist_le y x r K hx (lt_of_lt_of_le hyx (min_le_left _ _)).le)
      x (self_subset_cthickening K hx) (lt_of_lt_of_le hyx (min_le_right _ _))).le
  have he := (DeGiorgi.shrinkingBump (d := 2) n).dist_normed_convolution_le hu hb
  exact (show |planarMollification u n x - u x| ≤ ε / 2 by
    simpa only [planarMollification, Real.dist_eq] using he).trans_lt (half_lt_self hε)

end CircleDomainRigidity

end

end OAI
