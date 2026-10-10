import OAI.Geometry.RCD.Heat.GaussianHyperbolicComparison
import OAI.Geometry.RCD.Transport.HyperbolicChordLimit

namespace OAI

/-! # Exact continuous comparison, including zero curvature -/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem gaussian_hyperbolic_comparison_with_margin (u : ℝ → ℝ) {c q : ℝ}
    (hc : 0 ≤ c) (hq : 0 < q) (hcq : c < q^2)
    (hu : UpperSemicontinuousOn u (Icc 0 1))
    (hpos : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ u x)
    (hm : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      Real.exp (-c*(x-y)^2/8)*(u x+u y)/2 ≤ u ((x+y)/2))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : hyperbolicChord q (u 0) (u 1) t ≤ u t := by
  let d := (c+q^2)/2
  have hd0 : 0 < d := by dsimp [d]; nlinarith
  have hcd : c ≤ d := by dsimp [d]; linarith
  have hdq : d < q^2 := by dsimp [d]; linarith
  apply gaussian_hyperbolic_comparison u hd0 hq hdq hu (hpos 0 (by simp))
    (hpos 1 (by simp)) _ ht
  intro x hx y hy
  have he : Real.exp (-d*(x-y)^2/8) ≤ Real.exp (-c*(x-y)^2/8) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hcd (sq_nonneg (x-y))
    linarith
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right he (add_nonneg (hpos x hx) (hpos y hy))) (by norm_num)).trans
    (hm x hx y hy)

theorem gaussian_continuous_comparison (u : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hu : UpperSemicontinuousOn u (Icc 0 1))
    (hpos : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ u x)
    (hm : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      Real.exp (-c*(x-y)^2/8)*(u x+u y)/2 ≤ u ((x+y)/2))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (if c=0 then (1-t)*u 0+t*u 1 else hyperbolicChord (Real.sqrt c) (u 0) (u 1) t) ≤ u t := by
  by_cases hc0 : c=0
  · simp only [hc0, ↓reduceIte]
    have hlim := (tendsto_hyperbolicChord_zero (u 0) (u 1) t).mono_left (nhdsGT_le_nhdsNE 0)
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact gaussian_hyperbolic_comparison_with_margin u hc hq
      (by rw [hc0]; exact sq_pos_of_pos hq) hu hpos hm ht
  · simp only [hc0, ↓reduceIte]
    have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcpos
    have hlim : Tendsto (fun q : ℝ => hyperbolicChord q (u 0) (u 1) t)
        (𝓝[>] (Real.sqrt c)) (𝓝 (hyperbolicChord (Real.sqrt c) (u 0) (u 1) t)) :=
      (continuousAt_hyperbolicChord_parameter hs (u 0) (u 1) t).tendsto.mono_left
        nhdsWithin_le_nhds
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with q hq
    change Real.sqrt c < q at hq
    have hq0 : 0 < q := hs.trans hq
    have hq2 : c < q^2 := by nlinarith [Real.sq_sqrt hc]
    exact gaussian_hyperbolic_comparison_with_margin u hc hq0 hq2 hu hpos hm ht

end RegularPointCoordinates

end

end OAI
