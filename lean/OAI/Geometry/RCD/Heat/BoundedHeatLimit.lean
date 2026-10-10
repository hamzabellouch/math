import OAI.Geometry.RCD.Sobolev.UniformLipschitzL2Limit

namespace OAI

/-! # Pointwise continuity of bounded-data heat evaluation in the L² topology -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem boundedHeat_sub (f g : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (hg : HasBoundedAmplitude g)
    (hsub : HasBoundedAmplitude (f - g)) (t : ℝ) (ht : 0 < t) :
    hX.boundedHeat hn p (f - g) hsub t ht =
      hX.boundedHeat hn p f hf t ht - hX.boundedHeat hn p g hg t ht := by
  apply hX.boundedHeat_unique hn p
  · exact (hX.boundedHeat_continuous hn p f hf t ht).sub
      (hX.boundedHeat_continuous hn p g hg t ht)
  · rw [map_sub]
    filter_upwards [hX.boundedHeat_represents hn p f hf t ht,
      hX.boundedHeat_represents hn p g hg t ht,
      Lp.coeFn_sub (heatAt (hausdorff n X) hX.quadratic t f)
        (heatAt (hausdorff n X) hX.quadratic t g)] with x hx hy he
    simp only [Pi.sub_apply, he, hx, hy]

theorem boundedHeat_tendsto (f : ℕ → Lp ℝ 2 (hausdorff n X))
    (g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf : ∀ i, ∀ᵐ x ∂hausdorff n X, |f i x| ≤ C)
    (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ C)
    (hlim : Tendsto f atTop (𝓝 g)) (t : ℝ) (ht : 0 < t) (x : X) :
    Tendsto (fun i => hX.boundedHeat hn p (f i) ⟨C, hf i⟩ t ht x) atTop
      (𝓝 (hX.boundedHeat hn p g ⟨C, hg⟩ t ht x)) := by
  have hb (i : ℕ) : ∀ᵐ y ∂hausdorff n X, |(f i - g) y| ≤ (2 * C : ℝ≥0) := by
    filter_upwards [hf i, hg, Lp.coeFn_sub (f i) g] with y hy hz he
    rw [he]
    have hh := (abs_sub (f i y) (g y)).trans (add_le_add hy hz)
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, two_mul, Pi.sub_apply] using! hh
  have hzero : Tendsto (fun i => f i - g) atTop (𝓝 0) := by
    simpa only [sub_self] using hlim.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => g) atTop (𝓝 g))
  have h := hX.boundedHeat_tendsto_zero hn p (fun i => f i - g) (2 * C) hb hzero t ht x
  have he (i : ℕ) : hX.boundedHeat hn p (f i - g) ⟨2 * C, hb i⟩ t ht x =
      hX.boundedHeat hn p (f i) ⟨C, hf i⟩ t ht x -
        hX.boundedHeat hn p g ⟨C, hg⟩ t ht x :=
    congrFun (hX.boundedHeat_sub hn p (f i) g ⟨C, hf i⟩ ⟨C, hg⟩ ⟨2 * C, hb i⟩ t ht) x
  simpa only [he, sub_add_cancel, zero_add] using h.add_const (hX.boundedHeat hn p g ⟨C, hg⟩ t ht x)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
