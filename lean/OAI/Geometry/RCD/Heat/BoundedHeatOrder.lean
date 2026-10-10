import OAI.Geometry.RCD.Heat.BoundedHeatRepresentative

namespace OAI

/-! # Pointwise order and linearity of the actual bounded heat flow -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {n : ℕ}

namespace HasBoundedAmplitude

variable {f g : Lp ℝ 2 (hausdorff n X)}

theorem add (hf : HasBoundedAmplitude f) (hg : HasBoundedAmplitude g) :
    HasBoundedAmplitude (f + g) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, ?_⟩
  filter_upwards [hC, hD, Lp.coeFn_add f g] with x hx hy he
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hx hy)

theorem smul (hf : HasBoundedAmplitude f) (c : ℝ) :
    HasBoundedAmplitude (c • f) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨⟨|c| * C, mul_nonneg (abs_nonneg _) C.coe_nonneg⟩, ?_⟩
  filter_upwards [hC, Lp.coeFn_smul c f] with x hx he
  rw [he]
  change |c * f x| ≤ |c| * C
  simpa only [abs_mul] using
    mul_le_mul_of_nonneg_left hx (abs_nonneg c)

end HasBoundedAmplitude

omit [BorelSpace X] in
private theorem continuous_le_of_ae {μ : Measure X} [μ.IsOpenPosMeasure]
    {f g : X → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f ≤ᵐ[μ] g) : ∀ x, f x ≤ g x := by
  have he : (fun x => min (f x) (g x)) = f :=
    Measure.eq_of_ae_eq (by filter_upwards [h] with x hx; exact min_eq_left hx)
      (hf.min hg) hf
  intro x
  exact min_eq_left_iff.mp (congrFun he x)

namespace NoncollapsedRCD

variable {K : ℝ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
  [ProperSpace X]
  [(hausdorff n X).Regular]

theorem boundedHeat_add (f g : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (hg : HasBoundedAmplitude g)
    (t : ℝ) (ht : 0 < t) :
    hX.boundedHeat hn p (f + g) (hf.add hg) t ht =
      hX.boundedHeat hn p f hf t ht + hX.boundedHeat hn p g hg t ht := by
  apply hX.boundedHeat_unique hn p
  · exact (hX.boundedHeat_continuous hn p f hf t ht).add
      (hX.boundedHeat_continuous hn p g hg t ht)
  · rw [map_add]
    filter_upwards [hX.boundedHeat_represents hn p f hf t ht,
      hX.boundedHeat_represents hn p g hg t ht,
      Lp.coeFn_add (heatAt (hausdorff n X) hX.quadratic t f)
        (heatAt (hausdorff n X) hX.quadratic t g)] with x hx hy he
    simp only [Pi.add_apply, he, hx, hy]

theorem boundedHeat_smul (f : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (c t : ℝ) (ht : 0 < t) :
    hX.boundedHeat hn p (c • f) (hf.smul c) t ht =
      c • hX.boundedHeat hn p f hf t ht := by
  apply hX.boundedHeat_unique hn p
  · exact (hX.boundedHeat_continuous hn p f hf t ht).const_smul c
  · rw [map_smul]
    filter_upwards [hX.boundedHeat_represents hn p f hf t ht,
      Lp.coeFn_smul c (heatAt (hausdorff n X) hX.quadratic t f)] with x hx he
    simp only [Pi.smul_apply, he, hx]

theorem boundedHeat_mono (f g : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (hg : HasBoundedAmplitude g)
    (t : ℝ) (ht : 0 < t) (hfg : f ≤ g) :
    ∀ x, hX.boundedHeat hn p f hf t ht x ≤ hX.boundedHeat hn p g hg t ht x := by
  let := hX.openPos K n
  apply continuous_le_of_ae (μ := hausdorff n X) (hX.boundedHeat_continuous hn p f hf t ht)
    (hX.boundedHeat_continuous hn p g hg t ht)
  filter_upwards [hX.boundedHeat_represents hn p f hf t ht,
    hX.boundedHeat_represents hn p g hg t ht,
    (Lp.coeFn_le _ _).mpr (heatAt_mono (hausdorff n X) hX.quadratic t hfg)] with x hx hy he
  simpa only [← hx, ← hy] using he

theorem boundedHeat_nonneg (f : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (t : ℝ) (ht : 0 < t) (hf0 : 0 ≤ f) :
    ∀ x, 0 ≤ hX.boundedHeat hn p f hf t ht x := by
  let := hX.openPos K n
  apply continuous_le_of_ae (μ := hausdorff n X) continuous_const (hX.boundedHeat_continuous hn p f hf t ht)
  filter_upwards [hX.boundedHeat_represents hn p f hf t ht,
    (Lp.coeFn_nonneg _).mpr (heatAt_nonneg (hausdorff n X) hX.quadratic t f hf0)] with x hx he
  simpa only [← hx, Pi.zero_apply] using he

theorem boundedHeat_abs_le (f : Lp ℝ 2 (hausdorff n X))
    (hf : HasBoundedAmplitude f) (t : ℝ) (ht : 0 < t)
    (C : ℝ≥0) (hC : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C) :
    ∀ x, |hX.boundedHeat hn p f hf t ht x| ≤ C := by
  let := hX.openPos K n
  apply continuous_le_of_ae (μ := hausdorff n X) (hX.boundedHeat_continuous hn p f hf t ht).abs continuous_const
  filter_upwards [hX.boundedHeat_represents hn p f hf t ht,
    heatAt_abs_le_const (hausdorff n X) hX.quadratic t C f hC] with x hx he
  simpa only [← hx, Pi.zero_apply] using he

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
