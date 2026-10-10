import OAI.Geometry.RCD.Transport.DimensionalExpansion
import OAI.Geometry.RCD.Metric.EvolutionInitialLimit

namespace OAI

/-! # Dimensional heat transport expansion including the initial time -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem NoncollapsedRCD.heat_dimensional_expansion
    (K : ℝ) (n : ℕ) [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N) (p : X)
    (f g : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf0 : 0 ≤ f) (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C)
    (hfm : ∫x, f x ∂hausdorff n X = 1)
    {rf : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ rf)
    (hg0 : 0 ≤ g) (hgC : ∀ᵐ x ∂hausdorff n X, g x ≤ C)
    (hgm : ∫x, g x ∂hausdorff n X = 1)
    {rg : ℝ} (hgs : ∀ᵐ x ∂hausdorff n X, g x ≠ 0 → dist p x ≤ rg)
    {α β b : ℝ} (hα : 0 < α) (hβ : 0 < β) (hb : 0 ≤ b) :
    (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic (α*b) f)
      (heatMeasure (hausdorff n X) hX.quadratic (β*b) g)).toReal ≤
    gronwallBound
      (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic 0 f)
        (heatMeasure (hausdorff n X) hX.quadratic 0 g)).toReal
      (-K*(α+β)) (2*N*(Real.sqrt α-Real.sqrt β)^2) b := by
  rcases hb.eq_or_lt with hb|hb
  · subst b
    simp only [mul_zero,gronwallBound_x0,le_refl]
  let μ := hausdorff n X
  let := ACWassersteinProbability.metric μ K n hX.cd
  let ρ := hX.heatProbability K n hn p f hf0 ⟨rf,hfs⟩ hfm
  let σ := hX.heatProbability K n hn p g hg0 ⟨rg,hgs⟩ hgm
  let D := fun t => dist (ρ (α*t)) (σ (β*t))^2
  have hfabs : ∀ᵐ x ∂μ, |f x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hgabs : ∀ᵐ x ∂μ, |g x| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hg0,hgC] with x hl hu
    simpa only [abs_of_nonneg hl] using hu
  have hρ : ContinuousOn ρ (Icc 0 (α*b)) := by
    simpa only [uIcc_of_le (mul_pos hα hb).le] using (metricAC_uniformContinuousOn
      (hX.heat_probability_absolutelyContinuous K n hn p f hf0 ⟨rf,hfs⟩ hfm C hfabs (α*b)
        (mul_pos hα hb).le)).continuousOn
  have hσ : ContinuousOn σ (Icc 0 (β*b)) := by
    simpa only [uIcc_of_le (mul_pos hβ hb).le] using (metricAC_uniformContinuousOn
      (hX.heat_probability_absolutelyContinuous K n hn p g hg0 ⟨rg,hgs⟩ hgm C hgabs (β*b)
        (mul_pos hβ hb).le)).continuousOn
  have hρα : ContinuousOn (fun t => ρ (α*t)) (Icc 0 b) :=
    hρ.comp (continuous_const.mul continuous_id).continuousOn (fun t ht =>
      ⟨mul_nonneg hα.le ht.1,mul_le_mul_of_nonneg_left ht.2 hα.le⟩)
  have hσβ : ContinuousOn (fun t => σ (β*t)) (Icc 0 b) :=
    hσ.comp (continuous_const.mul continuous_id).continuousOn (fun t ht =>
      ⟨mul_nonneg hβ.le ht.1,mul_le_mul_of_nonneg_left ht.2 hβ.le⟩)
  have hD : ContinuousOn D (Icc 0 b) := fun t ht => ((hρα t ht).dist (hσβ t ht)).pow 2
  have heq (t : ℝ) (ht : 0 ≤ t) : D t =
      (wassersteinSq (heatMeasure μ hX.quadratic (α*t) f)
        (heatMeasure μ hX.quadratic (β*t) g)).toReal := by
    rw [show D t = dist (ρ (α*t)) (σ (β*t))^2 from rfl,ACWassersteinProbability.dist_sq μ hX.cd]
    dsimp only [ρ,σ,NoncollapsedRCD.heatProbability]
    rw [max_eq_left (mul_nonneg hα.le ht),max_eq_left (mul_nonneg hβ.le ht)]
  have hh := evolution_initial_limit hb hD (k := -K*(α+β))
      (e := 2*N*(Real.sqrt α-Real.sqrt β)^2) (by
    intro a ha hab
    rw [heq b hb.le,heq a ha.le]
    exact hX.heat_dimensional_expansion_positive K n hn hK hN p f g C
      hf0 hfC hfm hfs hg0 hgC hgm hgs hα hβ ha hab)
  rw [heq b hb.le,heq 0 le_rfl] at hh
  simpa only [mul_zero] using hh

end RegularPointCoordinates

end

end OAI
