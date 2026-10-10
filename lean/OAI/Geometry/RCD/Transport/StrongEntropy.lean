import OAI.Geometry.RCD.Heat.EVIGeodesicConvexity
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Strong entropy convexity at bounded-density Wasserstein geodesic points

Applying the integrated EVI to both endpoints gives the entropy bound at every bounded-density
geodesic point, rather than only at a selected entropy interpolation.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)

theorem bounded_entropy_geodesic_point (hn : 2 ≤ n) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0) (hf0 : 0 ≤ f)
    (hfC : ∀ᵐ x ∂hausdorff n X, f x ≤ C) (hfm : (∫ x, f x ∂hausdorff n X)=1)
    {r : ℝ} (hfs : ∀ᵐ x ∂hausdorff n X, f x≠0 → dist p x ≤ r)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (hν₀ : ν₀ ≤ ENNReal.ofReal C • hausdorff n X)
    (hν₁ : ν₁ ≤ ENNReal.ofReal C • hausdorff n X)
    {R₀ R₁ : ℝ} (hs₀ : ∀ᵐ x ∂ν₀, dist x p ≤ R₀) (hs₁ : ∀ᵐ x ∂ν₁, dist x p ≤ R₁)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd₀ : (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic 0 f) ν₀).toReal=
      θ^2*(wassersteinSq ν₀ ν₁).toReal)
    (hd₁ : (wassersteinSq (heatMeasure (hausdorff n X) hX.quadratic 0 f) ν₁).toReal=
      (1-θ)^2*(wassersteinSq ν₀ ν₁).toReal) :
    boltzmannEntropy (hausdorff n X) (heatMeasure (hausdorff n X) hX.quadratic 0 f) ≤
      (1-θ)*boltzmannEntropy (hausdorff n X) ν₀+θ*boltzmannEntropy (hausdorff n X) ν₁-
      (K/2)*θ*(1-θ)*(wassersteinSq ν₀ ν₁).toReal := by
  let μ := hausdorff n X
  let := ACWassersteinProbability.metric μ K n hX.cd
  let x : ACWassersteinProbability μ := ⟨ν₀,inferInstance,
    Measure.absolutelyContinuous_of_le_smul hν₀,finiteSecondMoment_of_ae_dist_le ν₀ p hs₀⟩
  let y : ACWassersteinProbability μ := ⟨ν₁,inferInstance,
    Measure.absolutelyContinuous_of_le_smul hν₁,finiteSecondMoment_of_ae_dist_le ν₁ p hs₁⟩
  let z := hX.heatProbability K n hn p f hf0 ⟨r,hfs⟩ hfm
  let E := fun v : ACWassersteinProbability μ => boltzmannEntropy μ v.val
  have hfabs : ∀ᵐ a ∂μ, |f a| ≤ C := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0,hfC] with a ha hb
    simpa only [abs_of_nonneg ha] using hb
  have hz : ContinuousOn z (Icc 0 1) := by
    simpa only [uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] using (metricAC_uniformContinuousOn
      (hX.heat_probability_absolutelyContinuous K n hn p f hf0 ⟨r,hfs⟩ hfm C hfabs 1 zero_le_one)).continuousOn
  have hmeasure (t : ℝ) (ht : 0 ≤ t) : (z t).val=heatMeasure μ hX.quadratic t f := by
    change heatMeasure μ hX.quadratic (max t 0) f=heatMeasure μ hX.quadratic t f
    rw [max_eq_left ht]
  have hdist₀ (t : ℝ) (ht : 0 ≤ t) :
      dist (z t) x^2=(wassersteinSq (heatMeasure μ hX.quadratic t f) ν₀).toReal := by
    rw [ACWassersteinProbability.dist_sq μ hX.cd,hmeasure t ht]
  have hdist₁ (t : ℝ) (ht : 0 ≤ t) :
      dist (z t) y^2=(wassersteinSq (heatMeasure μ hX.quadratic t f) ν₁).toReal := by
    rw [ACWassersteinProbability.dist_sq μ hX.cd,hmeasure t ht]
  have hdist : dist x y^2=(wassersteinSq ν₀ ν₁).toReal := ACWassersteinProbability.dist_sq μ hX.cd x y
  have hx : dist (z 0) x=θ*dist x y := by
    apply (sq_eq_sq₀ dist_nonneg (mul_nonneg hθ0 dist_nonneg)).mp
    rw [mul_pow,hdist₀ 0 le_rfl,hdist]
    exact hd₀
  have hy : dist (z 0) y=(1-θ)*dist x y := by
    apply (sq_eq_sq₀ dist_nonneg (mul_nonneg (sub_nonneg.mpr hθ1) dist_nonneg)).mp
    rw [mul_pow,hdist₁ 0 le_rfl,hdist]
    exact hd₁
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hraw := heatAt_entropy_absolutelyContinuous_nonneg μ hX.quadratic p hA hB hvol f hf0
    (lp_integrable_of_bounded_support μ f p hfs) hfs (a:=0) (b:=1) le_rfl zero_le_one
  have he : ContinuousOn (fun t => E (z t)) (Icc 0 1) := by
    have hc : ContinuousOn (fun t => boltzmannEntropy μ (heatMeasure μ hX.quadratic t f)) (Icc 0 1) := by
      simpa only [uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1),boltzmannEntropy_heatMeasure_eq μ hX.quadratic f hf0]
        using hraw.continuousOn
    apply hc.congr
    intro t ht
    change boltzmannEntropy μ (z t).val=boltzmannEntropy μ (heatMeasure μ hX.quadratic t f)
    rw [hmeasure t ht.1]
  have hbound := geodesic_convexity_of_integrated_evi (K:=K) hθ0 hθ1 zero_lt_one hz he hx hy
    (fun a b ha hab _ => ?_) (fun a b ha hab _ => ?_)
  · simpa only [E,hmeasure 0 le_rfl,hdist] using hbound
  · rw [hdist₀ b (ha.le.trans hab),hdist₀ a ha.le]
    have h := hX.bounded_heat_EVI K n hn p f C hf0 hfC hfm hfs ν₀ hν₀ hs₀ ha hab
    convert h using 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := ha.le.trans ((uIcc_of_le hab ▸ ht).1)
    change boltzmannEntropy μ ν₀-boltzmannEntropy μ (z t).val-(K/2)*dist (z t) x^2=
      boltzmannEntropy μ ν₀-boltzmannEntropy μ (heatMeasure μ hX.quadratic t f)-
        (K/2)*(wassersteinSq (heatMeasure μ hX.quadratic t f) ν₀).toReal
    rw [hmeasure t ht0,hdist₀ t ht0]
  · rw [hdist₁ b (ha.le.trans hab),hdist₁ a ha.le]
    have h := hX.bounded_heat_EVI K n hn p f C hf0 hfC hfm hfs ν₁ hν₁ hs₁ ha hab
    convert h using 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := ha.le.trans ((uIcc_of_le hab ▸ ht).1)
    change boltzmannEntropy μ ν₁-boltzmannEntropy μ (z t).val-(K/2)*dist (z t) y^2=
      boltzmannEntropy μ ν₁-boltzmannEntropy μ (heatMeasure μ hX.quadratic t f)-
        (K/2)*(wassersteinSq (heatMeasure μ hX.quadratic t f) ν₁).toReal
    rw [hmeasure t ht0,hdist₁ t ht0]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
