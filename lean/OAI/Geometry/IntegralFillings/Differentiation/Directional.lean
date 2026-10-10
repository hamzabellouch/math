import Mathlib
import OAI.Geometry.IntegralFillings.Differentiation.CurveSpeed

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
variable {X : Type*} [MetricSpace X]
noncomputable def signedDistance (c : ℝ → X) (t : ℝ) : ℝ :=
  if 0 ≤ t then dist (c t) (c 0) else -dist (c t) (c 0)

lemma signedDistance_zero (c : ℝ → X) : signedDistance c 0 = 0 := by
  simp [signedDistance]

lemma signedDistance_div (c : ℝ → X) (t : ℝ) :
    signedDistance c t / t = dist (c t) (c 0) / |t| := by
  rcases le_total 0 t with ht | ht
  · simp [signedDistance, ht, abs_of_nonneg ht]
  · by_cases h0 : t = 0
    · simp [h0]
    · simp [signedDistance, not_le.mpr (lt_of_le_of_ne ht h0), abs_of_nonpos ht, neg_div, div_neg]

lemma hasDerivAt_signedDistance_iff (c : ℝ → X) (d : ℝ) :
    HasDerivAt (signedDistance c) d 0 ↔
      Tendsto (fun t => dist (c t) (c 0) / |t|) (𝓝[≠] 0) (𝓝 d) := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, signedDistance_zero, sub_zero, smul_eq_mul, ← div_eq_inv_mul,
    signedDistance_div]

lemma continuous_signedDistance {A : Type*} [TopologicalSpace A] {c : A → ℝ → X}
    (hc : Continuous c.uncurry) : Continuous (fun p : A × ℝ => signedDistance (c p.1) p.2) := by
  have hd : Continuous (fun p : A × ℝ => dist (c p.1 p.2) (c p.1 0)) :=
    hc.dist (hc.comp (continuous_fst.prodMk continuous_const))
  exact hd.if_le hd.neg continuous_const continuous_snd (by
    rintro ⟨x,t⟩ (h : 0 = t)
    simp [← h])

lemma measurableSet_metricDirectionalDeriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → X} (hf : Continuous f) (v : E) :
    MeasurableSet {x | ∃ d : ℝ, Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 d)} := by
  let c : E → ℝ → X := fun x t => f (x + t • v)
  have hc : Continuous c.uncurry := hf.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hm := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x t => signedDistance (c x) t) (continuous_signedDistance hc)
  have hm' := measurable_prodMk_right (y := (0 : ℝ)) hm
  convert hm' using 1
  ext x
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨d, hd⟩
    exact ((hasDerivAt_signedDistance_iff (c x) d).mpr (by simpa [c] using hd)).differentiableAt
  · intro hd
    refine ⟨deriv (signedDistance (c x)) 0, ?_⟩
    simpa [c] using (hasDerivAt_signedDistance_iff (c x) _).mp hd.hasDerivAt

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

noncomputable def scalarCoordinate (f : E → X) (q : ℕ) (x : E) : ℝ :=
  dist (f x) (denseSeq X q)

omit [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ E] in
lemma scalarCoordinate_lipschitz (hf : LipschitzWith K f) (q : ℕ) :
    LipschitzWith K (scalarCoordinate f q) := by
  change LipschitzWith K (fun x : E => dist (f x) (denseSeq X q))
  simpa only [Function.comp_def, one_mul] using
    (LipschitzWith.dist_left (denseSeq X q)).comp hf

noncomputable def lineSpeed (f : E → X) (v x : E) : ℝ :=
  ⨆ q : ℕ, |lineDeriv ℝ (scalarCoordinate f q) x v|

lemma measurable_lineSpeed (hf : Continuous f) (v : E) : Measurable (lineSpeed f v) := by
  apply Measurable.iSup
  intro q
  exact (measurable_lineDeriv (hf.dist continuous_const)).abs

omit [MeasurableSpace E] [BorelSpace E] in
lemma deriv_coordinate_line (p v : E) (s : ℝ) (q : ℕ) :
    deriv (MetricDifferentiationDense.distanceCoordinate (fun t => f (p+t • v)) q) s =
      lineDeriv ℝ (scalarCoordinate f q) (p+s • v) v := by
  rw [lineDeriv]
  have he : (fun t : ℝ => scalarCoordinate f q (p+s • v+t • v)) =
      (fun t : ℝ => MetricDifferentiationDense.distanceCoordinate (fun t => f (p+t • v)) q (s+t)) := by
    ext t
    simp [scalarCoordinate, MetricDifferentiationDense.distanceCoordinate, add_smul, add_assoc]
  rw [he]
  simpa using (deriv_comp_const_add (f := MetricDifferentiationDense.distanceCoordinate
    (fun t => f (p+t • v)) q) s 0).symm

omit [MeasurableSpace E] [BorelSpace E] in
lemma lineSpeed_eq_curveSpeed (p v : E) (s : ℝ) :
    lineSpeed f v (p+s • v) = MetricDifferentiationDense.metricSpeed (fun t => f (p+t • v)) s := by
  simp only [lineSpeed, MetricDifferentiationDense.metricSpeed, deriv_coordinate_line]

lemma measurableSet_hasMetricDirectionalDeriv (hf : Continuous f) (v : E) :
    MeasurableSet {x | Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 (lineSpeed f v x))} := by
  let c : E → ℝ → X := fun x t => f (x + t • v)
  have hc : Continuous c.uncurry := hf.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hD := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x t => signedDistance (c x) t) (continuous_signedDistance hc)
  have hder := measurable_deriv_with_param (f := fun x t => signedDistance (c x) t)
    (continuous_signedDistance hc)
  have hm := (measurable_prodMk_right (y := (0 : ℝ)) hD).inter
    (measurableSet_eq_fun (hder.comp (measurable_prodMk_right (y := (0 : ℝ)))) (measurable_lineSpeed hf v))
  convert hm using 1
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro ht
    have hd := (hasDerivAt_signedDistance_iff (c x) (lineSpeed f v x)).mpr (by simpa [c] using ht)
    exact ⟨hd.differentiableAt, hd.deriv⟩
  · rintro ⟨hd, he⟩
    rw [← he]
    simpa [c] using (hasDerivAt_signedDistance_iff (c x) _).mp hd.hasDerivAt

lemma tendsto_add_zero_punctured (s : ℝ) :
    Tendsto (fun t : ℝ => s+t) (𝓝[≠] 0) (𝓝[≠] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => s) (𝓝 0) (𝓝 s)).add tendsto_id).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

theorem ae_hasMetricDirectionalDeriv [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f) (v : E) :
    ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 (lineSpeed f v x)) := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  apply ae_mem_of_ae_add_linearMap_mem L.toLinearMap volume μ
    (measurableSet_hasMetricDirectionalDeriv hf.continuous v)
  intro p
  have hcurve := hf.comp ((LipschitzWith.const p).add L.lipschitzWith)
  filter_upwards [MetricDifferentiationDense.ae_hasMetricDerivAt hcurve] with s hs
  change Tendsto (fun t : ℝ => dist (f (p+s • v+t • v)) (f (p+s • v)) / |t|)
    (𝓝[≠] 0) (𝓝 (lineSpeed f v (p+s • v)))
  rw [lineSpeed_eq_curveSpeed]
  have hh := hs.comp (tendsto_add_zero_punctured s)
  simpa only [Function.comp_def, L, MetricDifferentiationDense.HasMetricDerivAt,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul,
    add_smul, add_assoc, add_sub_cancel_left] using hh

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
