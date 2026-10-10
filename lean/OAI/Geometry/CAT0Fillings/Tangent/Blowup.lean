import Mathlib
import OAI.Geometry.CAT0Fillings.Differentiation.HilbertCharts

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity

lemma tangent_kernel_mono {t u β c : ℝ} (ht : 0 ≤ t) (htu : t ≤ u)
    (hb : 0 ≤ β) (hc : 0 ≤ c) (n : ℕ) :
    t^(2*(n:ℝ)*β)/(1+c*t^(2*β))^n ≤ u^(2*(n:ℝ)*β)/(1+c*u^(2*β))^n := by
  have hu := ht.trans htu
  have htp : 0 ≤ t^(2*β) := Real.rpow_nonneg ht _
  have hup : 0 ≤ u^(2*β) := Real.rpow_nonneg hu _
  have hmono : t^(2*β) ≤ u^(2*β) := Real.rpow_le_rpow ht htu (by positivity)
  have hdenT : 0 < 1+c*t^(2*β) := by positivity
  have hdenU : 0 < 1+c*u^(2*β) := by positivity
  have hdiv : t^(2*β)/(1+c*t^(2*β)) ≤ u^(2*β)/(1+c*u^(2*β)) := by
    apply (div_le_div_iff₀ hdenT hdenU).mpr
    nlinarith [hmono]
  have he (a : ℝ) (ha : 0 ≤ a) : a^(2*(n:ℝ)*β) = (a^(2*β))^n := by
    rw [←Real.rpow_mul_natCast ha]
    congr 1; ring
  rw [he t ht,he u hu,←div_pow,←div_pow]
  exact pow_le_pow_left₀ (div_nonneg htp hdenT.le) hdiv n

noncomputable def boundedCoordinate (u : ℝ) (N : ℝ) : ℝ := min (max u 0) N
lemma boundedCoordinate_nonneg {N : ℝ} (hN : 0 ≤ N) (u : ℝ) :
    0 ≤ boundedCoordinate u N := le_min (le_max_right _ _) hN
lemma boundedCoordinate_le {u N : ℝ} (hu : 0 ≤ u) : boundedCoordinate u N ≤ u := by
  simp only [boundedCoordinate,max_eq_left hu]
  exact min_le_left _ _
lemma boundedCoordinate_eq {u N : ℝ} (hu : 0 ≤ u) (hN : u ≤ N) : boundedCoordinate u N = u := by
  simp [boundedCoordinate,hu,hN]

lemma integrable_coordinate_truncation {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {s : Set E} (hs : MeasurableSet s) (hfin : μ s ≠ ∞) {u : E → ℝ} (hu : Measurable u)
    {N : ℝ} (hN : 0 ≤ N) : Integrable (s.indicator (fun z => boundedCoordinate (u z) N)) μ := by
  let : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hfin
  apply IntegrableOn.integrable_indicator _ hs
  have hm : Measurable (fun z => boundedCoordinate (u z) N) := (hu.max measurable_const).min measurable_const
  apply (MemLp.of_bound hm.aestronglyMeasurable N ?_).integrable (by norm_num : (1:ℝ≥0∞) ≤ 1)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (boundedCoordinate_nonneg hN _)]
  exact min_le_right _ _
end CAT0Fillings.TangentDensity
end

section
open Set Filter MeasureTheory Metric Asymptotics
open scoped Topology

namespace CAT0Fillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] {s : Set E} {φ : s → X} {p : Seminorm ℝ E}

lemma rescaled_distance_tendsto {z : s} (hp : HasCenteredMetricDifferentialWithin s φ p z)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hε0 : Tendsto ε atTop (𝓝 0))
    (h : E) (q : ℕ → s) (hq : ∀ᶠ j in atTop, (q j : E) = z+ε j • h) :
    Tendsto (fun j => dist (φ (q j)) (φ z)/ε j) atTop (𝓝 (p h)) := by
  have ht : Tendsto q atTop (𝓝 z) := by
    apply tendsto_subtype_rng.mpr
    have hh := (tendsto_const_nhds (x := (z:E))).add (hε0.smul_const h)
    simp only [zero_smul,add_zero] at hh
    exact hh.congr' (hq.mono fun _ h => h.symm)
  have hb : (fun j => (q j : E)-(z:E)) =O[atTop] ε := by
    apply IsBigO.of_bound ‖h‖
    filter_upwards [hq] with j hj
    rw [hj,add_sub_cancel_left,norm_smul]
    exact le_of_eq (mul_comm _ _)
  have hl := ((hp.comp_tendsto ht).trans_isBigO hb).tendsto_div_nhds_zero
  have ha := hl.add_const (p h)
  simp only [zero_add] at ha
  apply ha.congr'
  filter_upwards [hq] with j hj
  change (dist (φ (q j)) (φ z)-p ((q j:E)-(z:E)))/ε j+p h = _
  rw [hj,add_sub_cancel_left,map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (hε j)]
  field_simp [ne_of_gt (hε j)]
  ring
end CAT0Fillings.MetricDifferentiation
end

section
open Set Filter MeasureTheory Metric
open scoped Topology Pointwise

namespace CAT0Fillings.TangentDensity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F]

lemma integral_affine_closedBall [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → F) (z : E) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    (∫ h in closedBall (0:E) R, f (z+ε • h) ∂μ) =
      (ε ^ Module.finrank ℝ E)⁻¹ • ∫ x in closedBall z (ε*R), f x ∂μ := by
  rw [Measure.setIntegral_comp_smul_of_pos μ (fun x => f (z+x)) _ hε,
    smul_closedBall' hε.ne',smul_zero,Real.norm_eq_abs,abs_of_pos hε]
  congr 1
  have ht := (measurePreserving_add_left μ z).setIntegral_preimage_emb
    (Homeomorph.addLeft z).measurableEmbedding f (closedBall z (ε*R))
  have he : (fun x : E => z+x) ⁻¹' closedBall z (ε*R) = closedBall 0 (ε*R) := by
    ext x
    simp only [mem_preimage,mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero]
  rwa [he] at ht

lemma integral_affine_eq_average [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) (z : E) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    (∫ h in closedBall (0:E) R, f (z+ε • h) ∂μ) =
      μ.real (closedBall (0:E) R) • (⨍ x in closedBall z (ε*R), f x ∂μ) := by
  rw [integral_affine_closedBall μ f z hε,setAverage_eq]
  have hball : 0 < μ.real (ball (0:E) 1) := ENNReal.toReal_pos
    (isOpen_ball.measure_ne_zero μ (Metric.nonempty_ball.mpr (by norm_num)))
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0:E) 1).measure_lt_top).ne
  rw [Measure.addHaar_real_closedBall μ 0 hR.le,
    Measure.addHaar_real_closedBall μ z (mul_pos hε hR).le,smul_smul,mul_pow]
  congr 1
  field_simp

lemma integrable_affine [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → F) (hf : Integrable f μ) (z : E)
    {ε : ℝ} (hε : ε ≠ 0) : Integrable (fun h => f (z+ε • h)) μ :=
  ((measurePreserving_add_left μ z).integrable_comp_emb
    (Homeomorph.addLeft z).measurableEmbedding |>.mpr hf).comp_smul hε

lemma tendsto_integral_blowup [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F} {z : E} {ε : ℕ → ℝ} {R : ℝ}
    (hε : ∀ j, 0 < ε j) (hR : 0 < R)
    (havg : Tendsto (fun j => ⨍ x in closedBall z (ε j*R), ‖f x-f z‖ ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun j => ∫ h in closedBall (0:E) R, ‖f (z+ε j • h)-f z‖ ∂μ)
      atTop (𝓝 0) := by
  simp_rw [integral_affine_eq_average μ (fun x => ‖f x-f z‖) z (hε _) hR]
  simpa using havg.const_smul (μ.real (closedBall (0:E) R))

lemma tendstoInMeasure_blowup [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F} (hf : Integrable f μ) {z : E}
    {ε : ℕ → ℝ} {R : ℝ} (hε : ∀ j, 0 < ε j) (hR : 0 < R)
    (havg : Tendsto (fun j => ⨍ x in closedBall z (ε j*R), ‖f x-f z‖ ∂μ)
      atTop (𝓝 0)) :
    TendstoInMeasure (μ.restrict (closedBall (0:E) R))
      (fun j h => f (z+ε j • h)) atTop (fun _ => f z) := by
  let : IsFiniteMeasure (μ.restrict (closedBall (0:E) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:E) R).measure_lt_top.ne
  have hi (j) : Integrable (fun h => f (z+ε j • h)) (μ.restrict (closedBall (0:E) R)) :=
    (integrable_affine μ f hf z (hε j).ne').integrableOn
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by simp)
  have hl := (ENNReal.continuous_ofReal.tendsto 0).comp
    (tendsto_integral_blowup μ hε hR havg)
  simp only [ENNReal.ofReal_zero] at hl
  convert hl using 1
  ext j
  rw [eLpNorm_one_eq_lintegral_enorm ((hi j).aestronglyMeasurable.sub aestronglyMeasurable_const),
    ←ofReal_integral_norm_eq_lintegral_enorm ((hi j).sub (integrable_const _))]
  rfl
end CAT0Fillings.TangentDensity
end

end OAI
