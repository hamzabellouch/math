import OAI.Geometry.Riemannian.HarmonicCore.Model

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample.Main

abbrev UnitSphere3 := Metric.sphere (0:E3) 1



def angularMeasure : Measure UnitSphere3 :=
  ENNReal.ofReal (1/(4*Real.pi)) • (volume : Measure E3).toSphere



instance angularMeasure_probability : IsProbabilityMeasure angularMeasure := by
  constructor
  rw [angularMeasure,Measure.smul_apply,Measure.toSphere_apply_univ]
  simp only [E3, finrank_euclideanSpace, Fintype.card_fin, EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one,one_pow,one_mul,smul_eq_mul]
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  convert ENNReal.ofReal_one using 1
  field_simp
  ring_nf



def sphericalMean (u : E3 → ℝ) (r : ℝ) : ℝ :=
  ∫ z : UnitSphere3, u (r • (z:E3)) ∂angularMeasure



def sphericalMeanDerivative (u : E3 → ℝ) (r : ℝ) : ℝ :=
  ∫ z : UnitSphere3, fderiv ℝ u (r • (z:E3)) (z:E3) ∂angularMeasure



lemma sphericalMean_continuous {u : E3 → ℝ} (hu : Continuous u) :
    Continuous (sphericalMean u) := by
  have hh : Continuous (fun p : ℝ × UnitSphere3 ↦ u (p.1 • (p.2:E3))) := by fun_prop
  change Continuous (fun r ↦ ∫ z : UnitSphere3, u (r • (z:E3)) ∂angularMeasure)
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ:=angularMeasure)
      (f:=fun r (z:UnitSphere3) ↦ u (r • (z:E3))) hh isCompact_univ)



lemma sphericalMeanDerivative_continuous {u : E3 → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (sphericalMeanDerivative u) := by
  have hh : Continuous (fun p : ℝ × UnitSphere3 ↦ fderiv ℝ u (p.1 • (p.2:E3)) (p.2:E3)) :=
    ((hu.continuous_fderiv (by simp)).comp (continuous_fst.smul
      (continuous_subtype_val.comp continuous_snd))).clm_apply (continuous_subtype_val.comp continuous_snd)
  change Continuous (fun r ↦ ∫ z : UnitSphere3, fderiv ℝ u (r • (z:E3)) (z:E3) ∂angularMeasure)
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (μ:=angularMeasure)
      (f:=fun r (z:UnitSphere3) ↦ fderiv ℝ u (r • (z:E3)) (z:E3)) hh isCompact_univ)



lemma sphericalMean_hasDerivAt {u : E3 → ℝ} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    HasDerivAt (sphericalMean u) (sphericalMeanDerivative u r) r := by
  have hd := hu.continuous_fderiv (by simp)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E3) (|r|+1)).exists_bound_of_continuousOn hd.continuousOn
  have huc (s : ℝ) : Continuous (fun z : UnitSphere3 ↦ u (s • (z:E3))) := by fun_prop
  have hdc (s : ℝ) : Continuous (fun z : UnitSphere3 ↦ fderiv ℝ u (s • (z:E3)) (z:E3)) :=
    (hd.comp ((continuous_const (y:=s)).smul continuous_subtype_val)).clm_apply continuous_subtype_val
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=angularMeasure) (F:=fun s (z:UnitSphere3) ↦ u (s • (z:E3)))
    (F':=fun s (z:UnitSphere3) ↦ fderiv ℝ u (s • (z:E3)) (z:E3))
    (bound:=fun _ ↦ C) (Metric.ball_mem_nhds r zero_lt_one)
    (Eventually.of_forall (fun s ↦ (huc s).aestronglyMeasurable))
    ((huc r).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hdc r).aestronglyMeasurable ?_ (integrable_const C) ?_).2
  · exact Eventually.of_forall fun z s hs ↦ by
      have hz : ‖(z:E3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using z.property
      have hs' : ‖s‖ ≤ |r|+1 := by
        have hsr : ‖s-r‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hs
        have hb := norm_add_le (s-r) r
        rw [sub_add_cancel] at hb
        rw [Real.norm_eq_abs r] at hb
        linarith
      have hx : s • (z:E3) ∈ Metric.closedBall 0 (|r|+1) := by
        simpa only [Metric.mem_closedBall,dist_zero_right,norm_smul,hz,mul_one] using hs'
      calc
        ‖fderiv ℝ u (s • (z:E3)) (z:E3)‖ ≤ ‖fderiv ℝ u (s • (z:E3))‖*‖(z:E3)‖ :=
          (fderiv ℝ u (s • (z:E3))).le_opNorm _
        _ ≤ C := by rw [hz,mul_one]; exact hC _ hx
  · exact Eventually.of_forall fun z s _ ↦
      (hu.differentiable (by simp) (s • (z:E3))).hasFDerivAt.comp_hasDerivAt s
        (by simpa only [id_eq,one_smul] using (hasDerivAt_id s).smul_const (z:E3))



lemma sphericalMean_zero (u : E3 → ℝ) : sphericalMean u 0=u 0 := by
  simp [sphericalMean]



lemma regular_origin_flux_zero {u : E3 → ℝ} (hu : ContDiff ℝ ∞ u)
    {f : ℝ → ℝ} (hf : ContinuousAt f 0) (hzero : f 0=0) :
    Tendsto (fun r ↦ f r^2 * sphericalMeanDerivative u r) (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun r ↦ f r^2 * sphericalMeanDerivative u r) (𝓝 0)
      (𝓝 (f 0^2 * sphericalMeanDerivative u 0)) :=
    (hf.tendsto.pow 2).mul (sphericalMeanDerivative_continuous hu).continuousAt.tendsto
  simpa only [hzero,zero_pow (by norm_num : (2:ℕ)≠0),zero_mul] using h



theorem integral_polar_three {h : E3 → ℝ} (hh : Integrable h volume) :
    (∫ x : E3, h x) = ∫ r in Ioi (0:ℝ), r^2 *
      (∫ z : UnitSphere3, h (r • (z:E3)) ∂(volume : Measure E3).toSphere) := by
  let H := homeomorphUnitSphereProd E3
  let F : UnitSphere3 × Ioi (0:ℝ) → ℝ := fun p ↦ h (p.2.val • (p.1:E3))
  have hm : MeasurePreserving H ((volume : Measure E3).comap Subtype.val)
      ((volume : Measure E3).toSphere.prod (Measure.volumeIoiPow 2)) := by
    simpa only [E3,finrank_euclideanSpace,Fintype.card_fin,Nat.reduceSub] using
      (volume : Measure E3).measurePreserving_homeomorphUnitSphereProd
  have hcomp : F ∘ H = fun x : ({(0:E3)}ᶜ : Set E3) ↦ h x := by
    funext x
    simpa only [H,F,Function.comp_apply,homeomorphUnitSphereProd_symm_apply_coe] using
      congrArg (fun y : ({(0:E3)}ᶜ : Set E3) ↦ h y) (H.symm_apply_apply x)
  have hi : Integrable (fun x : ({(0:E3)}ᶜ : Set E3) ↦ h x)
      ((volume : Measure E3).comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal ((measurableSet_singleton (0:E3)).compl)).mp hh.integrableOn
  have hF : Integrable F ((volume : Measure E3).toSphere.prod (Measure.volumeIoiPow 2)) := by
    rw [← hm.integrable_comp_emb (Homeomorph.measurableEmbedding H),hcomp]
    exact hi
  calc
    (∫ x : E3, h x) = ∫ x : ({(0:E3)}ᶜ : Set E3), h x ∂((volume : Measure E3).comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton (0:E3)).compl h,restrict_compl_singleton]
    _ = ∫ p, F p ∂((volume : Measure E3).toSphere.prod (Measure.volumeIoiPow 2)) := by
      rw [← hm.integral_comp (Homeomorph.measurableEmbedding H) F]
      exact integral_congr_ae (Eventually.of_forall (fun x ↦ (congrFun hcomp x).symm))
    _ = ∫ r : Ioi (0:ℝ), (∫ z : UnitSphere3, h ((r:ℝ) • (z:E3))
        ∂(volume : Measure E3).toSphere) ∂Measure.volumeIoiPow 2 := integral_prod_symm F hF
    _ = _ := by
      simp only [Measure.volumeIoiPow,ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul]
      · rw [integral_subtype_comap measurableSet_Ioi
          (fun r : ℝ ↦ Real.toNNReal (r^2) • (∫ z : UnitSphere3, h (r • (z:E3)) ∂(volume : Measure E3).toSphere))]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp only
        rw [NNReal.smul_def,Real.coe_toNNReal _ (sq_nonneg r),smul_eq_mul]
      · exact (measurable_subtype_coe.pow_const 2).real_toNNReal

end HarmonicCounterexample.Main

end

end OAI
