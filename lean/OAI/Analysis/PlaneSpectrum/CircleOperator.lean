import OAI.Analysis.PlaneSpectrum.CircleDecay
import OAI.Geometry.PlaneColoring.Compactness

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
lemma planeTranslate_continuous (g : ComplexPlaneL2) : Continuous (fun h => planeTranslate h g) := by
  let f : C(ℂ,C(ℂ,ℂ)) := (ContinuousMap.mk (fun p : ℂ × ℂ => p.2+p.1) (by fun_prop)).curry
  exact continuous_const.compMeasurePreservingLp f.continuous (fun h => measurePreserving_add_right volume h) (by simp)
lemma circleTranslate_integrable (g : ComplexPlaneL2) : Integrable (fun t => planeTranslate (direction t) g) angularMeasure :=
  Integrable.of_bound ((planeTranslate_continuous g).comp direction_continuous).aestronglyMeasurable ‖g‖
    (Eventually.of_forall fun t => (planeTranslate (direction t)).norm_map g |>.le)
def circleOperator (g : ComplexPlaneL2) : ComplexPlaneL2 := ∫ t, planeTranslate (direction t) g ∂angularMeasure
lemma circleOperator_norm_le (g : ComplexPlaneL2) : ‖circleOperator g‖≤‖g‖ := by
  simpa only [circleOperator,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (Eventually.of_forall fun t => (planeTranslate (direction t)).norm_map g |>.le :
      ∀ᵐ t ∂angularMeasure, ‖planeTranslate (direction t) g‖≤‖g‖)
lemma circleOperator_ae (g : ComplexPlaneL2) :
    circleOperator g =ᵐ[volume] fun x => ∫ t, g (x+direction t) ∂angularMeasure := by
  let F : ℂ × Angles → ℂ := fun p => g (p.1+direction p.2)
  have hF : StronglyMeasurable F := (Lp.stronglyMeasurable g).comp_measurable
    (measurable_fst.add (direction_continuous.measurable.comp measurable_snd))
  have hg2 : Integrable (fun x => ‖g x‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hi : Integrable (fun p => ‖F p‖^2) (volume.prod angularMeasure) := by
    apply (integrable_prod_iff' (hF.norm.pow 2).aestronglyMeasurable).mpr
    constructor
    · exact Eventually.of_forall fun t => (measurePreserving_add_right volume (direction t)).integrable_comp_of_integrable hg2
    · have he : (fun t => ∫ x, ‖‖F (x,t)‖^2‖ ∂volume) = fun _ => ∫ x, ‖g x‖^2 ∂volume := by
        funext t
        simp only [Real.norm_eq_abs,abs_sq,F]
        change (∫ x : ℂ, (fun y => ‖g y‖^2) (x+direction t)) = _
        exact (measurePreserving_add_right volume (direction t)).integral_comp
          (Homeomorph.addRight (direction t)).measurableEmbedding (fun y : ℂ => ‖g y‖^2)
      simp only [Pi.pow_apply]
      rw [he]
      exact integrable_const _
  have h := ProbabilityL2.average_toLp_integral volume angularMeasure hF hi
    (fun t => planeTranslate (direction t) g) (circleTranslate_integrable g)
    (Eventually.of_forall fun t => planeTranslate_ae (direction t) g)
  have ha : circleOperator g = (ProbabilityL2.average_memLp volume angularMeasure hF hi).toLp (ProbabilityL2.average angularMeasure F) := h.symm
  rw [ha]
  exact MemLp.coeFn_toLp (ProbabilityL2.average_memLp volume angularMeasure hF hi)
lemma circleSymbol_stronglyMeasurable : StronglyMeasurable circleSymbol := by
  have h : Continuous (fun p : ℂ × Angles => planePhase (direction p.2) p.1) := by
    unfold planePhase
    exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
      ((direction_continuous.comp continuous_snd).inner continuous_fst)
  exact h.stronglyMeasurable.integral_prod_right'
def circleMultiplier : ComplexPlaneL2 →L[ℂ] ComplexPlaneL2 :=
  Multiplier.clm volume circleSymbol circleSymbol_stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall circleSymbol_norm_le_one)
lemma circleMultiplier_ae (g : ComplexPlaneL2) :
    circleMultiplier g =ᵐ[volume] fun x => circleSymbol x*g x := Multiplier.clm_ae _ _ _ _ _
lemma fourier_circleOperator (g : ComplexPlaneL2) : 𝓕 (circleOperator g) = circleMultiplier (𝓕 g) := by
  let F : ℂ × Angles → ℂ := fun p => planePhase (direction p.2) p.1 * 𝓕 g p.1
  have hF : StronglyMeasurable F := by
    have h : Continuous (fun p : ℂ × Angles => planePhase (direction p.2) p.1) := by
      unfold planePhase
      exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        ((direction_continuous.comp continuous_snd).inner continuous_fst)
    exact h.stronglyMeasurable.mul ((Lp.stronglyMeasurable (𝓕 g)).comp_measurable measurable_fst)
  have hi : Integrable (fun p => ‖F p‖^2) (volume.prod angularMeasure) := by
    have he : (fun p => ‖F p‖^2) = fun p => ‖𝓕 g p.1‖^2 := by
      funext p
      simp only [F,norm_mul,planePhase_norm,one_mul]
    rw [he]
    exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (𝓕 g))).mp
      (Lp.memLp (𝓕 g))).comp_fst angularMeasure
  have hG : Integrable (fun t => 𝓕 (planeTranslate (direction t) g)) angularMeasure :=
    (Lp.fourierTransformₗᵢ ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (circleTranslate_integrable g)
  have h := ProbabilityL2.average_toLp_integral volume angularMeasure hF hi
    (fun t => 𝓕 (planeTranslate (direction t) g)) hG (Eventually.of_forall fun t => by
      rw [fourier_planeTranslate]
      exact phaseMultiplier_ae (direction t) (𝓕 g))
  have hc := (Lp.fourierTransformₗᵢ ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (circleTranslate_integrable g)
  change (∫ t, 𝓕 (planeTranslate (direction t) g) ∂angularMeasure) = 𝓕 (circleOperator g) at hc
  rw [← hc,← h]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (ProbabilityL2.average_memLp volume angularMeasure hF hi),
    circleMultiplier_ae (𝓕 g)] with x hx hy
  rw [hx,hy]
  exact integral_mul_const (𝓕 g x) (fun t => planePhase (direction t) x)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
lemma planePhase_sub_bound (h ξ : ℂ) : ‖1-planePhase h ξ‖ ≤ 8*‖h‖*‖ξ‖ := by
  have he : planePhase h ξ = Complex.exp (Complex.I * (2*Real.pi*inner ℝ h ξ : ℝ)) := by
    rw [planePhase,Real.fourierChar_apply,mul_comm Complex.I]
  rw [he,norm_sub_rev]
  apply (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*inner ℝ h ξ)).trans
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)]
  have hi := abs_real_inner_le_norm h ξ
  have hp := mul_nonneg (norm_nonneg h) (norm_nonneg ξ)
  calc
    _ ≤ 2*Real.pi*(‖h‖*‖ξ‖) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ 8*‖h‖*‖ξ‖ := by nlinarith [Real.pi_lt_four]
lemma planePhase_sub_bound_two (h ξ : ℂ) : ‖1-planePhase h ξ‖≤2 := by
  have hi := norm_sub_le (1:ℂ) (planePhase h ξ)
  simpa only [norm_one,planePhase_norm,one_add_one_eq_two] using hi

def circleDifferenceRatio (h ξ : ℂ) : ℝ :=
  ‖circleSymbol ξ‖^2 * ‖1-planePhase h ξ‖^2 / ‖h‖
lemma circleDifferenceRatio_nonneg (h ξ : ℂ) : 0≤circleDifferenceRatio h ξ := by
  unfold circleDifferenceRatio
  positivity
lemma circleDifferenceRatio_small (h ξ : ℂ) :
    circleDifferenceRatio h ξ ≤ 64*‖h‖*‖ξ‖^2 := by
  by_cases hh : h=0
  · simp [hh,circleDifferenceRatio]
  have hh0 : 0<‖h‖ := norm_pos_iff.mpr hh
  have hb := planePhase_sub_bound h ξ
  have hc := circleSymbol_norm_le_one ξ
  have hc2 : ‖circleSymbol ξ‖^2 ≤ 1 := by nlinarith [norm_nonneg (circleSymbol ξ)]
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  unfold circleDifferenceRatio
  apply (div_le_iff₀ hh0).mpr
  calc
    _ ≤ ‖1-planePhase h ξ‖^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg ‖1-planePhase h ξ‖)]
    _ ≤ (8*‖h‖*‖ξ‖)^2 := hb2
    _ = _ := by ring
lemma circleDifferenceRatio_bound (h ξ : ℂ) : circleDifferenceRatio h ξ ≤ 25600 := by
  by_cases hh : h=0
  · simp [hh,circleDifferenceRatio]
  have hh0 : 0<‖h‖ := norm_pos_iff.mpr hh
  have hn : 0<1+‖ξ‖ := by positivity
  have hc := (le_div_iff₀ hn).mp (circleSymbol_sq_bound ξ)
  by_cases hs : ‖h‖*‖ξ‖≤1
  · have hb2 := pow_le_pow_left₀ (norm_nonneg _) (planePhase_sub_bound h ξ) 2
    have hmul := mul_le_mul_of_nonneg_left hb2 (sq_nonneg ‖circleSymbol ξ‖)
    have hs' : ‖h‖ * ‖ξ‖^2 ≤ ‖ξ‖ := by nlinarith [mul_nonneg (sub_nonneg.mpr hs) (norm_nonneg ξ)]
    have hc' : ‖circleSymbol ξ‖^2 * ‖ξ‖ ≤ 400 := by nlinarith [sq_nonneg ‖circleSymbol ξ‖]
    have hb : ‖circleSymbol ξ‖^2 * (‖h‖ * ‖ξ‖^2) ≤ 400 :=
      (mul_le_mul_of_nonneg_left hs' (sq_nonneg _)).trans hc'
    unfold circleDifferenceRatio
    apply (div_le_iff₀ hh0).mpr
    have hb' := mul_le_mul_of_nonneg_left hb (by positivity : 0≤64*‖h‖)
    nlinarith
  · have hb2 := pow_le_pow_left₀ (norm_nonneg _) (planePhase_sub_bound_two h ξ) 2
    have hc' : ‖circleSymbol ξ‖^2 ≤ 400*‖h‖ := by
      have hmul := mul_le_mul_of_nonneg_left hc (norm_nonneg h)
      have hi := mul_nonneg (sq_nonneg ‖circleSymbol ξ‖)
        (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hs)))
      nlinarith
    unfold circleDifferenceRatio
    apply (div_le_iff₀ hh0).mpr
    have hmul := mul_le_mul_of_nonneg_left hb2 (sq_nonneg ‖circleSymbol ξ‖)
    nlinarith
lemma circleDifferenceRatio_tendsto (ξ : ℂ) :
    Tendsto (fun h => circleDifferenceRatio h ξ) (𝓝 0) (𝓝 0) := by
  apply squeeze_zero (fun h => circleDifferenceRatio_nonneg h ξ)
    (fun h => circleDifferenceRatio_small h ξ)
  simpa using ((continuous_norm.tendsto (0:ℂ)).const_mul 64).mul_const (‖ξ‖^2)
lemma circleDifferenceRatio_measurable (h : ℂ) : StronglyMeasurable (circleDifferenceRatio h) := by
  unfold circleDifferenceRatio
  have hc : StronglyMeasurable circleSymbol := by
    have h' : Continuous (fun p : ℂ × Angles => planePhase (direction p.2) p.1) := by
      unfold planePhase
      exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        ((direction_continuous.comp continuous_snd).inner continuous_fst)
    exact h'.stronglyMeasurable.integral_prod_right'
  exact ((hc.norm.pow 2).mul ((continuous_const.sub (planePhase_continuous h)).stronglyMeasurable.norm.pow 2)).div stronglyMeasurable_const
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
lemma planeL2_norm_sq (g : ComplexPlaneL2) : ‖g‖^2 = ∫ x, ‖g x‖^2 ∂volume := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
lemma circleDifference_norm_sq (g : ComplexPlaneL2) (h : ℂ) :
    ‖circleOperator (g-planeTranslate h g)‖^2 / ‖h‖ =
      ∫ ξ, circleDifferenceRatio h ξ * ‖𝓕 g ξ‖^2 ∂volume := by
  have hn := (Lp.fourierTransformₗᵢ ℂ ℂ).norm_map (circleOperator (g-planeTranslate h g))
  change ‖𝓕 (circleOperator (g-planeTranslate h g))‖ = _ at hn
  rw [← hn, fourier_circleOperator]
  have hs : 𝓕 (g-planeTranslate h g) = 𝓕 g - phaseMultiplier h (𝓕 g) := by
    change (Lp.fourierTransformₗᵢ ℂ ℂ) (g-planeTranslate h g) = _
    rw [map_sub]
    exact congrArg (fun f => 𝓕 g-f) (fourier_planeTranslate h g)
  rw [hs,planeL2_norm_sq,← integral_div]
  apply integral_congr_ae
  filter_upwards [circleMultiplier_ae (𝓕 g-phaseMultiplier h (𝓕 g)),
    Lp.coeFn_sub (𝓕 g) (phaseMultiplier h (𝓕 g)), phaseMultiplier_ae h (𝓕 g)] with ξ hc hs hp
  rw [hc,hs,Pi.sub_apply,hp]
  have he : 𝓕 g ξ-planePhase h ξ*𝓕 g ξ = (1-planePhase h ξ)*𝓕 g ξ := by ring
  rw [he,norm_mul,norm_mul]
  unfold circleDifferenceRatio
  ring
lemma circle_smoothing_L2 (g : ComplexPlaneL2) :
    Tendsto (fun h : ℂ => ‖circleOperator (g-planeTranslate h g)‖^2 / ‖h‖)
      (𝓝 0) (𝓝 0) := by
  simp_rw [circleDifference_norm_sq]
  have hg : Integrable (fun ξ => ‖𝓕 g ξ‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (𝓕 g))).mp (Lp.memLp (𝓕 g))
  have hd := tendsto_integral_filter_of_dominated_convergence
    (fun ξ : ℂ => 25600*‖𝓕 g ξ‖^2)
    (F := fun h ξ => circleDifferenceRatio h ξ * ‖𝓕 g ξ‖^2)
    (f := fun _ => (0:ℝ)) (l := 𝓝 (0:ℂ))
    (Eventually.of_forall fun h =>
      ((circleDifferenceRatio_measurable h).mul ((Lp.stronglyMeasurable (𝓕 g)).norm.pow 2)).aestronglyMeasurable)
    (Eventually.of_forall fun h => Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (circleDifferenceRatio_nonneg h ξ) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (circleDifferenceRatio_bound h ξ) (sq_nonneg _))
    (hg.const_mul 25600)
    (Eventually.of_forall fun ξ => by simpa using (circleDifferenceRatio_tendsto ξ).mul_const (‖𝓕 g ξ‖^2))
  simpa using hd
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
lemma ae_circle_pullback {p : ℂ → Prop} (hp : ∀ᵐ x ∂(volume : Measure ℂ), p x) :
    ∀ᵐ q ∂(volume : Measure ℂ), ∀ᵐ t ∂angularMeasure, p (q+direction t) := by
  have hq : QuasiMeasurePreserving (fun z : ℂ × Angles => z.1+direction z.2)
      (volume.prod angularMeasure) volume :=
    QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (direction_continuous.measurable.comp measurable_snd))
      (Eventually.of_forall fun t => (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving)
  exact Measure.ae_ae_of_ae_prod (hq.ae hp)
def circleAverage (f : ℂ → ℂ) (q : ℂ) : ℂ := ∫ t, f (q+direction t) ∂angularMeasure
lemma circleOperator_toLp_ae {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    circleOperator (hf.toLp f) =ᵐ[volume] circleAverage f := by
  filter_upwards [circleOperator_ae (hf.toLp f),ae_circle_pullback (MemLp.coeFn_toLp hf)] with q hq he
  exact hq.trans (integral_congr_ae he)
lemma circleOperator_difference_ae {f : ℂ → ℂ} (hf : MemLp f 2 volume) (h : ℂ) :
    circleOperator (hf.toLp f-planeTranslate h (hf.toLp f)) =ᵐ[volume]
      circleAverage (fun q => f q-f (q+h)) := by
  have hfh : MemLp (fun q => f (q+h)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume h)
  have he : (hf.sub hfh).toLp (fun q => f q-f (q+h)) = hf.toLp f-planeTranslate h (hf.toLp f) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hf.sub hfh),Lp.coeFn_sub (hf.toLp f) (planeTranslate h (hf.toLp f)),
      MemLp.coeFn_toLp hf,planeTranslate_ae h (hf.toLp f),
      (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (MemLp.coeFn_toLp hf)] with q h1 h2 h3 h4 h5
    change ((hf.sub hfh).toLp (fun q => f q-f (q+h))) q = _ at h1
    simp only [h1,h2,Pi.sub_apply,h3,h4,h5]
  rw [← he]
  exact circleOperator_toLp_ae (hf.sub hfh)
def colorMass {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (q : ℂ) : ℝ :=
  ∫ t, sampleFn c q 1 i t ∂angularMeasure
lemma colorMass_measurable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (i : Fin k) :
    Measurable (colorMass c i) := by
  have hm : StronglyMeasurable (fun p : ℂ × Angles => sampleFn c p.1 1 i p.2) := by
    simp only [sampleFn,Complex.ofReal_one,one_mul]
    exact (measurable_one.piecewise (measurableSet_eq_fun
      (hc.comp (measurable_fst.add (direction_continuous.measurable.comp measurable_snd))) measurable_const)
      measurable_zero).stronglyMeasurable
  exact hm.integral_prod_right'.measurable
lemma colorMass_nonneg {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (q : ℂ) : 0≤colorMass c i q :=
  integral_nonneg (sampleFn_nonneg c q 1 i)
lemma colorMass_le_one {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (i : Fin k) (q : ℂ) :
    colorMass c i q≤1 := by
  exact (integral_mono ((sampleFn_memLp c hc q 1 i).integrable (by norm_num)) (integrable_const 1)
    (sampleFn_le_one c q 1 i)).trans_eq (by simp)
def colorCutoff {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (x : ℂ) (R : ℝ) : ℂ → ℂ :=
  (Metric.closedBall x (R+2)).indicator (fun q => if c q=i then 1 else 0)
lemma colorCutoff_memLp {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (i : Fin k) (x : ℂ) (R : ℝ) :
    MemLp (colorCutoff c i x R) 2 volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall x (R+2))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall x (R+2)).measure_lt_top (μ := volume)⟩
  have hm : MeasureTheory.MemLp (fun q : ℂ => if c q=i then (1:ℂ) else 0) 2
      (volume.restrict (Metric.closedBall x (R+2))) := by
    apply MemLp.of_bound ((measurable_one.piecewise (measurableSet_eq_fun hc measurable_const)
      measurable_zero).aestronglyMeasurable) 1
    exact Eventually.of_forall fun q => by simp only [Set.piecewise]; split_ifs <;> simp
  exact (memLp_indicator_iff_restrict measurableSet_closedBall).mpr hm
lemma colorCutoff_sample {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (x q h : ℂ) (R : ℝ)
    (hq : q ∈ Metric.ball x R) (hh : ‖h‖<1) (t : Angles) :
    colorCutoff c i x R (q+direction t+h) = if c (q+direction t+h)=i then 1 else 0 := by
  apply Set.indicator_of_mem
  rw [Metric.mem_closedBall,dist_eq_norm]
  have hn := norm_add_le (q-x) (direction t+h)
  have hn' := norm_add_le (direction t) h
  have hd : ‖direction t‖=1 := Circle.norm_coe _
  have hqr : ‖q-x‖<R := by simpa only [Metric.mem_ball,dist_eq_norm] using hq
  rw [show q+direction t+h-x=(q-x)+(direction t+h) by ring]
  linarith
lemma colorCutoff_circleDifference {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (i : Fin k)
    (x q h : ℂ) (R : ℝ) (hq : q ∈ Metric.ball x R) (hh : ‖h‖<1) :
    circleAverage (fun y => colorCutoff c i x R y-colorCutoff c i x R (y+h)) q =
      ((colorMass c i q-colorMass c i (q+h) : ℝ) : ℂ) := by
  have he (t : Angles) : colorCutoff c i x R (q+direction t)-colorCutoff c i x R (q+direction t+h) =
      ((sampleFn c q 1 i t-sampleFn c (q+h) 1 i t : ℝ) : ℂ) := by
    have h0 := colorCutoff_sample c i x q 0 R hq (by simp) t
    simp only [add_zero] at h0
    rw [h0,colorCutoff_sample c i x q h R hq hh t]
    simp only [sampleFn,Complex.ofReal_one,one_mul,show q+direction t+h=q+h+direction t by ring,
      Complex.ofReal_sub]
    split_ifs <;> simp
  unfold circleAverage
  simp_rw [he,integral_complex_ofReal]
  rw [integral_sub ((sampleFn_memLp c hc q 1 i).integrable (by norm_num))
    ((sampleFn_memLp c hc (q+h) 1 i).integrable (by norm_num))]
  rfl
end EuclideanFiveColor
end

end OAI
