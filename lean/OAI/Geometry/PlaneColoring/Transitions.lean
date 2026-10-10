import OAI.Analysis.PlaneSpectrum.CircleOperator

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
def transitionSet (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) : Set ℂ :=
  {q | q ∈ Metric.ball x R ∧ ((c q=i ∧ c (q+h)=j) ∨ (c q=j ∧ c (q+h)=i))}
lemma transitionSet_measurable (hc : Measurable c) (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) :
    MeasurableSet (transitionSet c i j x R h) := by
  exact measurableSet_ball.inter (((measurableSet_eq_fun hc measurable_const).inter
    (measurableSet_eq_fun (hc.comp (measurable_id.add_const h)) measurable_const)).union
    ((measurableSet_eq_fun hc measurable_const).inter
    (measurableSet_eq_fun (hc.comp (measurable_id.add_const h)) measurable_const)))
lemma transitionSet_finite (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) :
    volume (transitionSet c i j x R h) < ⊤ :=
  (measure_mono (fun _ hq => Metric.ball_subset_closedBall hq.1)).trans_lt
    (isCompact_closedBall x R).measure_lt_top
def transitionRatio (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) : ENNReal :=
  volume (transitionSet c i j x R h) / ENNReal.ofReal ‖h‖
def TransitionEdge (i j : Fin k) (x : ℂ) : Prop :=
  i ≠ j ∧ ∀ R : ℝ, 0<R → 0 < limsup (transitionRatio c i j x R) (𝓝[≠] (0:ℂ))
lemma transition_abundance {i j : Fin k} {x : ℂ} (he : TransitionEdge c i j x)
    {R : ℝ} (hR : 0<R) : ∃ a : ℝ, 0<a ∧
      ∃ᶠ h in 𝓝[≠] (0:ℂ), a*‖h‖ < volume.real (transitionSet c i j x R h) := by
  obtain ⟨a,_,ha,hal⟩ := ENNReal.lt_iff_exists_real_btwn.mp (he.2 R hR)
  have ha0 : 0<a := ENNReal.ofReal_pos.mp ha
  refine ⟨a,ha0,?_⟩
  have hf := frequently_lt_of_lt_limsup (h := hal)
  refine (hf.and_eventually self_mem_nhdsWithin).mono ?_
  intro h hh
  have hne : h≠0 := hh.2
  have hn : ENNReal.ofReal ‖h‖≠0 := (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hne)).ne'
  have hm : ENNReal.ofReal a*ENNReal.ofReal ‖h‖ < volume (transitionSet c i j x R h) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hn) (Or.inl ENNReal.ofReal_ne_top)).mp hh.1
  rw [← ENNReal.ofReal_mul ha0.le] at hm
  exact (ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg ha0.le (norm_nonneg h)) (transitionSet_finite c i j x R h).ne).mp hm
lemma colorMass_own_zero (hc : Measurable c) (hw : WeakColoring k c) {q : ℂ}
    (hq : Typical c q) (hs : TypicalSampling c q 1) : colorMass c (c q) q=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hs.2] with t ht
  simp only [Complex.ofReal_one,one_mul] at ht
  have hn : c (q+direction t)≠c q := by
    intro he
    have hd : ‖q-(q+direction t)‖=1 := by
      simp only [sub_add_cancel_left,norm_neg]
      exact Circle.norm_coe _
    exact weak_density_proper c hc hw (c q) hd hq (by simpa only [Typical,he] using ht)
  simp only [sampleFn,Complex.ofReal_one,one_mul,ite_eq_right hn,Pi.zero_apply]
lemma exists_energy_small {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {T : Set X} (hT : MeasurableSet T) (hfin : μ T < ⊤) {E : X → ℝ}
    (hE : Integrable E μ) (hn : ∀ᵐ q ∂μ, 0≤E q) {P : X → Prop} (hP : ∀ᵐ q ∂μ, P q)
    {d : ℝ} (hi : (∫ q, E q ∂μ) < d*μ.real T) : ∃ q ∈ T, P q ∧ E q<d := by
  by_contra! h
  have : IsFiniteMeasure (μ.restrict T) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  have hge : ∀ᵐ q ∂μ.restrict T, d≤E q := by
    filter_upwards [ae_restrict_mem hT,ae_restrict_of_ae hP] with q hq hp
    exact h q hq hp
  have hl := integral_mono_ae (integrable_const d) hE.restrict hge
  have hr := integral_mono_measure (μ.restrict_le_self (s := T)) hn hE
  have he : (∫ _q in T, d ∂μ)=d*μ.real T := by simp [mul_comm]
  rw [he] at hl
  exact (not_lt_of_ge (hl.trans hr)) hi
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
def colorError (i : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) : ComplexPlaneL2 :=
  let g := (colorCutoff_memLp c hc i x R).toLp (colorCutoff c i x R)
  circleOperator (g-planeTranslate h g)
lemma colorError_ae (i : Fin k) (x : ℂ) (R : ℝ) {h : ℂ} (hh : ‖h‖<1) :
    ∀ᵐ q ∂(volume : Measure ℂ), q ∈ Metric.ball x R →
      colorError c hc i x R h q = ((colorMass c i q-colorMass c i (q+h) : ℝ) : ℂ) := by
  filter_upwards [circleOperator_difference_ae (colorCutoff_memLp c hc i x R) h] with q hq hB
  exact hq.trans (colorCutoff_circleDifference c hc i x q h R hB hh)
lemma colorError_smoothing (i : Fin k) (x : ℂ) (R : ℝ) :
    Tendsto (fun h : ℂ => ‖colorError c hc i x R h‖^2 / ‖h‖) (𝓝 0) (𝓝 0) :=
  circle_smoothing_L2 _
lemma transition_mass_energy (hw : WeakColoring k c) (i j : Fin k) (x : ℂ) (R : ℝ)
    {h : ℂ} (hh : ‖h‖<1) : ∀ᵐ q ∂(volume : Measure ℂ), q ∈ transitionSet c i j x R h →
      (colorMass c i q+colorMass c j q)^2 ≤
        ‖colorError c hc i x R h q‖^2+‖colorError c hc j x R h q‖^2 := by
  filter_upwards [colorError_ae c hc i x R hh,colorError_ae c hc j x R hh,
    ae_density_actual c hc,ae_typicalSampling c hc (by norm_num : (0:ℝ)<1),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (ae_density_actual c hc),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae
      (ae_typicalSampling c hc (by norm_num : (0:ℝ)<1))] with q hi hj hq hqs hqh hqhs hT
  have he_i : ‖colorError c hc i x R h q‖^2=(colorMass c i q-colorMass c i (q+h))^2 := by
    rw [hi hT.1,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have he_j : ‖colorError c hc j x R h q‖^2=(colorMass c j q-colorMass c j (q+h))^2 := by
    rw [hj hT.1,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [he_i,he_j]
  have h0 := colorMass_own_zero c hc hw hq hqs
  have h1 := colorMass_own_zero c hc hw hqh hqhs
  rcases hT.2 with ⟨hqi,hqj⟩ | ⟨hqj,hqi⟩
  · rw [hqi] at h0
    rw [hqj] at h1
    rw [h0,h1]
    nlinarith [sq_nonneg (colorMass c i (q+h))]
  · rw [hqj] at h0
    rw [hqi] at h1
    rw [h0,h1]
    nlinarith [sq_nonneg (colorMass c j (q+h))]
include hc in
lemma transition_small_mass (hw : WeakColoring k c) {i j : Fin k} {x : ℂ}
    (he : TransitionEdge c i j x) {R ε : ℝ} (hR : 0<R) (hε : 0<ε) :
    ∃ q ∈ Metric.ball x R, TypicalSampling c q 1 ∧ colorMass c i q+colorMass c j q<ε := by
  obtain ⟨a,ha,hfreq⟩ := transition_abundance c he hR
  have hlim : Tendsto (fun h : ℂ =>
      (‖colorError c hc i x R h‖^2+‖colorError c hc j x R h‖^2)/‖h‖) (𝓝 0) (𝓝 0) := by
    simp only [add_div]
    simpa only [add_zero] using (colorError_smoothing c hc i x R).add (colorError_smoothing c hc j x R)
  have hsmall : ∀ᶠ h in 𝓝[≠] (0:ℂ),
      (‖colorError c hc i x R h‖^2+‖colorError c hc j x R h‖^2)/‖h‖<ε^2*a :=
    (hlim.eventually (gt_mem_nhds (by positivity))).filter_mono nhdsWithin_le_nhds
  have hnorm : ∀ᶠ h in 𝓝[≠] (0:ℂ), ‖h‖<1 :=
    (continuous_norm.tendsto (0:ℂ)).eventually (by simpa using (gt_mem_nhds (by norm_num : (0:ℝ)<1)))
      |>.filter_mono nhdsWithin_le_nhds
  obtain ⟨h,hab,hsm,hhn,hne⟩ := (hfreq.and_eventually (hsmall.and (hnorm.and self_mem_nhdsWithin))).exists
  have hnpos : 0<‖h‖ := norm_pos_iff.mpr hne
  let E : ℂ → ℝ := fun q => ‖colorError c hc i x R h q‖^2+‖colorError c hc j x R h q‖^2
  have hEi : Integrable (fun q => ‖colorError c hc i x R h q‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hEj : Integrable (fun q => ‖colorError c hc j x R h q‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hInt : (∫ q, E q ∂volume) < ε^2*volume.real (transitionSet c i j x R h) := by
    rw [show (∫ q, E q ∂volume) = ‖colorError c hc i x R h‖^2+‖colorError c hc j x R h‖^2 by
      dsimp only [E]
      rw [integral_add hEi hEj,← planeL2_norm_sq,← planeL2_norm_sq]]
    have hs := (div_lt_iff₀ hnpos).mp hsm
    have hab' := mul_lt_mul_of_pos_left hab (sq_pos_of_pos hε)
    nlinarith
  obtain ⟨q,hq,hqs,henergy⟩ := exists_energy_small volume (transitionSet_measurable c hc i j x R h)
    (transitionSet_finite c i j x R h) (hEi.add hEj)
    (Eventually.of_forall fun q => add_nonneg (sq_nonneg _) (sq_nonneg _))
    ((ae_typicalSampling c hc (by norm_num : (0:ℝ)<1)).and (transition_mass_energy c hc hw i j x R hhn)) hInt
  refine ⟨q,hq.1,hqs.1,?_⟩
  have hm := hqs.2 hq
  change E q<ε^2 at henergy
  change (colorMass c i q+colorMass c j q)^2≤E q at hm
  nlinarith
end EuclideanFiveColor
end

end OAI
