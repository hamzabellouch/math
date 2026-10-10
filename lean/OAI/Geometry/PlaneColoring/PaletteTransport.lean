import OAI.Geometry.PlaneColoring.PaletteDensity

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma angleRep_preserving (a : ℝ) :
    MeasurePreserving (fun t : Angles => (AddCircle.equivIoc (2*Real.pi) a t : ℝ))
      volume (volume.restrict (Ioc a (a+2*Real.pi))) :=
  (measurePreserving_subtype_coe measurableSet_Ioc).comp (AddCircle.measurePreserving_equivIoc _)
lemma weak_lift_Ioc {F : ℕ → Angles → ℝ} {b : Angles → ℝ}
    (hw : ∀ v : Angles → ℝ, Integrable v angularMeasure →
      Tendsto (fun n => ∫ t, F n t*v t ∂angularMeasure) atTop (𝓝 (∫ t, b t*v t ∂angularMeasure)))
    (a : ℝ) (v : ℝ → ℝ) (hv : Integrable v (volume.restrict (Ioc a (a+2*Real.pi)))) :
    Tendsto (fun n => ∫ t in Ioc a (a+2*Real.pi), F n (t : Angles)*v t) atTop
      (𝓝 (∫ t in Ioc a (a+2*Real.pi), b (t : Angles)*v t)) := by
  let V : Angles → ℝ := AddCircle.liftIoc (2*Real.pi) a v
  have hvi : Integrable V (volume : Measure Angles) := (angleRep_preserving a).integrable_comp_of_integrable hv
  have hva : Integrable V angularMeasure := by
    rw [AddCircle.volume_eq_smul_haarAddCircle] at hvi
    exact (integrable_smul_measure (by positivity : ENNReal.ofReal (2*Real.pi) ≠ 0) (ENNReal.ofReal_ne_top)).mp hvi
  have h := (hw V hva).const_mul (2*Real.pi)
  have he (f : Angles → ℝ) : (∫ t in Ioc a (a+2*Real.pi), f (t : Angles)*v t) =
      (2*Real.pi)*(∫ t, f t*V t ∂angularMeasure) := by
    have hpre := AddCircle.integral_preimage (2*Real.pi) a (fun t => f t*V t)
    have hi : (∫ t in Ioc a (a+2*Real.pi), f (t : Angles)*v t) =
        ∫ t in Ioc a (a+2*Real.pi), f (t : Angles)*V (t : Angles) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change f (t : Angles)*v t=f (t : Angles)*V (t : Angles)
      rw [show V (t : Angles)=v t from AddCircle.liftIoc_coe_apply ht]
    rw [hi,hpre,AddCircle.volume_eq_smul_haarAddCircle,integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.pi),smul_eq_mul]
    rfl
  simpa only [← he] using h
lemma weak_restrict {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : ℕ → X → ℝ} {b : X → ℝ}
    (hw : ∀ v : X → ℝ, Integrable v μ →
      Tendsto (fun n => ∫ t, F n t*v t ∂μ) atTop (𝓝 (∫ t, b t*v t ∂μ)))
    {I : Set X} (hI : MeasurableSet I) :
    ∀ v : X → ℝ, Integrable v (μ.restrict I) →
      Tendsto (fun n => ∫ t, F n t*v t ∂μ.restrict I) atTop
        (𝓝 (∫ t, b t*v t ∂μ.restrict I)) := by
  intro v hv
  have hvi : Integrable (I.indicator v) μ := (integrable_indicator_iff hI).mpr hv
  have h := hw (I.indicator v) hvi
  have he (f : X → ℝ) : (fun t => f t*I.indicator v t)=I.indicator (fun t => f t*v t) := by
    funext t
    by_cases ht : t ∈ I <;> simp [ht]
  simpa only [he,integral_indicator hI] using h
lemma weak_lift_set {F : ℕ → Angles → ℝ} {b : Angles → ℝ}
    (hw : ∀ v : Angles → ℝ, Integrable v angularMeasure →
      Tendsto (fun n => ∫ t, F n t*v t ∂angularMeasure) atTop (𝓝 (∫ t, b t*v t ∂angularMeasure)))
    {I : Set ℝ} (hI : MeasurableSet I) {a : ℝ} (hIa : I ⊆ Ioc a (a+2*Real.pi)) :
    ∀ v : ℝ → ℝ, Integrable v (volume.restrict I) →
      Tendsto (fun n => ∫ t in I, F n (t : Angles)*v t) atTop
        (𝓝 (∫ t in I, b (t : Angles)*v t)) := by
  have h := weak_restrict (weak_lift_Ioc hw a) hI
  simpa only [Measure.restrict_restrict hI,inter_eq_left.mpr hIa] using h
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
lemma weak_strong_disjoint_single {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {F : ℕ → X → ℝ} {b : X → ℝ} {G : ℕ → X → ℝ} {g : X → ℝ}
    (hF : ∀ n, Measurable (F n)) (hb : Measurable b)
    (hG : ∀ n, Measurable (G n)) (hg : Measurable g)
    (hFb : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (hbb : ∀ᵐ x ∂μ, 0 ≤ b x ∧ b x ≤ 1)
    (hGb : ∀ n p, 0 ≤ G n p ∧ G n p ≤ 1)
    (hgb : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (hw : ∀ v : X → ℝ, Integrable v μ →
      Tendsto (fun n => ∫ x, F n x*v x ∂μ) atTop (𝓝 (∫ x, b x*v x ∂μ)))
    (hs : Tendsto (fun n => ∫ p, ‖G n p-g p‖ ∂μ) atTop (𝓝 0))
    (hz : ∀ n, ∀ᵐ p ∂μ, F n p*G n p=0) :
    ∀ᵐ p ∂μ, b p*g p=0 := by
  have hgi : Integrable g (μ) := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs,abs_of_nonneg (hgb p).1]; exact (hgb p).2)
  have hFi (n : ℕ) : Integrable (fun p : X => F n p*g p) (μ) := by
    apply Integrable.of_bound ((hF n).mul hg).aestronglyMeasurable 1
    exact Eventually.of_forall fun p => by
      change ‖F n p*g p‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hFb n p).1 (hgb p).1)]
      exact (mul_le_of_le_one_left (hgb p).1 (hFb n p).2).trans (hgb p).2
  have hbi : Integrable (fun p : X => b p*g p) (μ) := by
    apply Integrable.of_bound (hb.mul hg).aestronglyMeasurable 1
    filter_upwards [hbb] with p hp
    change ‖b p*g p‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp.1 (hgb p).1)]
    exact (mul_le_of_le_one_left (hgb p).1 hp.2).trans (hgb p).2
  have herr (n : ℕ) : Integrable (fun p => ‖G n p-g p‖) (μ) := by
    apply Integrable.of_bound ((hG n).sub hg).norm.aestronglyMeasurable 1
    exact Eventually.of_forall fun p => by
      rw [norm_norm,Real.norm_eq_abs,abs_le]
      change -1 ≤ G n p-g p ∧ G n p-g p ≤ 1
      constructor <;> linarith [(hGb n p).1,(hGb n p).2,(hgb p).1,(hgb p).2]
  have hi0 : Tendsto (fun n => ∫ p, F n p*g p ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun p => mul_nonneg (hFb n p).1 (hgb p).1) _ hs
    intro n
    apply integral_mono_ae (hFi n) (herr n)
    filter_upwards [hz n] with p hp
    rw [Real.norm_eq_abs]
    calc
      F n p*g p = F n p*(g p-G n p) := by rw [mul_sub,hp,sub_zero]
      _ ≤ |g p-G n p| := by
        calc
          _ ≤ F n p*|g p-G n p| := mul_le_mul_of_nonneg_left (le_abs_self _) (hFb n p).1
          _ ≤ 1*|g p-G n p| := mul_le_mul_of_nonneg_right (hFb n p).2 (abs_nonneg _)
          _ = _ := one_mul _
      _ = |G n p-g p| := abs_sub_comm _ _
  have he0 : (∫ p, b p*g p ∂μ)=0 := tendsto_nhds_unique (hw g hgi) hi0
  exact (integral_eq_zero_iff_of_nonneg_ae
    (hbb.mono fun p hp => mul_nonneg hp.1 (hgb p).1) hbi).mp he0
lemma weak_strong_disjoint_single_eventual {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ]
    {F : ℕ → X → ℝ} {b : X → ℝ} {G : ℕ → X → ℝ} {g : X → ℝ}
    (hF : ∀ n, Measurable (F n)) (hb : Measurable b)
    (hG : ∀ n, Measurable (G n)) (hg : Measurable g)
    (hFb : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (hbb : ∀ᵐ x ∂μ, 0 ≤ b x ∧ b x ≤ 1)
    (hGb : ∀ n p, 0 ≤ G n p ∧ G n p ≤ 1)
    (hgb : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (hw : ∀ v : X → ℝ, Integrable v μ →
      Tendsto (fun n => ∫ x, F n x*v x ∂μ) atTop (𝓝 (∫ x, b x*v x ∂μ)))
    (hs : Tendsto (fun n => ∫ p, ‖G n p-g p‖ ∂μ) atTop (𝓝 0))
    (hz : ∀ᶠ n in atTop, ∀ᵐ p ∂μ, F n p*G n p=0) :
    ∀ᵐ p ∂μ, b p*g p=0 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hz
  exact weak_strong_disjoint_single (fun n => hF (n+N)) hb (fun n => hG (n+N)) hg
    (fun n => hFb (n+N)) hbb (fun n => hGb (n+N)) hgb
    (fun v hv => (tendsto_add_atTop_iff_nat N).mpr (hw v hv))
    ((tendsto_add_atTop_iff_nat N).mpr hs) (fun n => hN _ (Nat.le_add_left N n))
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_trace_branch (hw : WeakColoring k c) {x z : ℂ} {t u a : ℝ}
    (h : Real.sin (u-t) ≠ 0) {P : Set CircleParameter} {I : Set ℝ} {K : ℝ≥0}
    (hP : P ∈ 𝓝 (samplingParameter x z 1))
    (hI : MeasurableSet I) (hIa : I ⊆ Ioc a (a+2*Real.pi))
    (hA : ∀ q ∈ P, AntilipschitzWith K (I.domRestrict (fun v => circleEndpoint h (q,v))))
    (hB : ∀ q ∈ P, ∀ v ∈ I, circleTarget (q,v) ∈ (circleInverseHomeo h).target ∧
      Real.sin ((circleInverse h (circleTarget (q,v))).2-(circleInverse h (circleTarget (q,v))).1) ≠ 0 ∧
      circleEndpoint h (q,v) ∈ Metric.closedBall t 1)
    {b : TraceVector k} (hb : IsTrace c hc z b) (i : Fin k) :
    ∀ᵐ f : ℝ ∂volume.restrict I, traceValue b i (f : Angles)*
      (liftPalette c hc x i).indicator (fun _ => (1 : ℝ)) (circleEndpoint h (samplingParameter x z 1,f))=0 := by
  have : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.mpr
    (ne_of_lt ((measure_mono (hIa.trans Ioc_subset_Icc_self)).trans_lt isCompact_Icc.measure_lt_top))
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall t 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall t 1).measure_lt_top.ne
  have hp : samplingParameter x z 1 ∈ P := mem_of_mem_nhds hP
  obtain ⟨y,r,hy,hyt,hrt,hwt⟩ := trace_realization_weakStar c hc hb
  let p : ℕ → CircleParameter := fun n => samplingParameter x (y n) (r n)
  let p₀ := samplingParameter x z 1
  let T : ℕ → ℝ → ℝ := fun n f => circleEndpoint h (p n,f)
  let S : ℝ → ℝ := fun f => circleEndpoint h (p₀,f)
  have hpt : Tendsto p atTop (𝓝 p₀) := samplingParameter_tendsto hyt hrt
  have hpn : ∀ᶠ n in atTop, p n ∈ P := hpt hP
  have hTm (n : ℕ) : Measurable (T n) :=
    (circleEndpoint_measurable h).comp (measurable_const.prodMk measurable_id)
  have hSm : Measurable S := (circleEndpoint_measurable h).comp (measurable_const.prodMk measurable_id)
  let D := liftPalette c hc x i
  have hDm : MeasurableSet D := liftPalette_measurable c hc x i
  have hDind : Measurable (D.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hDm
  have hs : Tendsto (fun n => ∫ f in I, ‖D.indicator (fun _ => (1 : ℝ)) (T n f)-
      D.indicator (fun _ => (1 : ℝ)) (S f)‖) atTop (𝓝 0) := by
    apply line_indicator_pullback_L1 hTm hSm (isCompact_closedBall t 1) hDm
    · exact hpn.mono fun n hn => hA (p n) hn
    · exact hA p₀ hp
    · exact hpn.mono fun n hn f hf => (hB (p n) hn f hf).2.2
    · exact fun f hf => (hB p₀ hp f hf).2.2
    · filter_upwards [ae_restrict_mem hI] with f hf
      exact ((circleInverse_continuousAt h (hB p₀ hp f hf).1).fst.comp
        circleTarget_continuous.continuousAt).tendsto.comp (hpt.prodMk_nhds tendsto_const_nhds)
  have hz : ∀ᶠ n in atTop, ∀ᵐ f : ℝ ∂volume.restrict I,
      sampleFn c (y n) (r n) i (f : Angles)*D.indicator (fun _ => (1 : ℝ)) (T n f)=0 := by
    filter_upwards [hpn] with n hn
    exact palette_sample_branch_exclusion c hc hw (hy n) i hI
      (line_antilipschitz_qmp (hTm n) (hA (p n) hn))
      (fun f hf => (hB (p n) hn f hf).2.1)
      (fun f hf => circleInverse_sampling h (hB (p n) hn f hf).1)
  have hbb : ∀ᵐ f : ℝ ∂volume.restrict I, 0 ≤ traceValue b i (f : Angles) ∧ traceValue b i (f : Angles) ≤ 1 :=
    ae_restrict_of_ae (angleMk_quasiMeasurePreserving.ae
      (((trace_bounds c hc hb).1 i).and ((trace_bounds c hc hb).2.1 i)))
  have hgi (f : ℝ) : 0 ≤ D.indicator (fun _ => (1 : ℝ)) f ∧ D.indicator (fun _ => (1 : ℝ)) f ≤ 1 := by
    by_cases hf : f ∈ D <;> simp [hf]
  exact weak_strong_disjoint_single_eventual
    (fun n => (sampleFn_measurable c hc (y n) (r n) i).comp angleMk_quasiMeasurePreserving.measurable)
    ((Lp.stronglyMeasurable (traceValue b i)).measurable.comp angleMk_quasiMeasurePreserving.measurable)
    (fun n => hDind.comp (hTm n)) (hDind.comp hSm)
    (fun n f => ⟨sampleFn_nonneg c _ _ _ _,sampleFn_le_one c _ _ _ _⟩) hbb
    (fun n f => hgi (T n f)) (fun f => hgi (S f))
    (weak_lift_set (hwt i) hI hIa) hs hz
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_branch_local (hw : WeakColoring k c) {x z : ℂ} {t u a : ℝ}
    (h : Real.sin (u-t) ≠ 0)
    (he : circleTarget (samplingParameter x z 1,a)=circleSum 1 (t,u))
    (ha : Real.sin (a-u) ≠ 0) :
    ∃ I : Set ℝ, IsOpen I ∧ a ∈ I ∧ ∀ i : Fin k,
      ∀ᵐ f : ℝ ∂volume.restrict I,
        f ∈ liftPalette c hc z i → circleEndpoint h (samplingParameter x z 1,f) ∉ liftPalette c hc x i := by
  obtain ⟨P,I,hP,hp,hI,haI,hIa,K,hA,hB⟩ := circleEndpoint_good_neighborhood h he rfl ha
  refine ⟨I,hI,haI,fun i => ?_⟩
  have ht : ∀ᵐ f : ℝ ∂volume.restrict I, ∀ b ∈ paletteGenerators c hc z i,
      traceValue b.1 i (f : Angles)*(liftPalette c hc x i).indicator (fun _ => (1 : ℝ))
        (circleEndpoint h (samplingParameter x z 1,f))=0 := by
    apply (ae_ball_iff (paletteGenerators_countable c hc z i)).mpr
    intro b _
    exact palette_trace_branch c hc hw h (hP.mem_nhds hp) hI.measurableSet hIa hA hB b.2 i
  filter_upwards [ht] with f hf hfm hxs
  obtain ⟨b,hb,hbf⟩ := mem_iUnion₂.mp (show (f : Angles) ∈ paletteSet c hc z i from hfm)
  have hz := hf b hb
  rw [indicator_of_mem hxs,mul_one] at hz
  exact (ne_of_gt hbf) hz
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma circleInverse_left {t u : ℝ} (h : Real.sin (u-t) ≠ 0) {q : RealPlane}
    (hq : q ∈ (circleInverseHomeo h).source) : circleInverse h (circleSum 1 q)=q := by
  have ht : circleSum 1 q ∈ (circleInverseHomeo h).target := (circleInverseHomeo h).map_source hq
  rw [circleInverse_eq h ht]
  exact (circleInverseHomeo h).left_inv hq
lemma circleEndpoint_eventuallyEq {x z : ℂ} {a : ℝ} {s t : ℝ → ℝ}
    (hs : ContinuousAt s a) (ht : ContinuousAt t a) (h : Real.sin (t a-s a) ≠ 0)
    (he : ∀ᶠ f in 𝓝 a, circleTarget (samplingParameter x z 1,f)=circleSum 1 (s f,t f)) :
    ∀ᶠ f in 𝓝 a, circleEndpoint h (samplingParameter x z 1,f)=s f := by
  have hp : (s a,t a) ∈ (circleInverseHomeo h).source :=
    (show HasStrictFDerivAt (circleSum 1)
      (circleSumDerivEquiv (r := 1) (p := (s a,t a)) (by simpa only [one_mul] using h) : RealPlane →L[ℝ] RealPlane)
      (s a,t a) from circleSum_strict 1 (s a,t a)).mem_toOpenPartialHomeomorph_source
  have hf := (hs.prodMk ht) ((circleInverseHomeo h).open_source.mem_nhds hp)
  filter_upwards [hf,he] with f hf he
  simp only [circleEndpoint,he,circleInverse_left h hf]
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma ae_of_locally_ae {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) {S : Set X} {P : X → Prop}
    (h : ∀x∈S,∃U : Set X,IsOpen U ∧ x∈U ∧ ∀ᵐy∂μ,y∈U → P y) :
    ∀ᵐx∂μ,x∈S → P x := by
  choose U ho hm ha using fun x : S => h x x.2
  obtain ⟨T,hT,hcov⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover U ho
    (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩,hm ⟨x,hx⟩⟩)
  have hh : ∀ᵐy∂μ,∀x∈T,y∈U x → P y := (ae_ball_iff hT).mpr (fun x _ => ha x)
  filter_upwards [hh] with y hy hs
  obtain ⟨x,hx,hyU⟩ := mem_iUnion₂.mp (hcov hs)
  exact hy x hx hyU
lemma ae_restrict_of_locally_ae {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} {S : Set X} {P : X → Prop}
    (hS : MeasurableSet S)
    (h : ∀x∈S,∃U : Set X,IsOpen U ∧ x∈U ∧ ∀ᵐy∂μ.restrict U,P y) :
    ∀ᵐx∂μ.restrict S,P x := by
  apply (ae_restrict_iff' hS).mpr
  apply ae_of_locally_ae μ
  intro x hx
  obtain ⟨U,hU,hxU,ha⟩ := h x hx
  exact ⟨U,hU,hxU,(ae_restrict_iff' hU.measurableSet).mp ha⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_transport_real (hw : WeakColoring k c) {x z : ℂ} {U : Set ℝ} (hU : IsOpen U)
    {s t : ℝ → ℝ} (hs : ContinuousOn s U) (ht : ContinuousOn t U)
    (hnp : ∀ a ∈ U, Real.sin (t a-s a) ≠ 0)
    (hss : ∀ a ∈ U, Real.sin (a-t a) ≠ 0)
    (he : ∀ a ∈ U, circleTarget (samplingParameter x z 1,a)=circleSum 1 (s a,t a)) (i : Fin k) :
    ∀ᵐ f : ℝ ∂volume.restrict U, f ∈ liftPalette c hc z i → s f ∉ liftPalette c hc x i := by
  apply ae_restrict_of_locally_ae hU.measurableSet
  intro a ha
  obtain ⟨I,hI,haI,hb⟩ := palette_branch_local c hc hw (hnp a ha) (he a ha) (hss a ha)
  have heq := circleEndpoint_eventuallyEq (hs.continuousAt (hU.mem_nhds ha))
    (ht.continuousAt (hU.mem_nhds ha)) (hnp a ha)
    ((show ∀ᶠ f in 𝓝 a, f ∈ U from hU.mem_nhds ha).mono fun f hf => he f hf)
  obtain ⟨V,hV,hVo,haV⟩ := mem_nhds_iff.mp heq
  refine ⟨I ∩ V,hI.inter hVo,⟨haI,haV⟩,?_⟩
  have hb' := ae_restrict_of_ae_restrict_of_subset (s := I ∩ V) (t := I) inter_subset_left (hb i)
  filter_upwards [hb',ae_restrict_mem (hI.inter hVo).measurableSet] with f hf hfI
  rw [hV hfI.2] at hf
  exact hf
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
namespace EuclideanFiveColor
lemma endpoint_fiber_nonzero {x z : ℂ} {a ds dt : ℝ} {s t : ℝ → ℝ}
    (hs : HasDerivAt s ds a) (ht : HasDerivAt t dt a) (hds : ds ≠ 0)
    (hn : Real.sin (t a-s a) ≠ 0)
    (he : ∀ᶠ f in 𝓝 a, circleTarget (samplingParameter x z 1,f)=circleSum 1 (s f,t f)) :
    Real.sin (a-t a) ≠ 0 := by
  have hv : HasDerivAt (fun f => circleTarget (samplingParameter x z 1,f))
      (-Real.sin a,Real.cos a) a := by
    simpa only [circleTarget,samplingParameter,one_smul] using
      ((Real.hasDerivAt_cos a).prodMk (Real.hasDerivAt_sin a)).const_add (Complex.equivRealProdCLM (z-x))
  have hc₁ := (Real.hasDerivAt_cos (s a)).comp a hs
  have hc₂ := (Real.hasDerivAt_cos (t a)).comp a ht
  have hs₁ := (Real.hasDerivAt_sin (s a)).comp a hs
  have hs₂ := (Real.hasDerivAt_sin (t a)).comp a ht
  have hw : HasDerivAt (fun f => circleSum 1 (s f,t f))
      (-Real.sin (s a)*ds+-Real.sin (t a)*dt,Real.cos (s a)*ds+Real.cos (t a)*dt) a := by
    have h := (hc₁.add hc₂).prodMk (hs₁.add hs₂)
    convert h using 1; simp [circleSum,Function.comp_def]
  have hd := (hv.congr_of_eventuallyEq (Filter.EventuallyEq.symm he)).unique hw
  have h₁ := congrArg Prod.fst hd
  have h₂ := congrArg Prod.snd hd
  dsimp only at h₁ h₂
  have hid : Real.sin (a-t a)=ds*Real.sin (s a-t a) := by
    rw [Real.sin_sub,Real.sin_sub]
    linear_combination -(Real.cos (t a))*h₁-(Real.sin (t a))*h₂
  rw [hid]
  apply mul_ne_zero hds
  rw [show s a-t a=-(t a-s a) by ring,Real.sin_neg,neg_ne_zero]
  exact hn
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_smooth_transport (hw : WeakColoring k c) {x z : ℂ} {U : Set ℝ} (hU : IsOpen U)
    {s t ds dt : ℝ → ℝ} (hs : ∀ a ∈ U, HasDerivAt s (ds a) a)
    (ht : ∀ a ∈ U, HasDerivAt t (dt a) a) (hds : ∀ a ∈ U, ds a ≠ 0)
    (hnp : ∀ a ∈ U, Real.sin (t a-s a) ≠ 0)
    (he : ∀ a ∈ U, circleTarget (samplingParameter x z 1,a)=circleSum 1 (s a,t a)) (i : Fin k) :
    ∀ᵐ f : ℝ ∂volume.restrict U, f ∈ liftPalette c hc z i → s f ∉ liftPalette c hc x i := by
  apply palette_transport_real c hc hw hU (fun a ha => (hs a ha).continuousAt.continuousWithinAt)
    (fun a ha => (ht a ha).continuousAt.continuousWithinAt) hnp ?_ he i
  intro a ha
  exact endpoint_fiber_nonzero (hs a ha) (ht a ha) (hds a ha) (hnp a ha)
    ((show ∀ᶠ f in 𝓝 a, f ∈ U from hU.mem_nhds ha).mono fun f hf => he f hf)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Set Filter Topology
namespace EuclideanFiveColor
lemma palette_transport_param {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    {x z : ℂ} {a s t Da Ds Dt : ℝ → ℝ}
    (ha : ∀ r, HasDerivAt a (Da r) r) (hpos : ∀ r, (1/2 : ℝ) ≤ Da r)
    (hs : ∀ r, HasDerivAt s (Ds r) r) (ht : ∀ r, HasDerivAt t (Dt r) r)
    (hDs : ∀ r, Ds r ≠ 0) (hnp : ∀ r, Real.sin (t r-s r) ≠ 0)
    (he : ∀ r, circleTarget (samplingParameter x z 1,a r)=circleSum 1 (s r,t r)) (i : Fin k) :
    ∀ᵐ r : ℝ ∂volume, a r ∈ liftPalette c hc z i → s r ∉ liftPalette c hc x i := by
  let e := derivLowerOrderIso ha hpos
  have heq : ∀ r, e r=a r := fun _ => rfl
  have hinv : ∀ y, HasDerivAt e.symm (Da (e.symm y))⁻¹ y := by
    intro y
    apply HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (ha (e.symm y))
      (ne_of_gt (lt_of_lt_of_le (by norm_num) (hpos _)))
    exact Filter.Eventually.of_forall fun r => by rw [← heq,e.apply_symm_apply]
  have h := palette_smooth_transport c hc hw (x := x) (z := z) isOpen_univ
    (s := s ∘ e.symm) (t := t ∘ e.symm)
    (fun y _ => (hs _).comp y (hinv y)) (fun y _ => (ht _).comp y (hinv y))
    (fun y _ => mul_ne_zero (hDs _) (inv_ne_zero (ne_of_gt (lt_of_lt_of_le (by norm_num) (hpos _)))))
    (fun y _ => hnp _) (fun y _ => by simpa only [Function.comp_apply,← heq,e.apply_symm_apply] using he (e.symm y)) i
  rw [Measure.restrict_univ] at h
  have h' := (deriv_lower_qmp ha hpos).ae h
  simpa only [Function.comp_apply,← heq,e.symm_apply_apply] using h'
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
namespace EuclideanFiveColor
def sixty : ℝ := Real.pi/3
lemma sin_sixty_ne : Real.sin sixty ≠ 0 := by
  rw [sixty,Real.sin_pi_div_three]
  positivity
lemma sin_twice_sixty_ne : Real.sin (2*sixty) ≠ 0 := by
  rw [Real.sin_two_mul,sixty,Real.sin_pi_div_three,Real.cos_pi_div_three]
  positivity
lemma sixty_sum (x : ℂ) (a : ℝ) :
    circleTarget (samplingParameter x x 1,a)=circleSum 1 (a+sixty,a-sixty) := by
  simp only [circleTarget,samplingParameter,sub_self,map_zero,one_smul,zero_add]
  ext <;> simp only [circleSum,one_mul,Real.cos_add,Real.cos_sub,Real.sin_add,Real.sin_sub]
  · rw [sixty,Real.cos_pi_div_three]
    ring
  · rw [sixty,Real.cos_pi_div_three]
    ring
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
namespace EuclideanFiveColor
lemma ae_angular_of_ae_line {p : Angles → Prop} (hp : MeasurableSet {t | p t})
    (h : ∀ᵐ t : ℝ ∂volume, p (t : Angles)) : ∀ᵐ t ∂angularMeasure, p t := by
  have hh : ∀ᵐ t ∂(volume : Measure Angles), p t := by
    rw [← (AddCircle.measurePreserving_mk (2*Real.pi) 0).map_eq]
    exact (ae_map_iff (AddCircle.measurePreserving_mk (2*Real.pi) 0).measurable.aemeasurable hp).mpr
      (ae_restrict_of_ae h)
  rw [AddCircle.volume_eq_smul_haarAddCircle] at hh
  exact (Measure.ae_ennreal_smul_measure_iff (by positivity : ENNReal.ofReal (2*Real.pi) ≠ 0)).mp hh
lemma ae_sin_sub_ne_zero (t : ℝ) : ∀ᵐ a : ℝ ∂volume, Real.sin (a-t) ≠ 0 := by
  have hs : {a : ℝ | Real.sin (a-t)=0} ⊆ range (fun n : ℤ => t+n*Real.pi) := by
    intro a ha
    obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp ha
    exact ⟨n,by linarith⟩
  change volume {a : ℝ | ¬Real.sin (a-t) ≠ 0}=0
  simpa only [not_not] using measure_mono_null hs ((countable_range _).measure_zero volume)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_sixty_real (hw : WeakColoring k c) (x : ℂ) (i : Fin k) :
    ∀ᵐ f : ℝ ∂volume, f ∈ liftPalette c hc x i → f+sixty ∉ liftPalette c hc x i := by
  have h := palette_transport_real c hc hw (x := x) (z := x) isOpen_univ
    (s := fun a => a+sixty) (t := fun a => a-sixty)
    (continuous_id.add continuous_const).continuousOn (continuous_id.sub continuous_const).continuousOn
    (fun a _ => by
      rw [show (a-sixty)-(a+sixty)=-(2*sixty) by ring,Real.sin_neg,neg_ne_zero]
      exact sin_twice_sixty_ne)
    (fun a _ => by simpa only [sub_sub_cancel] using sin_sixty_ne)
    (fun a _ => sixty_sum x a) i
  simpa only [Measure.restrict_univ] using h
lemma palette_sixty (hw : WeakColoring k c) (x : ℂ) (i : Fin k) :
    ∀ᵐ f ∂angularMeasure, f ∈ paletteSet c hc x i → f+(sixty : Angles) ∉ paletteSet c hc x i := by
  apply ae_angular_of_ae_line
  · simpa only [imp_iff_not_or,Set.compl_def,Set.union_def,Set.preimage,Function.id_def,Set.mem_ofPred_eq] using (paletteSet_measurable c hc x i).compl.union
      (((paletteSet_measurable c hc x i).preimage (measurable_id.add_const (sixty : Angles))).compl)
  · simpa only [liftPalette,mem_preimage,AddCircle.coe_add] using palette_sixty_real c hc hw x i
lemma palette_sixty_disjoint (hw : WeakColoring k c) (x : ℂ) :
    ∀ᵐ f ∂angularMeasure, Disjoint (palette c hc x f) (palette c hc x (f+(sixty : Angles))) := by
  filter_upwards [ae_all_iff.mpr (fun i => palette_sixty c hc hw x i)] with f hf
  exact Finset.disjoint_left.mpr fun i hi hj => hf i ((mem_palette c hc x f i).mp hi)
    ((mem_palette c hc x (f+(sixty : Angles)) i).mp hj)
end EuclideanFiveColor
end

end OAI
