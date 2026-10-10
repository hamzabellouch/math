import OAI.Geometry.PlaneColoring.BinaryDynamics
import OAI.Geometry.PlaneColoring.CircleMaps

namespace OAI

noncomputable section
open MeasureTheory Set Filter Topology
namespace EuclideanFiveColor
/-- A uniformly bounded nonnegative sequence converging locally in L¹ on a conull open
cover converges globally in L¹ for a finite inner-regular measure. -/
lemma tendsto_integral_of_local_cover {X I : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [Measure.InnerRegularCompactLTTop μ] {F : ℕ → X → ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hb : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (V : I → Set X) (hVo : ∀ i, IsOpen (V i)) (hfull : ∀ᵐ x ∂μ, x ∈ ⋃ i, V i)
    (hlocal : ∀ i, Tendsto (fun n => ∫ x in V i, F n x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hKU,hK,hμK⟩ := (isOpen_iUnion hVo).measurableSet.exists_isCompact_sdiff_lt
    (measure_ne_top μ _) (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (half_pos hε)))
  have hδ : μ Kᶜ < ENNReal.ofReal (ε/2) := by
    have he : (Kᶜ : Set X) =ᵐ[μ] ((⋃ i, V i) \ K : Set X) := by
      filter_upwards [hfull] with x hx
      exact propext ⟨fun h => ⟨hx,h⟩,fun h => h.2⟩
    exact (measure_congr he).trans_lt hμK
  have hδr : μ.real Kᶜ < ε/2 := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (ENNReal.ofReal_ne_top)).mpr hδ
    simpa only [Measure.real,ENNReal.toReal_ofReal (le_of_lt (half_pos hε))] using hh
  obtain ⟨J,hJ⟩ := hK.elim_finite_subcover V hVo hKU
  have hlim : Tendsto (fun n => ∑ i ∈ J, ∫ x in V i, F n x ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum J (fun i _ => hlocal i)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hmaj : (∫ x, F n x ∂μ) ≤ (∑ i ∈ J, ∫ x in V i, F n x ∂μ) + μ.real Kᶜ := by
    have hJJ : Integrable (fun x => ∑ i ∈ J, (V i).indicator (F n) x) μ :=
      integrable_finsetSum J (fun i _ => (hF n).indicator (hVo i).measurableSet)
    have hCC : Integrable (Kᶜ.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const _).indicator hK.measurableSet.compl
    have hi := integral_mono (hF n) (hJJ.add hCC) (fun x => by
      have hs (i : I) : 0 ≤ (V i).indicator (F n) x := indicator_nonneg (fun y _ => (hb n y).1) x
      by_cases hx : x ∈ K
      · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hJ hx)
        have hsum := Finset.single_le_sum (fun j _ => hs j) hi
        simp only [Pi.add_apply,indicator_of_notMem (show x ∉ Kᶜ from not_not.mpr hx),add_zero]
        exact (by simpa only [indicator_of_mem hxi] using hsum)
      · change F n x ≤ (∑ i ∈ J, (V i).indicator (F n) x) + Kᶜ.indicator (fun _ => (1 : ℝ)) x
        rw [indicator_of_mem hx]
        linarith [Finset.sum_nonneg (fun i (_ : i ∈ J) => hs i), (hb n x).2])
    apply hi.trans_eq
    refine (integral_add hJJ hCC).trans ?_
    apply congrArg₂ (·+·)
    · exact (integral_finsetSum J (fun i _ => (hF n).indicator (hVo i).measurableSet)).trans
        (Finset.sum_congr rfl (fun i _ => integral_indicator (hVo i).measurableSet))
    · rw [integral_indicator hK.measurableSet.compl]
      simp only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => (hb n x).1)]
  have hh := hN n hn
  have hs0 : 0 ≤ ∑ i ∈ J, ∫ x in V i, F n x ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg (fun x => (hb n x).1)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hs0] at hh
  linarith
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma bounded_difference_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    Integrable (fun x => ‖f x-g x‖) μ := by
  apply Integrable.of_bound ((hf.sub hg).norm.aestronglyMeasurable) 1
  exact Eventually.of_forall fun x => by
    rw [norm_norm,Real.norm_eq_abs,abs_le]
    change -1 ≤ f x-g x ∧ f x-g x ≤ 1
    constructor <;> linarith [(hfb x).1,(hfb x).2,(hgb x).1,(hgb x).2]
lemma circleSum_tendsto_L1 {μ : Measure RealPlane} [IsFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] (hμ : μ ≤ volume)
    {r : ℕ → ℝ} {y : ℕ → RealPlane} {x : RealPlane}
    (hr : Tendsto r atTop (𝓝 1)) (hy : Tendsto y atTop (𝓝 x))
    {f : RealPlane → ℝ} (hf : Measurable f) (hfb : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    Tendsto (fun n => ∫ q, ‖f (y n+circleSum (r n) q)-f (x+circleSum 1 q)‖ ∂μ) atTop (𝓝 0) := by
  classical
  let T : ℕ → RealPlane → RealPlane := fun n q => y n+circleSum (r n) q
  let S : RealPlane → RealPlane := fun q => x+circleSum 1 q
  have hT (n : ℕ) : Measurable (T n) := (continuous_const.add (circleSum_continuous _)).measurable
  have hS : Measurable S := (continuous_const.add (circleSum_continuous _)).measurable
  let R : Set RealPlane := {p | Real.sin (p.2-p.1) ≠ 0}
  have hex : ∀ p : R, ∃ V : Set RealPlane, IsOpen V ∧ p.1 ∈ V ∧
      ∃ K : ℝ≥0, AntilipschitzWith K (V.domRestrict (circleSum 1)) := by
    intro p
    exact circleSum_local_antilipschitz (by simpa only [one_mul] using (show Real.sin (p.1.2-p.1.1) ≠ 0 from p.2))
  choose V hVo hpV K hK using hex
  have hfull : ∀ᵐ q ∂μ, q ∈ ⋃ p : R, V p := by
    filter_upwards [circleSum_regular_ae.filter_mono (ae_mono hμ)] with q hq
    exact mem_iUnion.mpr ⟨⟨q,hq⟩,hpV ⟨q,hq⟩⟩
  apply tendsto_integral_of_local_cover (μ := μ)
    (fun n => bounded_difference_integrable (hf.comp (hT n)) (hf.comp hS)
      (fun q => hfb (T n q)) (fun q => hfb (S q)))
    (fun n q => ⟨norm_nonneg _,by
      rw [Real.norm_eq_abs,abs_le]
      change -1 ≤ f (T n q)-f (S q) ∧ f (T n q)-f (S q) ≤ 1
      constructor <;> linarith [(hfb (T n q)).1,(hfb (T n q)).2,(hfb (S q)).1,(hfb (S q)).2]⟩)
    V hVo hfull
  intro p
  let B := Metric.closedBall x (4 : ℝ)
  let ν : Measure RealPlane := volume.restrict B
  have hB : MeasurableSet B := measurableSet_closedBall
  let : IsFiniteMeasure ν := ⟨by simpa [ν] using (isCompact_closedBall x 4).measure_lt_top⟩
  have hfi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hfb z).1]; exact (hfb z).2)
  have hmapT : ∀ᶠ n in atTop, ((μ.restrict (V p)).map (T n)) ≤
      (((2*K p)^2 : ℝ≥0) : ENNReal) • ν := by
    filter_upwards [circleSum_eventual_image hr hy,circleSum_eventual_antilipschitz (hK p) hr y] with n hn ha
    apply (Measure.map_mono (Measure.restrict_mono_measure hμ (V p)) (hT n)).trans
    exact map_restrict_volume_le (hT n) hB ha (fun q _ => hn q)
  have hmapS : ((μ.restrict (V p)).map S) ≤ (((2*K p)^2 : ℝ≥0) : ENNReal) • ν := by
    apply (Measure.map_mono (Measure.restrict_mono_measure hμ (V p)) hS).trans
    exact map_restrict_volume_le hS hB (circleSum_limit_antilipschitz (hK p) x)
      (fun q _ => circleSum_limit_image x q)
  apply tendsto_integral_norm_comp_sub_eventual hT hS hmapT hmapS _ hfi
  exact Eventually.of_forall fun q => hy.add (circleSum_parameter_tendsto hr q)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
def angularSum (x : ℂ) (r : ℝ) (p : Angles × Angles) :=
  x+(r : ℂ)*direction p.1+direction p.2
lemma angularSum_measurable (x : ℂ) (r : ℝ) : Measurable (angularSum x r) :=
  (measurable_const.add (measurable_const.mul (direction_continuous.measurable.comp measurable_fst))).add
    (direction_continuous.measurable.comp measurable_snd)
lemma angularSum_chart (x : ℂ) (r : ℝ) (q : RealPlane) :
    angularSum x r (angleChart q) = Complex.equivRealProdCLM.symm
      (Complex.equivRealProdCLM x+circleSum r q) := by
  apply Complex.equivRealProdCLM.injective
  simpa only [angularSum,ContinuousLinearEquiv.apply_symm_apply] using circleSum_chart x r q
lemma angularSum_quasiMeasurePreserving (x : ℂ) {r : ℝ} (hr : r ≠ 0) :
    Measure.QuasiMeasurePreserving (angularSum x r) (angularMeasure.prod angularMeasure) volume := by
  have hreal : Measure.QuasiMeasurePreserving
      (fun q => Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM x+circleSum r q)) volume volume :=
    (Complex.volume_preserving_equiv_real_prod.symm).quasiMeasurePreserving.comp
      ((measurePreserving_add_left volume (Complex.equivRealProdCLM x)).quasiMeasurePreserving.comp
        (circleSum_quasiMeasurePreserving hr))
  refine ⟨angularSum_measurable x r,Measure.AbsolutelyContinuous.mk (fun A hA hz => ?_)⟩
  rw [Measure.map_apply (angularSum_measurable x r) hA]
  have hpre : angleChartMeasure (angleChart ⁻¹' (angularSum x r ⁻¹' A))=0 := by
    apply le_antisymm _ bot_le
    apply (angleChartMeas_le _).trans
    have hz' := hreal.preimage_null hz
    simpa [preimage_preimage,Function.comp_def,angularSum_chart] using le_of_eq hz'
  have hz' : (ENNReal.ofReal (2*Real.pi))^2 *
      (angularMeasure.prod angularMeasure) (angularSum x r ⁻¹' A)=0 := by
    rw [← smul_eq_mul,← Measure.smul_apply,← angleChart_measure,
      Measure.map_apply angleChart_preserving.measurable ((angularSum_measurable x r) hA)]
    exact hpre
  exact (mul_eq_zero.mp hz').resolve_left (by positivity)
lemma angularSum_tendsto_L1 {r : ℕ → ℝ} {y : ℕ → ℂ} {x : ℂ}
    (hr : Tendsto r atTop (𝓝 1)) (hy : Tendsto y atTop (𝓝 x))
    {f : ℂ → ℝ} (hf : Measurable f) (hfb : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    Tendsto (fun n => ∫ p, ‖f (angularSum (y n) (r n) p)-f (angularSum x 1 p)‖
      ∂angularMeasure.prod angularMeasure) atTop (𝓝 0) := by
  have h := circleSum_tendsto_L1 (μ := angleChartMeasure) angleChartMeas_le hr
    (Complex.equivRealProdCLM.continuous.tendsto x |>.comp hy)
    (hf.comp Complex.equivRealProdCLM.symm.continuous.measurable)
    (fun z => hfb (Complex.equivRealProdCLM.symm z))
  have he := h.const_mul (((2*Real.pi)^2)⁻¹)
  simp only [mul_zero] at he
  convert he using 1
  ext n
  simpa only [Function.comp_def,Pi.sub_apply,angularSum_chart] using
    (integral_angular_eq_chart (f := fun p => ‖f (angularSum (y n) (r n) p)-f (angularSum x 1 p)‖)
      (((hf.comp (angularSum_measurable _ _)).sub (hf.comp (angularSum_measurable _ _))).norm))
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Set MeasureTheory
namespace EuclideanFiveColor
def samplingParameter (x y : ℂ) (r : ℝ) : CircleParameter := (Complex.equivRealProdCLM (y-x),r)
lemma samplingParameter_tendsto {x z : ℂ} {y : ℕ → ℂ} {r : ℕ → ℝ}
    (hy : Tendsto y atTop (𝓝 z)) (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => samplingParameter x (y n) (r n)) atTop (𝓝 (samplingParameter x z 1)) :=
  (Complex.equivRealProdCLM.continuous.continuousAt.tendsto.comp (hy.sub_const x)).prodMk_nhds hr
lemma circleTarget_sampling (x y : ℂ) (r f : ℝ) :
    Complex.equivRealProdCLM x + circleTarget (samplingParameter x y r,f) =
      Complex.equivRealProdCLM (y+(r : ℂ)*direction (f : Angles)) := by
  have he : (r : ℂ)*direction (f : Angles)=r • direction (f : Angles) := by simp
  rw [he,map_add,map_smul,direction_realPlane]
  simp only [circleTarget,samplingParameter,map_sub]
  abel
lemma circleInverse_sampling {t u : ℝ} (h : Real.sin (u-t) ≠ 0) {x y : ℂ} {r f : ℝ}
    (ht : circleTarget (samplingParameter x y r,f) ∈ (circleInverseHomeo h).target) :
    y+(r : ℂ)*direction (f : Angles) =
      angularSum x 1 (angleChart (circleInverse h (circleTarget (samplingParameter x y r,f)))) := by
  rw [angularSum_chart,circleInverse_right h ht]
  apply Complex.equivRealProdCLM.injective
  exact (circleTarget_sampling x y r f).symm
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
def binaryPhi (d t : ℝ) : ℝ := t+Real.arctan (d*Real.sin t/(1-d*Real.cos t))
def binaryBeta (d t : ℝ) : ℝ := Real.arccos (Real.sqrt (binaryQ d t)/2)
def binaryTarget (d t : ℝ) : ℝ := -binaryCircleMap d (-t)+Real.pi/3
def binaryOther (d t : ℝ) : ℝ := binaryCircleMap d t+2*(Real.pi/3)
lemma binaryTarget_eq (d t : ℝ) : binaryTarget d t=binaryPhi d t+binaryBeta d t := by
  simp only [binaryTarget,binaryCircleMap,binaryPhi,binaryBeta,binaryQ,Real.sin_neg,Real.cos_neg,
    mul_neg,neg_div,Real.arctan_neg]
  ring
lemma binaryOther_eq (d t : ℝ) : binaryOther d t=binaryPhi d t+Real.pi-binaryBeta d t := by
  dsimp [binaryOther,binaryCircleMap,binaryPhi,binaryBeta]
  ring
lemma binaryPhi_trig {d : ℝ} (hd : |d|<1/2) (t : ℝ) :
    Real.cos (binaryPhi d t)=(Real.cos t-d)/Real.sqrt (binaryQ d t) ∧
    Real.sin (binaryPhi d t)=Real.sin t/Real.sqrt (binaryQ d t) := by
  have hq := binaryQ_range hd t
  have hsq : Real.sqrt (binaryQ d t) ≠ 0 := Real.sqrt_ne_zero'.mpr hq.1
  have hi := binary_arctan_identity d t
  have he : 1+(d*Real.sin t/(1-d*Real.cos t))^2=binaryQ d t/(1-d*Real.cos t)^2 := by
    field_simp [hq.2.2.ne']
    nlinarith [hi]
  have hs : Real.sqrt (1+(d*Real.sin t/(1-d*Real.cos t))^2)=Real.sqrt (binaryQ d t)/(1-d*Real.cos t) := by
    rw [he,Real.sqrt_div hq.1.le,Real.sqrt_sq hq.2.2.le]
  have hcθ : Real.cos (Real.arctan (d*Real.sin t/(1-d*Real.cos t)))=(1-d*Real.cos t)/Real.sqrt (binaryQ d t) := by
    rw [Real.cos_arctan,hs]
    field_simp
  have hsθ : Real.sin (Real.arctan (d*Real.sin t/(1-d*Real.cos t)))=d*Real.sin t/Real.sqrt (binaryQ d t) := by
    rw [Real.sin_arctan,hs]
    field_simp [hq.2.2.ne']
  dsimp [binaryPhi]
  simp only [Real.cos_add,Real.sin_add,hcθ,hsθ]
  constructor
  · field_simp [hq.2.2.ne',hsq]
    linear_combination -d*(Real.sin_sq_add_cos_sq t)
  · field_simp [hq.2.2.ne',hsq]
    ring
lemma binaryBeta_trig {d : ℝ} (hd : |d|<1/2) (t : ℝ) :
    Real.cos (binaryBeta d t)=Real.sqrt (binaryQ d t)/2 ∧
    Real.sin (binaryBeta d t)=Real.sqrt (1-binaryQ d t/4) := by
  have hq := binaryQ_range hd t
  have hs := Real.sq_sqrt hq.1.le
  have hs' : Real.sqrt (binaryQ d t)/2 ≤ 1 := by nlinarith [Real.sqrt_nonneg (binaryQ d t)]
  constructor
  · exact Real.cos_arccos (by linarith [Real.sqrt_nonneg (binaryQ d t)]) hs'
  · dsimp [binaryBeta]
    rw [Real.sin_arccos]
    congr 1
    nlinarith
lemma binary_geometry {d : ℝ} (hd : |d|<1/2) (t : ℝ) :
    d+Real.cos (binaryTarget d t)=Real.cos t+Real.cos (binaryOther d t) ∧
    Real.sin (binaryTarget d t)=Real.sin t+Real.sin (binaryOther d t) := by
  have hp := binaryPhi_trig hd t
  have hb := binaryBeta_trig hd t
  have hq := binaryQ_range hd t
  have hs : Real.sqrt (binaryQ d t) ≠ 0 := Real.sqrt_ne_zero'.mpr hq.1
  rw [binaryTarget_eq,binaryOther_eq,
    show binaryPhi d t+Real.pi-binaryBeta d t=(binaryPhi d t-binaryBeta d t)+Real.pi by ring,
    Real.cos_add_pi,Real.sin_add_pi,Real.cos_add,Real.sin_add,Real.cos_sub,Real.sin_sub,hp.1,hp.2,hb.1,hb.2]
  constructor <;> field_simp <;> ring
lemma binaryTarget_hasDeriv {d : ℝ} (hd : |d|<1/2) (t : ℝ) :
    HasDerivAt (binaryTarget d) (1+d*binaryB d (-t)) t := by
  convert ((binaryCircleMap_hasDeriv_t hd (-t)).comp t (hasDerivAt_neg t)).neg.add_const (Real.pi/3) using 1 <;>
    first | rfl | ring
lemma binaryOther_hasDeriv {d : ℝ} (hd : |d|<1/2) (t : ℝ) :
    HasDerivAt (binaryOther d) (1+d*binaryB d t) t := by
  exact (binaryCircleMap_hasDeriv_t hd t).add_const (2*(Real.pi/3))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma binary_nonparallel {d : ℝ} (hd : |d|<1/2) (t : ℝ) :
    Real.sin (binaryOther d t-t) ≠ 0 := by
  intro hz
  have hq := binaryQ_range (show |-d|<1/2 by simpa only [abs_neg] using hd) (binaryTarget d t)
  have hg := binary_geometry hd t
  have hs := Real.sin_sq_add_cos_sq (binaryOther d t-t)
  rw [hz] at hs
  have hi : binaryQ (-d) (binaryTarget d t)=2+2*Real.cos (binaryOther d t-t) := by
    have hc := Real.sin_sq_add_cos_sq t
    have hh := Real.sin_sq_add_cos_sq (binaryOther d t)
    have ht := Real.sin_sq_add_cos_sq (binaryTarget d t)
    dsimp only [binaryQ]
    rw [Real.cos_sub]
    nlinarith [sq_eq_sq_iff_eq_or_eq_neg.mpr (Or.inl hg.1),sq_eq_sq_iff_eq_or_eq_neg.mpr (Or.inl hg.2)]
  rw [hi] at hq
  nlinarith [sq_nonneg (Real.cos (binaryOther d t-t))]
lemma binary_geometry_rotated {x z : ℂ} {d φ : ℝ} (hd : |d|<1/2)
    (hxr : (z-x).re=d*Real.cos φ) (hxi : (z-x).im=d*Real.sin φ) (t : ℝ) :
    circleTarget (samplingParameter x z 1,binaryTarget d t+φ)=
      circleSum 1 (t+φ,binaryOther d t+φ) := by
  have hg := binary_geometry hd t
  simp only [circleTarget,samplingParameter,one_smul,circleSum,one_mul]
  apply Prod.ext
  · change (z-x).re+Real.cos (binaryTarget d t+φ)=Real.cos (t+φ)+Real.cos (binaryOther d t+φ)
    rw [hxr,Real.cos_add,Real.cos_add,Real.cos_add]
    linear_combination Real.cos φ*hg.1-Real.sin φ*hg.2
  · change (z-x).im+Real.sin (binaryTarget d t+φ)=Real.sin (t+φ)+Real.sin (binaryOther d t+φ)
    rw [hxi,Real.sin_add,Real.sin_add,Real.sin_add]
    linear_combination Real.sin φ*hg.1+Real.cos φ*hg.2
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma deriv_lower_surjective {f D : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (D x) x)
    (hp : ∀ x, (1/2 : ℝ) ≤ D x) : Function.Surjective f := by
  intro y
  let R := 2*(|y-f 0|+1)
  have hR : 0 < R := by dsimp [R]; positivity
  have h₁ := mul_sub_le_image_sub_of_le_deriv (fun x => (hd x).differentiableAt)
    (fun x => by rw [(hd x).deriv]; exact hp x) (show -R ≤ 0 by linarith)
  have h₂ := mul_sub_le_image_sub_of_le_deriv (fun x => (hd x).differentiableAt)
    (fun x => by rw [(hd x).deriv]; exact hp x) hR.le
  have hy : y ∈ Icc (f (-R)) (f R) := by
    constructor <;> dsimp [R] at * <;> linarith [le_abs_self (y-f 0),neg_abs_le (y-f 0)]
  obtain ⟨x,_,hx⟩ := intermediate_value_Icc (by linarith : -R ≤ R)
    (continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)).continuousOn hy
  exact ⟨x,hx⟩
def derivLowerOrderIso {f D : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (D x) x)
    (hp : ∀ x, (1/2 : ℝ) ≤ D x) : ℝ ≃o ℝ :=
  (strictMono_of_deriv_pos (fun x => by rw [(hd x).deriv]; linarith [hp x])).orderIsoOfRightInverse f
    (Function.surjInv (deriv_lower_surjective hd hp)) (Function.rightInverse_surjInv (deriv_lower_surjective hd hp))
end EuclideanFiveColor
end

end OAI
