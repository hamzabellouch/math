import OAI.NumberTheory.DirichletL.Eisenstein.SeedHeight

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix

lemma levelThree_integral_eq_translation (M : CubicKubota.levelThree)
    (hc : (M : SL(2,ActualEisensteinCubic.O)) 1 0=0) :
    integralComplexMatrix M.1=complexTranslation (ConcreteTraceCRT.eisEmbedding ((M : SL(2,ActualEisensteinCubic.O)) 0 1)) := by
  have hr := row_eq_one_of_lower_left_zero M hc
  have hd : (M : SL(2,ActualEisensteinCubic.O)) 1 1=1 := by
    simpa [row,Matrix.one_apply] using congrFun hr 1
  have ha : (M : SL(2,ActualEisensteinCubic.O)) 0 0=1 := by
    have hh : (M : SL(2,ActualEisensteinCubic.O)) 0 0 * (M : SL(2,ActualEisensteinCubic.O)) 1 1-
      (M : SL(2,ActualEisensteinCubic.O)) 0 1 * (M : SL(2,ActualEisensteinCubic.O)) 1 0=1 := by
      simpa only [Matrix.det_fin_two] using (M : SL(2,ActualEisensteinCubic.O)).property
    simpa only [hc,hd,mul_zero,mul_one,sub_zero] using hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexTranslation,ha,hc,hd]

lemma periodDomain_unique_translate (z w t : ℂ) (hz : z∈periodDomain) (hw : w∈periodDomain)
    (ht : t∈periodLattice) (he : z=w+t) : z=w := by
  have hf := ZSpan.fract_add_ZSpan periodBasis w ht
  rw [←he,(ZSpan.fract_eq_self (b := periodBasis)).mpr hz,
    (ZSpan.fract_eq_self (b := periodBasis)).mpr hw] at hf
  exact hf

def cuspPeriodRegion : Set HyperbolicSpace :=
  {w | hyperbolicHorizontal w∈periodDomain ∧ 1<hyperbolicHeight w}

lemma cuspPeriodRegion_measurable : MeasurableSet cuspPeriodRegion :=
  (periodDomain_measurable.preimage hyperbolicHorizontal_continuous.measurable).inter
    (measurableSet_Ioi.preimage hyperbolicHeight_continuous.measurable)

lemma kernelProjection_cuspPeriodRegion_injective :
    Set.InjOn (integralOrbitProjection globalKubotaKernel) cuspPeriodRegion := by
  intro u hu v hv he
  obtain ⟨M,hM⟩ := (integralOrbitProjection_eq_iff globalKubotaKernel u v).mp he
  have hMu : integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • v=u := hM
  have hc : (M:SL(2,ActualEisensteinCubic.O)) 1 0=0 := by
    by_contra hn
    have hb := integral_hyperbolicHeight_mul_le_one (M:SL(2,ActualEisensteinCubic.O)) hn v
    rw [hMu] at hb
    have huh : 1<hyperbolicHeight u := hu.2
    have hvh : 1<hyperbolicHeight v := hv.2
    nlinarith [mul_pos (sub_pos.mpr huh) (sub_pos.mpr hvh)]
  let N : CubicKubota.levelThree := ⟨M,globalKubotaKernel_le_levelThree M.2⟩
  have ht := levelThree_integral_eq_translation N hc
  obtain ⟨z,t,htpos,hvrep⟩ := upperPoint_surjective v
  have hua : u=upperPoint (z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)) t htpos := by
    rw [←hMu,←hvrep,ht,complexTranslation_action]
  have hvl : hyperbolicHorizontal v=z := by rw [←hvrep,hyperbolicHorizontal_upperPoint]
  have hul : hyperbolicHorizontal u=z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1) := by
    rw [hua,hyperbolicHorizontal_upperPoint]
  obtain ⟨k,hk⟩ := CubicKubota.levelThree_upper N
  have hper : ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)∈periodLattice := by
    change ConcreteTraceCRT.eisEmbedding ((N:CubicKubota.levelThree).1 0 1)∈periodLattice
    rw [hk,map_mul,map_ofNat]
    exact three_embedding_mem k
  have hehor : hyperbolicHorizontal u=hyperbolicHorizontal v :=
    periodDomain_unique_translate _ _ _ hu.1 hv.1 hper (by rw [hul,hvl])
  have hez : z+ConcreteTraceCRT.eisEmbedding ((M:SL(2,ActualEisensteinCubic.O)) 0 1)=z := by
    simpa only [hul,hvl] using hehor
  rw [hua,hez,←hvrep]

def cuspPeriodStrip (a b : ℝ) : Set HyperbolicSpace :=
  {w | hyperbolicHorizontal w∈periodDomain ∧ hyperbolicHeight w∈Set.Icc a b}

lemma cuspPeriodStrip_measurable (a b : ℝ) : MeasurableSet (cuspPeriodStrip a b) :=
  (periodDomain_measurable.preimage hyperbolicHorizontal_continuous.measurable).inter
    (measurableSet_Icc.preimage hyperbolicHeight_continuous.measurable)

lemma kernelProjection_cuspPeriodStrip_injective (a b : ℝ) (ha : 1<a) :
    Set.InjOn (integralOrbitProjection globalKubotaKernel) (cuspPeriodStrip a b) := by
  apply kernelProjection_cuspPeriodRegion_injective.mono
  intro w hw
  exact ⟨hw.1,ha.trans_le hw.2.1⟩

lemma kernelProjection_cuspPeriodStrip_measurePreserving (a b : ℝ) (ha : 1<a) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      ((integralQuotientVolume globalKubotaKernel).restrict
        (integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip a b)) :=
  kernelProjection_measurePreserving_on _ (cuspPeriodStrip_measurable a b)
    (kernelProjection_cuspPeriodStrip_injective a b ha)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups

def kernelCuspStripSet : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6

lemma kernelCuspStripSet_measurable : MeasurableSet kernelCuspStripSet :=
  (cuspPeriodStrip_measurable 5 6).image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn
    (kernelProjection_cuspPeriodStrip_injective 5 6 (by norm_num))

def kernelCuspStripAverage : KernelQuotientL2→L[ℂ]ℂ :=
  innerSL ℂ (indicatorConstLp 2 kernelCuspStripSet_measurable
    (measure_ne_top (integralQuotientVolume globalKubotaKernel) _) (1:ℂ))

lemma kernelCuspStripAverage_apply (F : KernelQuotientL2) :
    kernelCuspStripAverage F=∫q in kernelCuspStripSet,F q∂integralQuotientVolume globalKubotaKernel :=
  L2.inner_indicatorConstLp_one kernelCuspStripSet_measurable
    (measure_ne_top (integralQuotientVolume globalKubotaKernel) _) F

lemma kernelCuspStripAverage_hyperbolic (F : KernelQuotientL2) :
    kernelCuspStripAverage F=∫w in cuspPeriodStrip 5 6,
      F (integralOrbitProjection globalKubotaKernel w)∂hyperbolicVolume := by
  rw [kernelCuspStripAverage_apply]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hh := (Lp.aestronglyMeasurable F).mono_measure (Measure.restrict_le_self (s := kernelCuspStripSet))
  change AEStronglyMeasurable F ((integralQuotientVolume globalKubotaKernel).restrict
    (integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6)) at hh
  change (∫q in integralOrbitProjection globalKubotaKernel '' cuspPeriodStrip 5 6,
    F q∂integralQuotientVolume globalKubotaKernel)=_
  rw [←hm.map_eq] at hh ⊢
  exact integral_map hm.measurable.aemeasurable hh

def kernelCuspAverageCompact : Set KernelQuotient :=
  {q | kernelQuotientBarrier 2 3 q≤6}

lemma kernelCuspAverageCompact_isCompact : IsCompact kernelCuspAverageCompact :=
  kernelBarrier_sublevel_isCompact 6

lemma kernelCuspStripSet_subset_compact : kernelCuspStripSet⊆kernelCuspAverageCompact := by
  rintro q ⟨w,hw,rfl⟩
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  have hfive : 5≤v := by simpa only [hyperbolicHeight_upperPoint] using hw.2.1
  have hsix : v≤6 := by simpa only [hyperbolicHeight_upperPoint] using hw.2.2
  change cuspBarrier 2 3 (upperPoint z v hv)≤6
  have hh := cuspBarrier_high 2 3 (by norm_num) (by norm_num) 1 z v hv (by linarith)
  simpa only [map_one,one_smul] using hh.le.trans hsix

lemma kernelCuspStripAverage_restrict (F : KernelQuotientL2) :
    kernelCuspStripAverage (kernelMassRestrictionCLM kernelCuspAverageCompact
      kernelCuspAverageCompact_isCompact.measurableSet F)=kernelCuspStripAverage F := by
  rw [kernelCuspStripAverage_apply,kernelCuspStripAverage_apply]
  apply setIntegral_congr_ae kernelCuspStripSet_measurable
  filter_upwards [kernelMassRestriction_coe kernelCuspAverageCompact
    kernelCuspAverageCompact_isCompact.measurableSet F] with q hq
  intro hmem
  exact hq.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact hmem) F)

def kernelCuspAverageFamily (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : ℂ :=
  kernelCuspStripAverage
    (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s)

lemma kernelCuspAverageFamily_meromorphicAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelCuspAverageFamily a b ha hab) (4/3:ℂ) :=
  meromorphicAt_clm kernelCuspStripAverage
    (kernelLocalCorrectedSeed_meromorphicAt kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)

lemma kernelCuspAverageFamily_residue_limit (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspAverageFamily a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspStripAverage (kernelEisensteinResidueVector a b ha hab))) := by
  have hh := kernelCuspStripAverage.continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspStripAverage_restrict,kernelCuspAverageFamily] using hh

lemma kernelCuspAverageFamily_actual_integral (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelCuspAverageFamily a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s (integralOrbitProjection globalKubotaKernel w)∂hyperbolicVolume := by
  rw [kernelCuspAverageFamily,kernelCuspStripAverage_hyperbolic]
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have hlocal := kernelLocalCorrectedSeed_ae_eq kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab s
  have hrestr := ae_restrict_of_ae hlocal (s := kernelCuspStripSet)
  have hp := hm.quasiMeasurePreserving.ae_eq_comp hrestr
  apply integral_congr_ae
  filter_upwards [hp,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  exact hw.trans (Set.indicator_of_mem (kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩) _)

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups Matrix

def spatialComplexSplit : EuclideanSpatial ≃ᵐ ℝ × ℂ :=
  spatialHeightSplit.trans ((MeasurableEquiv.refl ℝ).prodCongr Complex.measurableEquivPi.symm)

lemma spatialComplexSplit_fst (p : EuclideanSpatial) : (spatialComplexSplit p).1=p 2 := rfl
lemma spatialComplexSplit_snd (p : EuclideanSpatial) :
    (spatialComplexSplit p).2=(p 0:ℂ)+(p 1:ℂ)*Complex.I := rfl

lemma spatialComplexSplit_preserves_volume : MeasurePreserving spatialComplexSplit volume volume :=
  ((MeasurePreserving.id volume).prod Complex.volume_preserving_equiv_pi.symm).comp
    spatialHeightSplit_preserves_volume

lemma spatialComplexSplit_coordinates (w : HyperbolicSpace) :
    spatialComplexSplit (hyperbolicEuclideanCoordinates w)=
      (hyperbolicHeight w,hyperbolicHorizontal w) := by
  apply Prod.ext
  · rfl
  · change (hyperbolicHorizontal w).re+(hyperbolicHorizontal w).im*Complex.I=hyperbolicHorizontal w
    exact Complex.re_add_im _

def cuspCoordinateLift (q : ℝ × ℂ) : HyperbolicSpace :=
  euclideanToHyperbolic (spatialComplexSplit.symm q)

lemma cuspCoordinateLift_positive (v : ℝ) (z : ℂ) (hv : 0<v) :
    cuspCoordinateLift (v,z)=upperPoint z v hv := by
  have he : spatialComplexSplit (hyperbolicEuclideanCoordinates (upperPoint z v hv))=(v,z) := by
    simp only [spatialComplexSplit_coordinates,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  have he' := congrArg spatialComplexSplit.symm he
  rw [spatialComplexSplit.symm_apply_apply] at he'
  rw [cuspCoordinateLift,←he',euclideanToHyperbolic_coordinates]

def cuspEuclideanStrip : Set EuclideanSpatial :=
  spatialComplexSplit ⁻¹' (Set.Icc (5:ℝ) 6 ×ˢ periodDomain)

lemma cuspEuclideanStrip_measurable : MeasurableSet cuspEuclideanStrip :=
  spatialComplexSplit.measurable (measurableSet_Icc.prod periodDomain_measurable)

lemma cuspEuclideanStrip_positive : cuspEuclideanStrip⊆euclideanUpperHalf := by
  intro p hp
  have hh : 5≤p 2 := hp.1.1
  change 0<p 2
  linarith

lemma cuspEuclideanStrip_preimage :
    hyperbolicEuclideanCoordinates ⁻¹' cuspEuclideanStrip=cuspPeriodStrip 5 6 := by
  ext w
  change spatialComplexSplit (hyperbolicEuclideanCoordinates w)∈(Set.Icc (5:ℝ) 6 ×ˢ periodDomain) ↔ _
  rw [spatialComplexSplit_coordinates]
  exact and_comm

lemma cuspPeriodStrip_integral_coordinates (g : HyperbolicSpace→ℂ)
    (hg : AEStronglyMeasurable g hyperbolicVolume)
    (hint : IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) volume) :
    (∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,(∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3 := by
  have hm := euclideanToHyperbolic_measurePreserving_on cuspEuclideanStrip
    cuspEuclideanStrip_measurable cuspEuclideanStrip_positive
  rw [cuspEuclideanStrip_preimage] at hm
  have hh := hg.mono_measure (Measure.restrict_le_self (s := cuspPeriodStrip 5 6))
  have he : (∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume)=
      ∫p in cuspEuclideanStrip,g (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
    rw [←hm.map_eq] at hh ⊢
    exact integral_map hm.measurable.aemeasurable hh
  rw [he,hyperbolicEuclidean_setIntegral_complex cuspEuclideanStrip
    cuspEuclideanStrip_measurable cuspEuclideanStrip_positive]
  have hsplit := spatialComplexSplit.measurableEmbedding.setIntegral_map
    (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
    (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) («μ» := (volume : Measure EuclideanSpatial))
  rw [spatialComplexSplit_preserves_volume.map_eq] at hsplit
  have heq : (∫p in cuspEuclideanStrip,g (euclideanToHyperbolic p)/(p 2:ℂ)^3)=
      ∫q in Set.Icc (5:ℝ) 6 ×ˢ periodDomain,g (cuspCoordinateLift q)/(q.1:ℂ)^3 := by
    rw [hsplit]
    simp only [cuspEuclideanStrip,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply,
      spatialComplexSplit_fst]
  rw [heq]
  change (∫q in Set.Icc (5:ℝ) 6 ×ˢ periodDomain,
    g (cuspCoordinateLift q)/(q.1:ℂ)^3 ∂((volume : Measure ℝ).prod volume))=_
  rw [setIntegral_prod _ hint]
  congr 1
  ext v
  exact integral_div ((v:ℂ)^3) (fun z => g (cuspCoordinateLift (v,z)))

lemma hyperbolicEisenstein_continuous (s : ℂ) (hs : 2<s.re) :
    Continuous (hyperbolicEisenstein s) := by
  have hcoord : Continuous (fun p : UpperCoordinates =>
      upperEisenstein p.1.1 p.1.2 p.2 s) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hin : ContinuousAt (fun q : UpperCoordinates => (q,s)) p :=
      continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp (f := fun q : UpperCoordinates => (q,s))
      (upperEisenstein_joint_continuousAt (p,s) hs) hin
  convert hcoord.comp hyperbolicCoordinates_continuous using 1
  ext w
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  simp only [Function.comp_def,hyperbolicEisenstein_upperPoint,hyperbolicCoordinates,
    hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]

lemma spatialComplexSplit_symm_eq (q : ℝ × ℂ) :
    spatialComplexSplit.symm q=WithLp.toLp 2 ![q.2.re,q.2.im,q.1] := by
  apply spatialComplexSplit.injective
  rw [spatialComplexSplit.apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (Complex.re_add_im q.2).symm

lemma spatialComplexSplit_symm_continuous : Continuous spatialComplexSplit.symm := by
  change Continuous (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  fun_prop

lemma cuspCoordinateLift_continuousAt (q : ℝ × ℂ) (hq : 0<q.1) :
    ContinuousAt cuspCoordinateLift q := by
  have hp : 0<(spatialComplexSplit.symm q) 2 := by
    rw [spatialComplexSplit_symm_eq]
    exact hq
  exact (euclideanToHyperbolic_contMDiffAt _ hp).continuousAt.comp
    spatialComplexSplit_symm_continuous.continuousAt

lemma cuspCoordinateLift_weighted_integrable (g : HyperbolicSpace→ℂ) (hg : Continuous g) :
    IntegrableOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ periodDomain) volume := by
  let radiusBound : ℝ := ∑i,‖periodBasis i‖
  have hc : ContinuousOn (fun q : ℝ × ℂ => g (cuspCoordinateLift q)/(q.1:ℂ)^3)
      (Set.Icc (5:ℝ) 6 ×ˢ Metric.closedBall (0:ℂ) radiusBound) := by
    intro q hq
    have hpos : 0<q.1 := lt_of_lt_of_le (by norm_num) hq.1.1
    exact ((hg.continuousAt.comp (cuspCoordinateLift_continuousAt q hpos)).div
      ((Complex.continuous_ofReal.comp continuous_fst).continuousAt.pow 3)
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hpos.ne'))).continuousWithinAt
  apply (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))).mono_set
  intro q hq
  refine ⟨hq.1,?_⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain q.2 hq.2

lemma hyperbolicEisenstein_cusp_average (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume)=
      ∫v in Set.Icc (5:ℝ) 6,
        (((v:ℂ)^s+(v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
          ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3 := by
  rw [cuspPeriodStrip_integral_coordinates _
    (hyperbolicEisenstein_continuous s hs).aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable _ (hyperbolicEisenstein_continuous s hs))]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := lt_of_lt_of_le (by norm_num) hv.1
  have hh : (∫z in periodDomain,hyperbolicEisenstein s (cuspCoordinateLift (v,z)))=
      eisensteinFourierCoefficient v hpos s 0*((9*Real.sqrt 3/2:ℝ):ℂ) := by
    simp_rw [cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint]
    rw [eisensteinFourierCoefficient]
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
      AddChar.map_zero_eq_one,mul_one]
    exact (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (by positivity))).symm
  dsimp only
  rw [hh,eisensteinConstantCoefficient_formula v hpos s hs]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

def cuspMainHeightFactor (s : ℂ) : ℂ :=
  ((6:ℂ)^(s-2)-(5:ℂ)^(s-2))/(s-2)

def cuspScatterHeightFactor (s : ℂ) : ℂ :=
  ((5:ℂ)^(-s)-(6:ℂ)^(-s))/s

lemma cuspHeightPower_integrable (s : ℂ) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^s) (Set.Icc (5:ℝ) 6) volume := by
  apply ContinuousOn.integrableOn_Icc
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s (Or.inr (by linarith [hv.1]))).continuousWithinAt

lemma cuspMainHeightFactor_integral (s : ℂ) (hs : s≠2) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(s-3))=cuspMainHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : s-3≠(-1:ℂ) := by intro h; apply hs; linear_combination h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(s-3+1)-(5:ℂ)^(s-3+1))/(s-3+1)=_
  have he : s-3+1=s-2 := by ring
  rw [he]
  rfl

lemma cuspScatterHeightFactor_integral (s : ℂ) (hs : s≠0) :
    (∫v in Set.Icc (5:ℝ) 6,(v:ℂ)^(-s-1))=cuspScatterHeightFactor s := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (5:ℝ)≤6)]
  have hr : -s-1≠(-1:ℂ) := by intro h; apply hs; linear_combination -h
  rw [integral_cpow (Or.inr ⟨hr,by norm_num⟩)]
  change ((6:ℂ)^(-s-1+1)-(5:ℂ)^(-s-1+1))/(-s-1+1)=_
  have he : -s-1+1=-s := by ring
  rw [he,cuspScatterHeightFactor]
  ring

lemma cuspMainHeightFactor_differentiableAt (s : ℂ) (hs : s≠2) :
    DifferentiableAt ℂ cuspMainHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => z-2) s := differentiableAt_id.sub_const 2
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div hd (sub_ne_zero.mpr hs)

lemma cuspScatterHeightFactor_differentiableAt (s : ℂ) (hs : s≠0) :
    DifferentiableAt ℂ cuspScatterHeightFactor s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => -z) s := differentiableAt_id.neg
  exact ((hd.const_cpow (Or.inl (by norm_num))).sub
    (hd.const_cpow (Or.inl (by norm_num)))).div differentiableAt_id hs

def cuspConstantAverage (s : ℂ) : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(cuspMainHeightFactor s+
    ((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0*cuspScatterHeightFactor s)

lemma hyperbolicEisenstein_cusp_average_eq (s : ℂ) (hs : 2<s.re) :
    (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume)=
      cuspConstantAverage s := by
  have hs2 : s≠2 := by intro he; subst s; norm_num at hs
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  rw [hyperbolicEisenstein_cusp_average s hs]
  have heq : (∫v in Set.Icc (5:ℝ) 6,
      (((v:ℂ)^s+(v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
        ((9*Real.sqrt 3/2:ℝ):ℂ))/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((v:ℂ)^(s-3)+(((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*(v:ℂ)^(-s-1)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by linarith [hv.1])
    have h1 : (v:ℂ)^(s-3)=(v:ℂ)^s/(v:ℂ)^3 := by
      rw [Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    have h2 : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [h1,h2]
    ring
  rw [heq,integral_const_mul,integral_add (cuspHeightPower_integrable _)
    ((cuspHeightPower_integrable _).const_mul _),integral_const_mul,
    cuspMainHeightFactor_integral s hs2,cuspScatterHeightFactor_integral s hs0]
  rfl

lemma cuspConstantAverage_differentiableAt (s : ℂ) (hs : 4/3<s.re) (hs2 : s≠2) :
    DifferentiableAt ℂ cuspConstantAverage s := by
  have hs0 : s≠0 := by intro he; subst s; norm_num at hs
  have hs1 : s≠1 := by intro he; subst s; norm_num at hs
  have hsc : DifferentiableAt ℂ (fun z : ℂ => scatteringCoefficient z 0) s :=
    (arithmeticDirichletSeries_zero_differentiableAt s hs).div_const _
  exact ((cuspMainHeightFactor_differentiableAt s hs2).add
    ((((differentiableAt_const (Real.pi:ℂ)).div (differentiableAt_id.sub_const 1)
      (sub_ne_zero.mpr hs1)).mul hsc).mul
      (cuspScatterHeightFactor_differentiableAt s hs0))).const_mul _

lemma cuspScatterHeightFactor_center_re_pos :
    0<(cuspScatterHeightFactor (4/3:ℂ)).re := by
  have h5 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤5) (-(4/3:ℝ))
  have h6 := Complex.ofReal_cpow (by norm_num : (0:ℝ)≤6) (-(4/3:ℝ))
  norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat] at h5 h6
  have he : cuspScatterHeightFactor (4/3:ℂ)=
      (((5:ℝ)^(-(4/3:ℝ))-(6:ℝ)^(-(4/3:ℝ)))/(4/3:ℝ):ℝ) := by
    rw [cuspScatterHeightFactor,←h5,←h6]
    push_cast
    rfl
  rw [he,Complex.ofReal_re]
  apply div_pos
  · exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by norm_num))
  · norm_num

def cuspConstantAverageResidue : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
    cuspScatterHeightFactor (4/3:ℂ)

lemma cuspConstantAverageResidue_ne_zero : cuspConstantAverageResidue≠0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero cusp_volume_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      constantArithmeticResidue_ne_zero
  · intro he
    have hh := cuspScatterHeightFactor_center_re_pos
    rw [he,Complex.zero_re] at hh
    exact lt_irrefl 0 hh

lemma cuspConstantAverage_oneSidedResidue :
    Tendsto (fun x : ℝ => ((x:ℂ)-(4/3:ℂ))*cuspConstantAverage (x:ℂ))
      (𝓝[>] (4/3:ℝ)) (𝓝 cuspConstantAverageResidue) := by
  have harg : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝 (4/3:ℂ)) := by
    convert Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  have hlinear := harg.sub_const (4/3:ℂ)
  norm_num only [sub_self] at hlinear
  have hm := (cuspMainHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hh := (cuspScatterHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.comp harg
  have hpi : Tendsto (fun x : ℝ => (Real.pi:ℂ)/((x:ℂ)-1))
      (𝓝[>] (4/3:ℝ)) (𝓝 (3*(Real.pi:ℂ))) := by
    convert tendsto_const_nhds.div (harg.sub_const 1) (by norm_num : (4/3:ℂ)-1≠0) using 1 ; ring_nf
  have hall := ((hlinear.mul hm).add
    ((hpi.mul scatteringCoefficient_zero_oneSidedResidue).mul hh)).const_mul
      ((9*Real.sqrt 3/2:ℝ):ℂ)
  convert hall using 1
  · ext x
    dsimp only [cuspConstantAverage,Function.comp_def]
    ring
  · simp only [zero_mul,zero_add,cuspConstantAverageResidue]
    ring_nf

open Filter MeasureTheory
open scoped BigOperators Classical Topology

lemma kernelSpectralResolvent_analyticAt_of_isUnit (z : ℂ)
    (hz : IsUnit (kernelSpectralFormOperator z)) :
    AnalyticAt ℂ kernelSpectralResolvent z := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (Ring.inverse (kernelSpectralFormOperator z))).comp_of_eq
    (kernelSpectralFormInverse_analyticAt_of_isUnit z hz) rfl

lemma kernelEisensteinResolvent_analyticAt_of_isUnit (s : ℂ)
    (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ kernelEisensteinResolvent s := by
  exact (kernelSpectralResolvent_analyticAt_of_isUnit _ hs).comp_of_eq
    (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl

lemma kernelCuspAverageFamily_analyticAt_of_isUnit (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ (kernelCuspAverageFamily a b ha hab) s := by
  have hcor : AnalyticAt ℂ (kernelEisensteinL2Correction a b ha hab) s :=
    ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
      (kernelL2Defect a b ha hab s,kernelEisensteinResolvent s)).comp₂
      ((kernelL2Defect_entire a b ha hab).analyticAt s)
      (kernelEisensteinResolvent_analyticAt_of_isUnit s hs)
  have hlocal : AnalyticAt ℂ
      (kernelLocalCorrectedSeed kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha hab) s :=
    ((kernelLocalSeedL2_entire kernelCuspAverageCompact kernelCuspAverageCompact_isCompact a b ha).analyticAt s).add
      ((ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
        (kernelMassRestrictionCLM kernelCuspAverageCompact kernelCuspAverageCompact_isCompact.measurableSet)
        (kernelEisensteinL2Correction a b ha hab s)).comp_of_eq hcor rfl)
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    kernelCuspStripAverage _).comp_of_eq hlocal rfl

lemma kernelCuspAverageFamily_analyticAt_nonreal (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspAverageFamily a b ha hab) s :=
  kernelCuspAverageFamily_analyticAt_of_isUnit a b ha hab s
    (kernelSpectralFormOperator_isUnit_nonreal _ (kernelEisensteinSpectralParameter_nonreal s hs hi))

def cuspUpperParameterRegion : Set ℂ := {s | (4/3:ℝ)<s.re ∧ 0<s.im}

lemma cuspUpperParameterRegion_isOpen : IsOpen cuspUpperParameterRegion :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma cuspUpperParameterRegion_convex : Convex ℝ cuspUpperParameterRegion :=
  ((convex_Ioi (4/3:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)

lemma cuspConstantAverage_analyticOn_upper : AnalyticOnNhd ℂ cuspConstantAverage cuspUpperParameterRegion := by
  apply (Complex.analyticOnNhd_iff_differentiableOn cuspUpperParameterRegion_isOpen).mpr
  intro s hs
  apply (cuspConstantAverage_differentiableAt s hs.1 ?_).differentiableWithinAt
  intro he
  subst s
  norm_num [cuspUpperParameterRegion] at hs

lemma kernelCuspAverageFamily_eq_upper_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    Set.EqOn (kernelCuspAverageFamily a b ha hab) cuspConstantAverage cuspUpperParameterRegion := by
  have hleft : AnalyticOnNhd ℂ (kernelCuspAverageFamily a b ha hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelCuspAverageFamily_analyticAt_nonreal a b ha hab s (by linarith [hs.1]) hs.2.ne'
  have hstart : (5+Complex.I:ℂ)∈cuspUpperParameterRegion := by
    norm_num [cuspUpperParameterRegion]
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : kernelCuspAverageFamily a b ha hab =ᶠ[𝓝 (5+Complex.I:ℂ)] cuspConstantAverage := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact (hoverlap s hs.1 hs.2).trans (hyperbolicEisenstein_cusp_average_eq s (by linarith [hs.1]))
  exact hleft.eqOn_of_preconnected_of_eventuallyEq cuspConstantAverage_analyticOn_upper
    cuspUpperParameterRegion_convex.isPreconnected hstart hevent

lemma kernelCuspAverageFamily_eq_real_of_upper (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hupper : Set.EqOn (kernelCuspAverageFamily a b ha hab) cuspConstantAverage cuspUpperParameterRegion)
    (x : ℝ) (hx : (4/3:ℝ)<x) (hx2 : x≠2)
    (hunit : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter (x:ℂ)))) :
    kernelCuspAverageFamily a b ha hab (x:ℂ)=cuspConstantAverage (x:ℂ) := by
  have hpath : Tendsto (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have hcont : Continuous (fun t : ℝ => (x:ℂ)+(t:ℂ)*Complex.I) :=
      (Complex.continuous_ofReal.mul_const Complex.I).const_add (x:ℂ)
    have hh := (hcont.tendsto 0).mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using hh
  have hleft := (kernelCuspAverageFamily_analyticAt_of_isUnit a b ha hab (x:ℂ) hunit).continuousAt.tendsto.comp hpath
  have hx2' : (x:ℂ)≠2 := by exact_mod_cast hx2
  have hright := (cuspConstantAverage_differentiableAt (x:ℂ) hx hx2').continuousAt.tendsto.comp hpath
  have hevent : (fun t : ℝ => kernelCuspAverageFamily a b ha hab ((x:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ => cuspConstantAverage ((x:ℂ)+(t:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    apply hupper
    simpa only [cuspUpperParameterRegion,Set.mem_ofPred_eq,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,
      Complex.mul_im,mul_zero,zero_mul,sub_zero,add_zero,zero_add,mul_one] using And.intro hx ht
  exact tendsto_nhds_unique_of_eventuallyEq hleft hright hevent

lemma realAbove_tendsto_complex_punctured :
    Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (4/3:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · convert Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (4/3:ℝ)<x at hx
    change (x:ℂ)≠(4/3:ℂ)
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
    linarith [hx]

lemma kernelEisensteinResidueVector_average_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    kernelCuspStripAverage (kernelEisensteinResidueVector a b ha hab)=cuspConstantAverageResidue := by
  have hupper := kernelCuspAverageFamily_eq_upper_of_overlap a b ha hab hoverlap
  have hleft := (kernelCuspAverageFamily_residue_limit a b ha hab).comp realAbove_tendsto_complex_punctured
  have hunit := realAbove_tendsto_complex_punctured.eventually kernelEisensteinPencil_eventually_isUnit
  have hlt : ∀ᶠx : ℝ in 𝓝[>] (4/3:ℝ),x<2 := by
    have hh : ∀ᶠx : ℝ in 𝓝 (4/3:ℝ),x<2 := Iio_mem_nhds (by norm_num)
    exact hh.filter_mono nhdsWithin_le_nhds
  have hevent : (fun x : ℝ => ((x:ℂ)-4/3)*kernelCuspAverageFamily a b ha hab (x:ℂ))
      =ᶠ[𝓝[>] (4/3:ℝ)] (fun x : ℝ => ((x:ℂ)-4/3)*cuspConstantAverage (x:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin,hunit,hlt] with x hx hux hxx
    rw [kernelCuspAverageFamily_eq_real_of_upper a b ha hab hupper x hx hxx.ne hux]
  exact tendsto_nhds_unique_of_eventuallyEq hleft cuspConstantAverage_oneSidedResidue hevent

lemma kernelEisensteinResidueVector_ne_zero_of_overlap (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hoverlap : ∀s : ℂ,4<s.re → 0<s.im →
      kernelCuspAverageFamily a b ha hab s=
        ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s w∂hyperbolicVolume) :
    kernelEisensteinResidueVector a b ha hab≠0 := by
  intro he
  have hh := kernelEisensteinResidueVector_average_of_overlap a b ha hab hoverlap
  rw [he,map_zero] at hh
  exact cuspConstantAverageResidue_ne_zero hh.symm

end CubicEisenstein

end

end OAI
