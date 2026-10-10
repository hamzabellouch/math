import OAI.NumberTheory.DirichletL.Eisenstein.GaussFactorization
import OAI.NumberTheory.DirichletL.Reciprocity.KubotaCharacter

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
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspHeightFourierTest_memLp (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    MemLp (fun w => star (cuspWeightedFourierPhase ρ h w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) := by
  let := cuspPeriodStripFiniteVolume a b ha
  apply MemLp.of_bound (cuspWeightedFourierPhase_continuous ρ h).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star]; exact cuspWeightedFourierPhase_bound ρ h w)

def cuspHeightFourierTestL2 (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : CuspHeightStripL2 a b :=
  (cuspHeightFourierTest_memLp a b ha ρ h).toLp (fun w => star (cuspWeightedFourierPhase ρ h w))

def kernelCuspHeightFourier (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (cuspHeightFourierTestL2 a b ha ρ h)).comp (kernelCuspHeightPullback a b ha)

lemma kernelCuspHeightFourier_integral (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspHeightFourier a b ha ρ h F=∫w in cuspPeriodStrip a b,
      F (integralOrbitProjection globalKubotaKernel w)*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  change inner ℂ (cuspHeightFourierTestL2 a b ha ρ h) (kernelCuspHeightPullback a b ha F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (cuspHeightFourierTest_memLp a b ha ρ h),
    kernelCuspHeightPullback_ae a b ha F] with w hw hp
  rw [RCLike.inner_apply,cuspHeightFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma kernelCuspHeightFourier_restrict (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspHeightFourier a b ha ρ h (kernelMassRestrictionCLM (cuspHeightQuotientCompact a b)
      (cuspHeightQuotientCompact_isCompact a b ha).measurableSet F)=kernelCuspHeightFourier a b ha ρ h F := by
  rw [kernelCuspHeightFourier_integral,kernelCuspHeightFourier_integral]
  have he := (kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp
    (kernelMassRestriction_coe (cuspHeightQuotientCompact a b) (cuspHeightQuotientCompact_isCompact a b ha).measurableSet F)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  exact congrArg (fun z : ℂ => z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem (cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩) _))

def kernelCuspHeightFourierFamily (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) : ℂ :=
  kernelCuspHeightFourier a b ha ρ h
    (kernelLocalCorrectedSeed (cuspHeightQuotientCompact a b) (cuspHeightQuotientCompact_isCompact a b ha)
      2 3 (by norm_num) (by norm_num) s)

lemma kernelCuspHeightFourierFamily_analyticAt_nonreal (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelCuspHeightFourierFamily a b ha ρ h) s := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := ℂ)
    (kernelCuspHeightFourier a b ha ρ h) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal (cuspHeightQuotientCompact a b)
        (cuspHeightQuotientCompact_isCompact a b ha) 2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma kernelCuspHeightFourierFamily_residue_limit (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    Tendsto (fun s : ℂ => (s-4/3)*kernelCuspHeightFourierFamily a b ha ρ h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue)) := by
  have hh := (kernelCuspHeightFourier a b ha ρ h).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit (cuspHeightQuotientCompact a b) (cuspHeightQuotientCompact_isCompact a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,kernelCuspHeightFourier_restrict,
    kernelCuspHeightFourierFamily] using hh

lemma kernelCuspHeightFourierFamily_initial (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspHeightFourierFamily a b ha ρ h s=∫w in cuspPeriodStrip a b,
      hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [kernelCuspHeightFourierFamily,kernelCuspHeightFourier_integral]
  have he := (kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp
    (cubicEisensteinLocalFamily_initial_ae (cuspHeightQuotientCompact a b)
      (cuspHeightQuotientCompact_isCompact a b ha) s hs hi)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩),
    kernelQuotientEisenstein_mk]

def cuspIntervalWhittakerHeightFactor (a b : ℝ)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (h : ActualEisensteinCubic.O) : ℂ :=
  ∫v in Set.Icc a b,ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))

lemma hyperbolicEisenstein_cusp_height_fourier_nonzero (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 2<s.re) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg)]
  have hexp : ∀v∈Set.Icc a b,
      ((∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
        (((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
          (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) := by
    intro v hv
    have hpos : 0<v := ha.trans_le hv.1
    have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ρ v*(eisensteinFourierCoefficient v hpos s h*((9*Real.sqrt 3/2:ℝ):ℂ)) := by
      simp_rw [g,cuspCoordinateLift_positive v _ hpos,hyperbolicEisenstein_upperPoint,
        cuspWeightedFourierPhase,hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      have hrearr : (∫z in periodDomain,upperEisenstein z v hpos s*
          (ρ v*ShortDraftTrace.breveE (-cuspFrequency h*z)))=
          ρ v*(∫z in periodDomain,upperEisenstein z v hpos s*ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      rw [hrearr,eisensteinFourierCoefficient]
      congr 1
      exact (div_mul_cancel₀ _ cusp_volume_ne_zero).symm
    rw [hinner,eisensteinFourierCoefficient_formula v hpos s hs h,ite_eq_right hh,zero_add]
    have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hp : (v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3 := by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hv0]
      congr 1
      exact Complex.cpow_natCast _ 3
    rw [hp]
    ring
  calc
    _ = ∫v in Set.Icc a b,(((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h)*
        (ρ v*((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v))) :=
      setIntegral_congr_fun measurableSet_Icc hexp
    _ = _ := integral_const_mul _ _

lemma kernelCuspHeightFourierFamily_initial_factor (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelCuspHeightFourierFamily a b ha ρ h s=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*scatteringCoefficient s h*cuspIntervalWhittakerHeightFactor a b ρ s h := by
  rw [kernelCuspHeightFourierFamily_initial a b ha ρ h s hs hi,
    hyperbolicEisenstein_cusp_height_fourier_nonzero a b ha ρ s (by linarith) h hh]

lemma cuspIntervalWhittakerHeightFactor_analyticAt (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    AnalyticAt ℂ (fun w => cuspIntervalWhittakerHeightFactor a b ρ w h) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hopen : IsOpen {w : ℂ | 1<w.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  have heq : (fun s => cuspIntervalWhittakerHeightFactor a b ρ s h)=
      (fun s => ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)) := by
    funext s
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => (mul_assoc _ _ _).symm)
  rw [heq]
  exact cuspWeightedWhittakerInterval_differentiableAt ρ a b ha (cuspFrequency h) w hw

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma kernelCuspHeightFourierFamily_cross_identity (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    Set.EqOn (fun s => kernelCuspHeightFourierFamily a b ha ρ h s*cuspWhittakerHeightFactor s h)
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s => kernelCuspHeightFourierFamily a b ha ρ h s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (kernelCuspHeightFourierFamily_analyticAt_nonreal a b ha ρ h s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hright : AnalyticOnNhd ℂ
      (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
        cuspIntervalWhittakerHeightFactor a b ρ s h) domain := by
    intro s hs
    exact (kernelCuspFourierFamily_analyticAt_nonreal h 2 3 (by norm_num) (by norm_num)
      s hs.1.ne' hs.2.ne').mul (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => kernelCuspHeightFourierFamily a b ha ρ h s*cuspWhittakerHeightFactor s h)
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s*
          cuspIntervalWhittakerHeightFactor a b ρ s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [kernelCuspHeightFourierFamily_initial_factor a b ha ρ h hh s hs.1 hs.2,
      kernelCuspFourierFamily_eq_upper h hh ⟨by linarith [hs.1],hs.2⟩]
    ring
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

lemma kernelCuspHeightFourier_residue_factor (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*nonzeroScatteringResidue h*
        cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h := by
  have hbase : Tendsto (fun s : ℂ => cuspWhittakerHeightFactor s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) h)) :=
    (cuspWhittakerHeightFactor_analyticAt h (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hweight : Tendsto (fun s : ℂ => cuspIntervalWhittakerHeightFactor a b ρ s h)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h)) :=
    (cuspIntervalWhittakerHeightFactor_analyticAt a b ha ρ h (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hleft := ((kernelCuspHeightFourierFamily_residue_limit a b ha ρ h).mul hbase).comp
    upperVertical_tendsto_cubic_punctured
  have hright := ((kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num)).mul hweight).comp
    upperVertical_tendsto_cubic_punctured
  have hevent : (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*kernelCuspHeightFourierFamily a b ha ρ h ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h)
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num)
        ((4/3:ℂ)+(t:ℂ)*Complex.I))*cuspIntervalWhittakerHeightFactor a b ρ ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)*Complex.I∈{s : ℂ | 1<s.re ∧ 0<s.im} := by
      constructor
      · norm_num
      · simpa using ht
    have he := kernelCuspHeightFourierFamily_cross_identity a b ha ρ h hh hs
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue*cuspWhittakerHeightFactor (4/3:ℂ) h=
      kernelCuspFourier h cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright hevent
  have hH := cuspWhittakerHeightFactor_center_ne_zero h
  calc
    _ = (kernelCuspFourier h cubicEisensteinResidue*cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h)/
        cuspWhittakerHeightFactor (4/3:ℂ) h := (eq_div_iff hH).mpr heq
    _ = _ := by
      unfold nonzeroScatteringResidue
      field_simp [cusp_volume_ne_zero,hH]

lemma cuspIntervalWhittakerHeightFactor_center_bessel (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cuspIntervalWhittakerHeightFactor a b ρ (4/3:ℂ) h=
      cubicBesselNormalizer h*(∫v in Set.Icc a b,
        ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [cuspIntervalWhittakerHeightFactor,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := ha.trans_le hv.1
  dsimp only
  rw [sourceFourierKernel_cubic_height h hh v hpos]
  ring

lemma kernelCuspHeightFourier_residue_bessel (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFourierCoefficient h*
        (∫v in Set.Icc a b,ρ v*
          (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
  rw [kernelCuspHeightFourier_residue_factor a b ha ρ h hh,
    cuspIntervalWhittakerHeightFactor_center_bessel a b ha ρ h hh,cubicResidualFourierCoefficient]
  ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma kernelCuspHeightFourier_uniform_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(ρ : BoundedContinuousFunction ℝ ℂ)(h : ActualEisensteinCubic.O)(F : KernelQuotientL2),
      ‖kernelCuspHeightFourier a b ha ρ h F‖≤C*‖ρ‖*‖F‖ := by
  let := cuspPeriodStripFiniteVolume a b ha
  let mass : ℝ := (measureUnivNNReal (hyperbolicVolume.restrict (cuspPeriodStrip a b)):ℝ)^((2:ℝ≥0∞).toReal)⁻¹
  have hmass : 0≤mass := Real.rpow_nonneg (by positivity) _
  refine ⟨mass*‖kernelCuspHeightPullback a b ha‖,mul_nonneg hmass (norm_nonneg _),?_⟩
  intro ρ h F
  have htest : ‖cuspHeightFourierTestL2 a b ha ρ h‖≤mass*‖ρ‖ := by
    apply Lp.norm_le_of_ae_bound (norm_nonneg ρ)
    filter_upwards [MemLp.coeFn_toLp (cuspHeightFourierTest_memLp a b ha ρ h)] with w hw
    change ‖cuspHeightFourierTestL2 a b ha ρ h w‖≤‖ρ‖
    rw [cuspHeightFourierTestL2,hw,norm_star]
    exact cuspWeightedFourierPhase_bound ρ h w
  change ‖inner ℂ (cuspHeightFourierTestL2 a b ha ρ h) (kernelCuspHeightPullback a b ha F)‖≤_
  calc
    _ ≤ ‖cuspHeightFourierTestL2 a b ha ρ h‖*‖kernelCuspHeightPullback a b ha F‖ := norm_inner_le_norm _ _
    _ ≤ (mass*‖ρ‖)*(‖kernelCuspHeightPullback a b ha‖*‖F‖) :=
      mul_le_mul htest ((kernelCuspHeightPullback a b ha).le_opNorm F) (norm_nonneg _)
        (mul_nonneg hmass (norm_nonneg _))
    _ = _ := by ring

lemma cubicResidualFourierCoefficient_interval_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖cubicResidualFourierCoefficient h‖*
        ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖≤C := by
  obtain ⟨C,hC,hbound⟩ := kernelCuspHeightFourier_uniform_bound a b ha
  let area : ℂ := ((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea : 0<‖area‖ := norm_pos_iff.mpr cusp_volume_ne_zero
  refine ⟨C*‖cubicEisensteinResidue‖/‖area‖,div_nonneg (mul_nonneg hC (norm_nonneg _)) harea.le,?_⟩
  intro h hh
  have heq := kernelCuspHeightFourier_residue_bessel a b ha (BoundedContinuousFunction.const ℝ (1:ℂ)) h hh
  have hhbound := hbound (BoundedContinuousFunction.const ℝ (1:ℂ)) h cubicEisensteinResidue
  rw [heq] at hhbound
  simp only [BoundedContinuousFunction.const_apply,one_mul,BoundedContinuousFunction.norm_const_eq,
    norm_one,mul_one,norm_mul,mul_assoc] at hhbound
  apply (le_div_iff₀ harea).mpr
  simpa only [area,mul_assoc,mul_comm,mul_left_comm] using hhbound

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

def cubicBesselDensity (x t : ℝ) : ℝ :=
  t^(-(2:ℝ)/3)*Real.exp (-t-x^2/(4*t))

lemma cubicBesselDensity_integrable (x : ℝ) :
    IntegrableOn (cubicBesselDensity x) (Set.Ioi 0) := by
  have hi := (schlafliIntegral_integrable (1/3:ℂ) x (by norm_num)).re
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  dsimp only
  rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,
    schlafliIntegrand_real (1/3) x t ht]
  change t^((1/3:ℝ)-1)*Real.exp (-t-x^2/(4*t))=cubicBesselDensity x t
  norm_num [cubicBesselDensity]

lemma cubicBesselDensity_nonneg (x t : ℝ) (ht : 0≤t) : 0≤cubicBesselDensity x t :=
  mul_nonneg (Real.rpow_nonneg ht _) (Real.exp_pos _).le

lemma schlafliIntegral_cubic_real (x : ℝ) :
    schlafliIntegral (1/3:ℂ) x=((∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t):ℝ) := by
  unfold schlafliIntegral
  calc
    _ = ∫t in Set.Ioi (0:ℝ),((cubicBesselDensity x t:ℝ):ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [show (1/3:ℂ)=((1/3:ℝ):ℂ) by norm_num,
        schlafliIntegrand_real (1/3) x t ht]
      norm_num [cubicBesselDensity]
    _ = _ := integral_ofReal

lemma schlafliBesselK_cubic_real (x : ℝ) (hx : 0<x) :
    schlafliBesselK (1/3:ℂ) x=
      (((1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)):ℝ) := by
  rw [schlafliBesselK,schlafliIntegral_cubic_real]
  have hp := Complex.ofReal_cpow (show 0≤x/2 by positivity) (-(1:ℝ)/3)
  norm_num only [Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,
    Complex.ofReal_ofNat,neg_div] at hp
  rw [←hp]
  push_cast
  ring_nf

lemma schlafliBesselK_cubic_norm_re (x : ℝ) (hx : 0<x) :
    ‖schlafliBesselK (1/3:ℂ) x‖=(schlafliBesselK (1/3:ℂ) x).re := by
  rw [schlafliBesselK_cubic_real x hx,Complex.ofReal_re]
  apply Complex.norm_of_nonneg
  apply mul_nonneg (by positivity)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cubicBesselDensity_nonneg x t ht.le

lemma cubicBesselDensity_upper (x t : ℝ) (ht : 0<t) :
    cubicBesselDensity x t≤Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
  have hq : -t-x^2/(4*t)≤-x/2-t/2 := by
    have hf : x/2-t/2≤x^2/(4*t) :=
      (le_div_iff₀ (show 0<4*t by positivity)).mpr (by
        nlinarith [sq_nonneg (t-x),sq_nonneg t])
    linarith
  have he := Real.exp_le_exp.mpr hq
  unfold cubicBesselDensity
  calc
    _ ≤ t^(-(2:ℝ)/3)*Real.exp (-x/2-t/2) :=
      mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le _)
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add]; ring_nf

lemma cubicBesselIntegral_upper (x : ℝ) :
    (∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)≤
      Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hi : IntegrableOn (fun t : ℝ => t^(-(2:ℝ)/3)*Real.exp (-t/2)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := -(2:ℝ)/3) (p := (1:ℝ)) (b := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simpa only [Real.rpow_one,show ∀t : ℝ,-(1/2)*t=-t/2 by intro t;ring] using h
  have hb := setIntegral_mono_on (cubicBesselDensity_integrable x)
    (hi.const_mul (Real.exp (-x/2))) measurableSet_Ioi (fun t ht => cubicBesselDensity_upper x t ht)
  rw [integral_const_mul] at hb
  have he : (∫t in Set.Ioi (0:ℝ),t^(-(2:ℝ)/3)*Real.exp (-t/2))=
      (2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3) := by
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (1/3:ℝ)) (r := (1/2:ℝ)) (by norm_num) (by norm_num)
    convert hh using 1 <;> norm_num ; congr 2 ; funext t ; ring_nf
  rw [he] at hb
  exact hb

def cubicBesselUpperConstant : ℝ :=
  (1/2:ℝ)*(1/2:ℝ)^(-(1:ℝ)/3)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

lemma cubicBesselUpperConstant_pos : 0<cubicBesselUpperConstant := by
  unfold cubicBesselUpperConstant
  positivity

theorem schlafliBesselK_cubic_upper (x : ℝ) (hx : 1≤x) :
    ‖schlafliBesselK (1/3:ℂ) x‖≤cubicBesselUpperConstant*Real.exp (-x/2) := by
  have hxp : 0<x := by linarith
  rw [schlafliBesselK_cubic_norm_re x hxp,schlafliBesselK_cubic_real x hxp,Complex.ofReal_re]
  have hp : (x/2)^(-(1:ℝ)/3)≤(1/2:ℝ)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)
  calc
    _ ≤ (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) :=
      mul_le_mul_of_nonneg_left (cubicBesselIntegral_upper x) (by positivity)
    _ ≤ (1/2:ℝ)*(1/2:ℝ)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = _ := by unfold cubicBesselUpperConstant;ring

lemma cubicBesselDensity_lower (x t : ℝ) (hx : 0<x) (ht : t∈Set.Icc x (2*x)) :
    (2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4)≤cubicBesselDensity x t := by
  have htp : 0<t := hx.trans_le ht.1
  have hp : (2*x)^(-(2:ℝ)/3)≤t^(-(2:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos htp ht.2 (by norm_num)
  have hfrac : x^2/(4*t)≤x/4 :=
    (div_le_iff₀ (show 0<4*t by positivity)).mpr (by nlinarith [ht.1])
  have he : Real.exp (-9*x/4)≤Real.exp (-t-x^2/(4*t)) :=
    Real.exp_le_exp.mpr (by linarith [ht.2])
  exact mul_le_mul hp he (Real.exp_pos _).le (Real.rpow_nonneg htp.le _)

lemma cubicBesselIntegral_lower (x : ℝ) (hx : 0<x) :
    x*((2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4))≤
      ∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
  have hsub : Set.Icc x (2*x)⊆Set.Ioi (0:ℝ) := fun t ht => hx.trans_le ht.1
  have hi := cubicBesselDensity_integrable x
  have hr := hi.mono_set hsub
  have hconstant : IntegrableOn (fun _ : ℝ => (2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4))
      (Set.Icc x (2*x)) := integrableOn_const (hs := isCompact_Icc.measure_ne_top)
  have hmono := setIntegral_mono_on hconstant hr measurableSet_Icc
    (fun t ht => cubicBesselDensity_lower x t hx ht)
  have hextend : (∫t in Set.Icc x (2*x),cubicBesselDensity x t)≤
      ∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselDensity_nonneg x t ht.le
    · exact Eventually.of_forall hsub
  rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith),smul_eq_mul,
    show 2*x-x=x by ring] at hmono
  exact hmono.trans hextend

def cubicBesselLowerConstant : ℝ :=
  (1/2:ℝ)*(1/2:ℝ)^(-(1:ℝ)/3)*(2:ℝ)^(-(2:ℝ)/3)

lemma cubicBesselLowerConstant_pos : 0<cubicBesselLowerConstant := by
  unfold cubicBesselLowerConstant
  positivity

theorem schlafliBesselK_cubic_lower (x : ℝ) (hx : 0<x) :
    cubicBesselLowerConstant*Real.exp (-9*x/4)≤(schlafliBesselK (1/3:ℂ) x).re := by
  rw [schlafliBesselK_cubic_real x hx,Complex.ofReal_re]
  have hp := mul_le_mul_of_nonneg_left (cubicBesselIntegral_lower x hx)
    (show 0≤(1/2:ℝ)*(x/2)^(-(1:ℝ)/3) by positivity)
  have hnorm : (x/2)^(-(1:ℝ)/3)=(1/2:ℝ)^(-(1:ℝ)/3)*x^(-(1:ℝ)/3) := by
    rw [show x/2=(1/2:ℝ)*x by ring,Real.mul_rpow (by norm_num) hx.le]
  have htwo : (2*x)^(-(2:ℝ)/3)=(2:ℝ)^(-(2:ℝ)/3)*x^(-(2:ℝ)/3) :=
    Real.mul_rpow (by norm_num) hx.le
  have hxp : x^(-(1:ℝ)/3)*x*x^(-(2:ℝ)/3)=1 := by
    calc
      _ = x^(-(1:ℝ)/3)*x^(1:ℝ)*x^(-(2:ℝ)/3) := by rw [Real.rpow_one]
      _ = x^((-(1:ℝ)/3+1)+(-(2:ℝ)/3)) := by rw [←Real.rpow_add hx,←Real.rpow_add hx]
      _ = 1 := by norm_num
  have he : (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(x*((2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4)))=
      cubicBesselLowerConstant*Real.exp (-9*x/4) := by
    rw [hnorm,htwo]
    calc
      _ = cubicBesselLowerConstant*(x^(-(1:ℝ)/3)*x*x^(-(2:ℝ)/3))*Real.exp (-9*x/4) := by
        unfold cubicBesselLowerConstant
        ring
      _ = _ := by rw [hxp,mul_one]
  rwa [he] at hp

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma exp_neg_mul_le_inverse_cube (ε r : ℝ) (hε : 0<ε) (hr : 0<r) :
    Real.exp (-ε*r)≤(6/ε^3)*r^(-3:ℝ) := by
  have hp := Real.pow_div_factorial_le_exp (ε*r) (le_of_lt (mul_pos hε hr)) 3
  norm_num only [Nat.factorial] at hp
  have hi := one_div_le_one_div_of_le (by positivity : (0:ℝ)<(ε*r)^3/6) hp
  rw [one_div,←Real.exp_neg] at hi
  rw [Real.rpow_neg hr.le]
  norm_num only [Real.rpow_ofNat]
  have halg : (6/ε^3)*(r^3)⁻¹=((ε*r)^3/6)⁻¹ := by
    field_simp
  rw [halg]
  simpa only [neg_mul,one_div] using hi

lemma summable_exp_neg_embedding_norm (ε : ℝ) (hε : 0<ε) :
    Summable (fun h : ActualEisensteinCubic.O => Real.exp (-ε*‖ConcreteTraceCRT.eisEmbedding h‖)) := by
  have hs := (summable_embedding_rpow (-3) (by norm_num)).mul_left (6/ε^3)
  have hz : Summable (fun h : ActualEisensteinCubic.O => if h=0 then (1:ℝ) else 0) :=
    (hasSum_ite_eq 0 (1:ℝ)).summable
  apply Summable.of_nonneg_of_le (fun h => (Real.exp_pos _).le) _ (hz.add hs)
  intro h
  by_cases hh : h=0
  · subst h
    norm_num [Pi.add_apply]
  · have hp : 0<‖ConcreteTraceCRT.eisEmbedding h‖ :=
      norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hh)
    simpa only [Pi.add_apply,ite_eq_right hh,zero_add] using exp_neg_mul_le_inverse_cube ε _ hε hp

lemma summable_exp_neg_cuspFrequency_norm (ε : ℝ) (hε : 0<ε) :
    Summable (fun h : ActualEisensteinCubic.O => Real.exp (-ε*‖cuspFrequency h‖)) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := by
    apply norm_pos_iff.mpr
    exact mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero
  have hs := summable_exp_neg_embedding_norm (ε/‖(3:ℂ)*ConcreteTraceCRT.eisLam‖) (div_pos hε hd)
  apply hs.congr
  intro h
  congr 1
  rw [cuspFrequency,norm_div]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cubicBesselNormalizer_ne_zero (h : ActualEisensteinCubic.O) (hh : h≠0) : cubicBesselNormalizer h≠0 := by
  unfold cubicBesselNormalizer
  apply mul_ne_zero
  · exact div_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  · apply Complex.cpow_ne_zero_iff.mpr
    left
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (cuspFrequency_ne_zero h hh)))

lemma cubicBesselHeight_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    IntegrableOn (fun v : ℝ => schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)
      (Set.Icc a b) volume := by
  have hsource : IntegrableOn (fun v : ℝ => (v:ℂ)^(-(4/3:ℂ)-1)*
      sourceFourierKernel (4/3) (cuspFrequency h*v)) (Set.Icc a b) volume := by
    apply ContinuousOn.integrableOn_Icc
    intro v hv
    have hpos := ha.trans_le hv.1
    exact ((Complex.continuousAt_ofReal_cpow_const v (-(4/3:ℂ)-1) (Or.inr hpos.ne')).mul
      ((sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp
        ((Complex.continuous_ofReal.const_mul (cuspFrequency h)).continuousAt))).continuousWithinAt
  apply (hsource.div_const (cubicBesselNormalizer h)).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  apply (div_eq_iff (cubicBesselNormalizer_ne_zero h hh)).mpr
  simpa only [mul_comm] using sourceFourierKernel_cubic_height h hh v (ha.trans_le hv.1)

lemma cubicBesselHeight_average_lower (a b : ℝ) (ha : 0<a) (hab : a<b) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ((b-a)*cubicBesselLowerConstant/b^2)*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
      ‖∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2‖ := by
  have hb : 0<b := ha.trans hab
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  let lower : ℝ := (cubicBesselLowerConstant/b^2)*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)
  have hi := cubicBesselHeight_integrable a b ha h hh
  have hpoint (v : ℝ) (hv : v∈Set.Icc a b) : lower≤
      RCLike.re (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
    have hvp := ha.trans_le hv.1
    have hx : 0<4*Real.pi*‖cuspFrequency h‖*v := by positivity
    have hK := schlafliBesselK_cubic_lower (4*Real.pi*‖cuspFrequency h‖*v) hx
    have he : Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
        Real.exp (-9*(4*Real.pi*‖cuspFrequency h‖*v)/4) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hv.2
        (show 0≤9*Real.pi*‖cuspFrequency h‖ by positivity)
      nlinarith [hmul]
    have hnum : cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖)≤
        (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)).re :=
      (mul_le_mul_of_nonneg_left he cubicBesselLowerConstant_pos.le).trans hK
    have hden : v^2≤b^2 := sq_le_sq₀ hvp.le hb.le |>.mpr hv.2
    change lower≤Complex.re (_/(v:ℂ)^2)
    rw [←Complex.ofReal_pow,Complex.div_ofReal_re]
    calc
      lower = (cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖))/b^2 := by dsimp [lower]; ring
      _ ≤ (cubicBesselLowerConstant*Real.exp (-9*Real.pi*b*‖cuspFrequency h‖))/v^2 :=
        div_le_div_of_nonneg_left (mul_nonneg cubicBesselLowerConstant_pos.le (Real.exp_pos _).le)
          (sq_pos_of_pos hvp) hden
      _ ≤ _ := div_le_div_of_nonneg_right hnum (sq_nonneg v)
  have hmono := setIntegral_mono_on
    (integrableOn_const (hs := isCompact_Icc.measure_ne_top) : IntegrableOn (fun _ : ℝ => lower) (Set.Icc a b))
    hi.re measurableSet_Icc hpoint
  rw [setIntegral_const,Real.volume_real_Icc_of_le hab.le,smul_eq_mul] at hmono
  have hreal : (∫v in Set.Icc a b,RCLike.re
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2))=
      Complex.re (∫v in Set.Icc a b,schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) :=
    integral_re hi
  rw [hreal] at hmono
  have hfinal := hmono.trans (Complex.re_le_norm _)
  convert hfinal using 1 ; dsimp [lower] ; ring

lemma cubicResidualFourierCoefficient_subexponential (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
      ‖cubicResidualFourierCoefficient h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let b : ℝ := ε/(9*Real.pi)
  let a : ℝ := b/2
  have hb : 0<b := div_pos hε (by positivity)
  have ha : 0<a := half_pos hb
  have hab : a<b := by dsimp [a]; linarith
  obtain ⟨C,hC,hbound⟩ := cubicResidualFourierCoefficient_interval_bound a b ha
  let D : ℝ := (b-a)*cubicBesselLowerConstant/b^2
  have hD : 0<D := div_pos (mul_pos (sub_pos.mpr hab) cubicBesselLowerConstant_pos) (sq_pos_of_pos hb)
  refine ⟨C/D,div_nonneg hC hD.le,?_⟩
  intro h hh
  have hlow := cubicBesselHeight_average_lower a b ha hab h hh
  have hscale : -9*Real.pi*b*‖cuspFrequency h‖=-(ε*‖cuspFrequency h‖) := by
    dsimp [b]
    field_simp
  rw [hscale] at hlow
  have hmul := (mul_le_mul_of_nonneg_left hlow (norm_nonneg (cubicResidualFourierCoefficient h))).trans
    (hbound h hh)
  have he : 0<Real.exp (-(ε*‖cuspFrequency h‖)) := Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD he)).mpr at hmul
  calc
    _ ≤ C/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hmul
    _ = (C/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg]; field_simp

end CubicEisenstein

end

end OAI
