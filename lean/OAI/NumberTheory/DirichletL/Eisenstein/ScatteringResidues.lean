import OAI.NumberTheory.DirichletL.Eisenstein.SourceProjection
import OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierSeries

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
open scoped BigOperators Classical Topology

section

lemma scalar_residue_sub_continuous (f g : ℂ→ℂ) (z r : ℂ)
    (hf : Tendsto (fun s => (s-z)*f s) (𝓝[≠] z) (𝓝 r)) (hg : ContinuousAt g z) :
    Tendsto (fun s => (s-z)*(f s-g s)) (𝓝[≠] z) (𝓝 r) := by
  have hlin : Tendsto (fun s : ℂ => s-z) (𝓝[≠] z) (𝓝 (0:ℂ)) := by
    simpa only [id_eq,sub_self] using (tendsto_id.sub_const z).mono_left
      (show 𝓝[≠] z≤𝓝 z from nhdsWithin_le_nhds)
  have hz : Tendsto (fun s => (s-z)*g s) (𝓝[≠] z) (𝓝 (0:ℂ)) := by
    simpa only [zero_mul] using hlin.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [mul_sub,sub_zero] using hf.sub hz

lemma weightedOutgoingConstant_residue_limit (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    Tendsto (fun s : ℂ => (s-4/3)*weightedOutgoingConstant a b ha ρ s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue)) := by
  apply scalar_residue_sub_continuous _ _ _ _ (kernelCuspHeightFourierFamily_residue_limit a b ha ρ 0)
  exact continuousAt_const.mul
    ((compactHeightMellin_differentiable a b ha ρ).continuous.continuousAt.comp
      (continuousAt_id.sub_const 3))

lemma baseOutgoingConstant_residue_limit :
    Tendsto (fun s : ℂ => (s-4/3)*baseOutgoingConstant s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 cuspConstantAverageResidue) := by
  have hf := kernelCuspAverageFamily_residue_limit 2 3 (by norm_num) (by norm_num)
  change Tendsto _ _ (𝓝 (kernelCuspStripAverage cubicEisensteinResidue)) at hf
  rw [cubicEisensteinResidue_cusp_average] at hf
  apply scalar_residue_sub_continuous _ _ _ _ hf
  exact continuousAt_const.mul
    (cuspMainHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt

theorem kernelCuspHeightFourier_zero_residue (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
        (∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(4/3:ℂ)-1)) := by
  have hbase : Tendsto cuspScatterHeightFactor (𝓝[≠] (4/3:ℂ))
      (𝓝 (cuspScatterHeightFactor (4/3:ℂ))) :=
    (cuspScatterHeightFactor_differentiableAt (4/3:ℂ) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hweight : Tendsto (fun s : ℂ => compactHeightMellin a b ρ (-s-1)) (𝓝[≠] (4/3:ℂ))
      (𝓝 (compactHeightMellin a b ρ (-(4/3:ℂ)-1))) :=
    ((compactHeightMellin_differentiable a b ha ρ).continuous.continuousAt.comp
      (continuousAt_id.neg.sub_const 1)).tendsto.mono_left nhdsWithin_le_nhds
  have hleft := ((weightedOutgoingConstant_residue_limit a b ha ρ).mul hbase).comp
    upperVertical_tendsto_cubic_punctured
  have hright := (baseOutgoingConstant_residue_limit.mul hweight).comp
    upperVertical_tendsto_cubic_punctured
  have hevent : (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*weightedOutgoingConstant a b ha ρ ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspScatterHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      (((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*baseOutgoingConstant ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        compactHeightMellin a b ρ (-((4/3:ℂ)+(t:ℂ)*Complex.I)-1)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have hs : (4/3:ℂ)+(t:ℂ)*Complex.I∈{s : ℂ | 1<s.re ∧ 0<s.im} := by
      constructor
      · norm_num
      · simpa using ht
    have he := weightedOutgoingConstant_cross_identity a b ha ρ hs
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue*cuspScatterHeightFactor (4/3:ℂ)=
      cuspConstantAverageResidue*compactHeightMellin a b ρ (-(4/3:ℂ)-1) :=
    tendsto_nhds_unique_of_eventuallyEq hleft hright hevent
  have hne : cuspScatterHeightFactor (4/3:ℂ)≠0 := by
    intro he
    have hpos := cuspScatterHeightFactor_center_re_pos
    rw [he,Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  apply mul_right_cancel₀ hne
  rw [heq,cuspConstantAverageResidue]
  change _=(((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
    compactHeightMellin a b ρ (-(4/3:ℂ)-1))*cuspScatterHeightFactor (4/3:ℂ)
  ring

lemma kernelCuspHeightFourier_zero_residue_seven_thirds (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    kernelCuspHeightFourier a b ha ρ 0 cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(3*(Real.pi:ℂ))*constantArithmeticResidue*
        (∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ))) := by
  convert kernelCuspHeightFourier_zero_residue a b ha ρ using 2
  congr 1
  norm_num

local notation "O" => ActualEisensteinCubic.O

def cubicResidualFullModeAmplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)
  else cubicResidualFourierCoefficient h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma cubicResidualFullModeAmplitude_zero (v : ℝ) :
    cubicResidualFullModeAmplitude v 0=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ) := by
  simp only [cubicResidualFullModeAmplitude,ite_true]

lemma cubicResidualFullModeAmplitude_nonzero (v : ℝ) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cubicResidualFullModeAmplitude v h=cubicResidualFourierCoefficient h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  rw [cubicResidualFullModeAmplitude,ite_eq_right hh]

lemma cubicResidualFullModeAmplitude_zero_density (v : ℝ) (hv : 0<v) :
    cubicResidualFullModeAmplitude v 0/(v:ℂ)^3=
      (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)) := by
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v:ℂ)^(-(7/3:ℂ))=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3 := by
    rw [show -(7/3:ℂ)=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hv0]
    congr 1
    exact Complex.cpow_natCast _ 3
  rw [cubicResidualFullModeAmplitude_zero,hp]
  ring

lemma cubicResidualFullModeAmplitude_nonzero_density (v : ℝ) (hv : 0<v)
    (h : ActualEisensteinCubic.O) (hh : h≠0) :
    cubicResidualFullModeAmplitude v h/(v:ℂ)^3=cubicResidualFourierCoefficient h*
      (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  rw [cubicResidualFullModeAmplitude_nonzero v h hh]
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

theorem kernelCuspHeightFourier_residue_full (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    kernelCuspHeightFourier a b ha ρ h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*
        (∫v in Set.Icc a b,ρ v*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  by_cases hh : h=0
  · subst h
    rw [kernelCuspHeightFourier_zero_residue_seven_thirds a b ha ρ]
    have he : (∫v in Set.Icc a b,ρ v*(cubicResidualFullModeAmplitude v 0/(v:ℂ)^3))=
        ((3*(Real.pi:ℂ))*constantArithmeticResidue)*
          (∫v in Set.Icc a b,ρ v*(v:ℂ)^(-(7/3:ℂ))) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [cubicResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)]
      ring
    rw [he]
    ring
  · rw [kernelCuspHeightFourier_residue_bessel a b ha ρ h hh]
    have he : (∫v in Set.Icc a b,ρ v*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3))=
        cubicResidualFourierCoefficient h*(∫v in Set.Icc a b,
          ρ v*(schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2)) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      dsimp only
      rw [cubicResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh]
      ring
    rw [he]
    ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cubicResidualFunction (w : HyperbolicSpace) : ℂ :=
  (3*Real.pi:ℂ)*constantArithmeticResidue*(hyperbolicHeight w:ℂ)^(2/3:ℂ)+
    cubicResidualNonzeroFunction w

lemma cubicResidualFunction_continuous : Continuous cubicResidualFunction := by
  have hp : Continuous (fun w : HyperbolicSpace => (hyperbolicHeight w:ℂ)^(2/3:ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (Complex.continuousAt_ofReal_cpow_const (hyperbolicHeight w) (2/3:ℂ)
      (Or.inr (hyperbolicHeight_pos w).ne')).comp (f := hyperbolicHeight) hyperbolicHeight_continuous.continuousAt
  exact (continuous_const.mul hp).add cubicResidualNonzeroFunction_continuous

lemma cubicResidualNonzeroSeries_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => cubicResidualNonzeroSeries (v,z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  exact (cubicResidualNonzeroSeries_continuousOn.continuousAt (hopen.mem_nhds hv)).comp
    (f := fun z : ℂ => (v,z)) (by fun_prop)

lemma periodDomain_integrable_of_continuous (f : ℂ→ℂ) (hf : Continuous f) :
    IntegrableOn f periodDomain volume := by
  apply (hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

lemma cubicResidualFunction_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicResidualFunction (upperPoint z v hv)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if k=0 then
        (3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ) else cubicResidualModeAmplitude v k) := by
  have hphase : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency k*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  have hc0 := periodDomain_integrable_of_continuous
    (fun z => ((3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ))*
      ShortDraftTrace.breveE (-cuspFrequency k*z)) (continuous_const.mul hphase)
  have hcn := periodDomain_integrable_of_continuous
    (fun z => cubicResidualNonzeroSeries (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))
    ((cubicResidualNonzeroSeries_height_continuous v hv).mul hphase)
  simp_rw [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,add_mul]
  rw [integral_add hc0 hcn,integral_const_mul,integral_cusp_character,cubicResidualNonzeroSeries_fourier v hv k]
  by_cases hk : k=0
  · simp only [ite_eq_left hk,cubicResidualModeAmplitude,mul_zero]
    ring
  · simp only [ite_eq_right hk,mul_zero,zero_add]

lemma cubicResidualFunction_heightFourier (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) :
    (∫w in cuspPeriodStrip a b,cubicResidualFunction w*cuspWeightedFourierPhase ρ h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(∫v in Set.Icc a b,ρ v*
        ((if h=0 then (3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ)
          else cubicResidualModeAmplitude v h)/(v:ℂ)^3)) := by
  let g : HyperbolicSpace→ℂ := fun w => cubicResidualFunction w*cuspWeightedFourierPhase ρ h w
  have hg : Continuous g := cubicResidualFunction_continuous.mul (cuspWeightedFourierPhase_continuous ρ h)
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable_of_pos a b ha g hg),←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos := ha.trans_le hv.1
  have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
      ρ v*(((9*Real.sqrt 3/2:ℝ):ℂ)*(if h=0 then
        (3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ) else cubicResidualModeAmplitude v h)) := by
    simp_rw [g,cuspCoordinateLift_positive v _ hpos,cuspWeightedFourierPhase,
      hyperbolicHeight_upperPoint,cuspFourierPhase,hyperbolicHorizontal_upperPoint]
    calc
      _ = ρ v*(∫z in periodDomain,cubicResidualFunction (upperPoint z v hpos)*
          ShortDraftTrace.breveE (-cuspFrequency h*z)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by ring)
      _ = _ := by rw [cubicResidualFunction_fourier v hpos h]
  dsimp only
  rw [hinner]
  ring

lemma cubicResidualFunction_period (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    cubicResidualFunction (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      cubicResidualFunction (upperPoint z v hv) := by
  simp only [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,cubicResidualNonzeroSeries_period]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

lemma kernelCuspHeightPullback_memLp (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    MemLp (fun w => F (integralOrbitProjection globalKubotaKernel w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) :=
  MemLp.ae_eq (kernelCuspHeightPullback_ae a b ha F)
    (MeasureTheory.Lp.memLp (kernelCuspHeightPullback a b ha F))

lemma kernelCuspCoordinates_memLp (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    MemLp (fun q : ℝ × ℂ => F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift q))) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict periodDomain)) := by
  have hm := euclideanToHyperbolic_measurePreserving_on (positiveEuclideanStrip a b)
    (positiveEuclideanStrip_measurable a b) (positiveEuclideanStrip_positive a b ha)
  rw [positiveEuclideanStrip_preimage] at hm
  have hF := (kernelCuspHeightPullback_memLp a b ha F).comp_measurePreserving hm
  have hvol := euclideanVolume_le_heightCube_hyperbolic (positiveEuclideanStrip a b)
    (positiveEuclideanStrip_measurable a b) (positiveEuclideanStrip_positive a b ha)
    (max 1 b) (by positivity) (fun p hp => hp.1.2.trans (le_max_right 1 b))
  have hFE := (hF.smul_measure (c := ENNReal.ofReal ((max 1 b)^3)) ENNReal.ofReal_ne_top).mono_measure hvol
  have hsplit := spatialComplexSplit_preserves_volume.restrict_preimage (s := Set.Icc a b ×ˢ periodDomain)
    (measurableSet_Icc.prod periodDomain_measurable)
  have hback := hsplit.symm
  have hpull := hFE.comp_measurePreserving hback
  simpa only [Measure.prod_restrict, Measure.volume_eq_prod, Function.comp_def,
    positiveEuclideanStrip, cuspCoordinateLift] using hpull

section ProductSections
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {«μ» : Measure α} {ν : Measure β} [SFinite «μ»] [SFinite ν]

lemma complex_memLp_two_sections {f : α × β → ℂ} (hf : MemLp f 2 («μ».prod ν)) :
    ∀ᵐx ∂«μ», MemLp (fun y => f (x,y)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    hf.norm.integrable_sq.prod_right_ae] with x hx hi
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hi

end ProductSections

lemma kernelCuspSections_memLp (a b : ℝ) (ha : 0<a) (F : KernelQuotientL2) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b),
      MemLp (fun z : ℂ => F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))) 2
        (volume.restrict periodDomain) :=
  complex_memLp_two_sections (kernelCuspCoordinates_memLp a b ha F)

lemma cuspCoordinateLift_measurable : Measurable cuspCoordinateLift :=
  euclideanToHyperbolic_measurable.comp spatialComplexSplit.symm.measurable

lemma kernelCuspFourierCoordinate_integrable (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    IntegrableOn (fun q : ℝ × ℂ =>
      (F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift q))*
        cuspWeightedFourierPhase ρ h (cuspCoordinateLift q))/(q.1:ℂ)^3)
      (Set.Icc a b ×ˢ periodDomain) volume := by
  let := periodDomain_finiteMeasure
  have hF := (kernelCuspCoordinates_memLp a b ha F).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hm : Measurable (fun q : ℝ × ℂ =>
      cuspWeightedFourierPhase ρ h (cuspCoordinateLift q)/(q.1:ℂ)^3) :=
    ((cuspWeightedFourierPhase_continuous ρ h).measurable.comp cuspCoordinateLift_measurable).div
      (by fun_prop)
  have hb : ∀ᵐq ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict periodDomain)),
      ‖cuspWeightedFourierPhase ρ h (cuspCoordinateLift q)/(q.1:ℂ)^3‖≤‖ρ‖/a^3 := by
    rw [Measure.prod_restrict, ←Measure.volume_eq_prod]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod periodDomain_measurable)] with q hq
    have hpos : 0<q.1 := ha.trans_le hq.1.1
    rw [norm_div,norm_pow,Complex.norm_of_nonneg hpos.le]
    calc
      _ ≤ ‖ρ‖/q.1^3 := div_le_div_of_nonneg_right
        (cuspWeightedFourierPhase_bound ρ h (cuspCoordinateLift q)) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (pow_le_pow_left₀ ha.le hq.1.1 3)
  have hi := hF.mul_bdd hm.aestronglyMeasurable hb
  simpa only [IntegrableOn, Measure.prod_restrict, ←Measure.volume_eq_prod, mul_div_assoc] using hi

def kernelCuspSliceCoefficient (F : KernelQuotientL2) (h : ActualEisensteinCubic.O) (v : ℝ) : ℂ :=
  (∫z in periodDomain, F (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
    ShortDraftTrace.breveE (-cuspFrequency h*z))/(v:ℂ)^3

lemma kernelCuspHeightFourier_eq_slice_integral (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    kernelCuspHeightFourier a b ha ρ h F =
      ∫v in Set.Icc a b, ρ v*kernelCuspSliceCoefficient F h v := by
  rw [kernelCuspHeightFourier_integral]
  have hg : StronglyMeasurable (fun w =>
      F (integralOrbitProjection globalKubotaKernel w)*cuspWeightedFourierPhase ρ h w) :=
    ((MeasureTheory.Lp.stronglyMeasurable F).comp_measurable (measurable_integralOrbitProjection _)).mul
      (cuspWeightedFourierPhase_continuous ρ h).stronglyMeasurable
  rw [cuspPeriodStrip_integral_coordinates_of_pos a b ha _ hg.aestronglyMeasurable
    (kernelCuspFourierCoordinate_integrable a b ha ρ h F)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hpos : 0<v := ha.trans_le hv.1
  simp only [kernelCuspSliceCoefficient]
  rw [←mul_div_assoc]
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [cuspWeightedFourierPhase,cuspFourierPhase,cuspCoordinateLift_positive v z hpos,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    ring)

lemma kernelCuspSliceCoefficient_integrable (a b : ℝ) (ha : 0<a)
    (h : ActualEisensteinCubic.O) (F : KernelQuotientL2) :
    IntegrableOn (kernelCuspSliceCoefficient F h) (Set.Icc a b) volume := by
  have hi := kernelCuspFourierCoordinate_integrable a b ha 1 h F
  rw [IntegrableOn, Measure.volume_eq_prod, ←Measure.prod_restrict] at hi
  apply hi.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hpos : 0<v := ha.trans_le hv.1
  rw [integral_div, kernelCuspSliceCoefficient]
  apply congrArg (fun c : ℂ => c/(v:ℂ)^3)
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [kernelCuspSliceCoefficient]
    rw [cuspWeightedFourierPhase,cuspFourierPhase,cuspCoordinateLift_positive v z hpos,
      hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    simp)

end

section

open scoped BigOperators Classical
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma third_character_eq_one_iff_basis (ψ:AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ) :
    ψ=1 ↔ ψ (Ideal.Quotient.mk _ (1:Eis))=1 ∧
      ψ (Ideal.Quotient.mk _ omega)=1 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h1,hw⟩
    ext x
    obtain ⟨z,rfl⟩:=Ideal.Quotient.mk_surjective x
    rw [←ActualEisensteinCoordinates.eval_coords z]
    change ψ (Ideal.Quotient.mk _
      (((ActualEisensteinCoordinates.coords z).1:Eis)+
       ((ActualEisensteinCoordinates.coords z).2:Eis)*omega))=1
    rw [map_add,AddChar.map_add_eq_mul]
    have hA:Ideal.Quotient.mk (Ideal.span {(3:Eis)})
        ((ActualEisensteinCoordinates.coords z).1:Eis)=
        (ActualEisensteinCoordinates.coords z).1 • Ideal.Quotient.mk _ (1:Eis):=by
      rw [←map_zsmul]
      simp
    have hB:Ideal.Quotient.mk (Ideal.span {(3:Eis)})
        (((ActualEisensteinCoordinates.coords z).2:Eis)*omega)=
        (ActualEisensteinCoordinates.coords z).2 • Ideal.Quotient.mk _ omega:=by
      rw [←map_zsmul]
      simp only [zsmul_eq_mul]
    rw [hA,hB,AddChar.map_zsmul_eq_zpow,AddChar.map_zsmul_eq_zpow,h1,hw]
    simp

lemma omega3_pow_exp_eq_one_iff (t:ℕ) (b:ℤ) :
    omega3^t*Complex.exp (2*Real.pi*Complex.I*(b:ℂ)/3)=1 ↔
      (3:ℤ)∣(t:ℤ)+b := by
  have hω:omega3=Complex.exp (2*Real.pi*Complex.I/3):=by
    rw [←TraceLambdaPhase.exp_minus_four_pi_div_three]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-1,?_⟩
    push_cast
    ring
  rw [hω,←Complex.exp_nat_mul,←Complex.exp_add]
  have he:(t:ℂ)*(2*Real.pi*Complex.I/3)+2*Real.pi*Complex.I*(b:ℂ)/3=
      2*Real.pi*Complex.I*(((t:ℤ)+b:ℤ):ℂ)/3:=by push_cast;ring
  rw [he]
  constructor
  · intro hh
    have hh':Complex.exp (2*Real.pi*Complex.I*((((t:ℤ)+b:ℤ):ℂ)/3))=1:=by
      convert hh using 1 ;ring_nf
    obtain ⟨v,hv⟩:=GeneralPrimitiveTrace.complex_exp_trace_integer hh'
    have hc:(((t:ℤ)+b:ℤ):ℂ)=3*(v:ℂ):=by linear_combination 3*hv
    have hi:(t:ℤ)+b=3*v:=by exact_mod_cast hc
    exact ⟨v,hi⟩
  · rintro ⟨v,hv⟩
    rw [hv]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨v,?_⟩
    push_cast
    ring

lemma eisEmbedding_omega_actual : eisEmbedding omega=omega3 := by
  have hω:omega=ActualEisensteinCoordinates.eval 0 1:=by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [hω,eisEmbedding_eval]
  norm_num

lemma trace_third_coordinate (k:Eis) :
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
      3 (by norm_num) (Ideal.Quotient.mk _ k)=
      Complex.exp (2*Real.pi*Complex.I*((ActualEisensteinCoordinates.coords k).2:ℂ)/3) := by
  rw [eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  have hh:=breveE_real_trace_of_O 3 k
  norm_num at hh
  convert hh using 1 ;simp only [map_ofNat] ;congr 1 ;ring

end

open scoped BigOperators Classical
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_symbol_primaryCoord (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) (A B:ℤ) :
    symbol (u.val*lambda^n) (primaryCoord A B)=
      (cubicExp (2*A-B))^j*(cubicExp A)^n := by
  have hp:=primaryCoord_primary A B
  rw [symbol_mul_numerator _ _ _ hp,symbol_pow_numerator _ _ hp,
    symbol_lambda_eq_linearRay _ hp,linearRay_primaryCoord]
  norm_num only [one_mul,zero_mul,add_zero]
  congr 1
  rcases hu with hu|hu
  · rw [hu,symbol_pow_numerator _ _ hp,symbol_omega_eq_linearRay _ hp,
      linearRay_primaryCoord]
    ring_nf
  · rw [hu,symbol_neg_numerator _ _ hp,symbol_pow_numerator _ _ hp,
      symbol_omega_eq_linearRay _ hp,linearRay_primaryCoord]
    ring_nf

lemma ramified_symbol_at_one (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    symbol (u.val*lambda^n) (1+3*(1:Eis))=omega^(2*j+n) := by
  have he:(1+3*(1:Eis))=primaryCoord 1 0:=by rw [primaryCoord_eq];norm_num
  rw [he,ramified_symbol_primaryCoord u n j hu]
  norm_num [cubicExp]
  rw [←pow_mul,←pow_add]

lemma ramified_symbol_at_omega (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    symbol (u.val*lambda^n) (1+3*omega)=omega^(2*j) := by
  have he:(1+3*omega)=primaryCoord 0 1:=by rw [primaryCoord_eq];norm_num
  rw [he,ramified_symbol_primaryCoord u n j hu]
  norm_num [cubicExp]
  rw [←pow_mul]

lemma ramifiedFrequencyChar_mk (k:Eis) (u:Eisˣ) (n:ℕ) (x:Eis) :
    ramifiedFrequencyChar k u n (Ideal.Quotient.mk _ x)=
      eisEmbedding (symbol (u.val*lambda^n) (1+3*x))*
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        3 (by norm_num) (Ideal.Quotient.mk _ (k*x)) := by
  rw [ramifiedFrequencyChar,AddChar.mul_apply,ramifiedQuotientChar,
    IdealGaussCRT.quotientAddChar_mk,AddChar.mulShift_apply,←map_mul]
  rfl

lemma coords_mul_omega_second (k:Eis) :
    (ActualEisensteinCoordinates.coords (k*omega)).2=
      (ActualEisensteinCoordinates.coords k).1-(ActualEisensteinCoordinates.coords k).2 := by
  conv_lhs => rw [←ActualEisensteinCoordinates.eval_coords k]
  have hw:omega=ActualEisensteinCoordinates.eval 0 1:=by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
  ring

def ramifiedCongruence (k:Eis) (j n:ℕ):Prop:=
  (3:ℤ)∣(2*(j:ℤ)+(n:ℤ)+(ActualEisensteinCoordinates.coords k).2) ∧
  (3:ℤ)∣(2*(j:ℤ)+(ActualEisensteinCoordinates.coords k).1-
    (ActualEisensteinCoordinates.coords k).2)

lemma ramifiedFrequencyChar_eq_one_iff (k:Eis) (u:Eisˣ) (n j:ℕ)
    (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j)) :
    ramifiedFrequencyChar k u n=1 ↔ ramifiedCongruence k j n := by
  rw [third_character_eq_one_iff_basis,ramifiedFrequencyChar_mk,
    ramifiedFrequencyChar_mk,ramified_symbol_at_one u n j hu,
    ramified_symbol_at_omega u n j hu,map_pow,map_pow,eisEmbedding_omega_actual,
    mul_one,trace_third_coordinate,trace_third_coordinate,coords_mul_omega_second,
    omega3_pow_exp_eq_one_iff,omega3_pow_exp_eq_one_iff]
  unfold ramifiedCongruence
  push_cast
  simp only [add_sub_assoc]

theorem ramified_arithmetic_explicit_table (h k:Eis) (u:Eisˣ) (n j:ℕ)
    (hn:2≤n) (hu:(u:Eis)=omega^j ∨ (u:Eis)=-(omega^j))
    (hk:3*h=(u.val*lambda^n)*k) :
    arithmeticResidueSum h (u.val*lambda^n)=
      if ramifiedCongruence k j n then ((3^n:ℕ):ℂ)*residueAdditive k 3 1 else 0 := by
  rw [ramified_arithmetic_character_test h k u n hn hk]
  simp only [ramifiedFrequencyChar_eq_one_iff k u n j hu]

def ramifiedUnitIndex (u:Eisˣ):Fin 3:=Classical.choose (unit_eq_sign_omega u)

lemma ramifiedUnitIndex_spec (u:Eisˣ) :
    (u:Eis)=omega^(ramifiedUnitIndex u).val ∨
      (u:Eis)=-(omega^(ramifiedUnitIndex u).val):=
  Classical.choose_spec (unit_eq_sign_omega u)

def explicitRamifiedCoefficient (h:Eis) (u:Eisˣ) (n:ℕ):ℂ:=
  if hd:u.val*lambda^n∣3*h then
    let k:=Classical.choose hd
    if ramifiedCongruence k (ramifiedUnitIndex u).val n then
      ((3^n:ℕ):ℂ)*residueAdditive k 3 1 else 0
  else 0

theorem arithmeticResidueSum_eq_explicitRamifiedCoefficient (h:Eis) (u:Eisˣ)
    (n:ℕ) (hn:2≤n) :
    arithmeticResidueSum h (u.val*lambda^n)=explicitRamifiedCoefficient h u n := by
  unfold explicitRamifiedCoefficient
  split_ifs with hd
  · exact ramified_arithmetic_explicit_table h (Classical.choose hd) u n
      (ramifiedUnitIndex u).val hn (ramifiedUnitIndex_spec u) (Classical.choose_spec hd)
  · by_contra hne
    exact hd (ramified_arithmetic_support h u n hn hne)

theorem scatteringCoefficient_explicit_ramified (s:ℂ) (hs:2<s.re)
    (h:Eis) (hh:h≠0) :
    scatteringCoefficient s h=
      (∑'u:Eisˣ,∑n∈Finset.range (ramifiedFrequencyBound h+1),
        ((3^(n+2):ℕ):ℂ)^(-s)*explicitRamifiedCoefficient h u (n+2)*
          unramifiedCubicGaussSeries s (h*(9*(u.val*lambda^(n+2)))))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [scatteringCoefficient_unramified_gauss s hs h hh]
  congr 1
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro n hn
  rw [arithmeticResidueSum_eq_explicitRamifiedCoefficient h u (n+2) (by omega)]

end CubicEisenstein

end

end OAI
