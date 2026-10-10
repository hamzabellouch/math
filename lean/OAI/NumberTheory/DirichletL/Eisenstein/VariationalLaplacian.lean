import OAI.NumberTheory.DirichletL.CubicSieve.PaddedPassage

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

def kernelLiftedCutoff (χ : PositiveChartCutoff) (w : HyperbolicSpace) : ℝ :=
  χ.func (hyperbolicEuclideanCoordinates w)

lemma kernelLiftedCutoff_continuous (χ : PositiveChartCutoff) : Continuous (kernelLiftedCutoff χ) :=
  χ.smooth.continuous.comp hyperbolicEuclideanCoordinates_continuous

lemma kernelLiftedCutoff_compact (χ : PositiveChartCutoff) : HasCompactSupport (kernelLiftedCutoff χ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (χ.compact.image_of_continuousOn (fun p hp =>
      (euclideanToHyperbolic_contMDiffAt p (χ.positive hp)).continuousAt.continuousWithinAt))
  intro w hw
  refine ⟨hyperbolicEuclideanCoordinates w,?_,euclideanToHyperbolic_coordinates w⟩
  exact subset_tsupport χ.func hw

lemma kernelLiftedCutoff_bounded (χ : PositiveChartCutoff) :
    ∃C : ℝ,∀w,‖kernelLiftedCutoff χ w‖≤C := by
  obtain ⟨w,hw⟩ := (kernelLiftedCutoff_continuous χ).norm.exists_forall_ge_of_hasCompactSupport
    (kernelLiftedCutoff_compact χ).norm
  exact ⟨_,hw⟩

lemma kernelCutoffGradient_memLp (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    MemLp (fun w => kernelLiftedCutoff χ w • g w) 2 KernelFundamentalVolume := by
  obtain ⟨C,hC⟩ := kernelLiftedCutoff_bounded χ
  have hm : AEStronglyMeasurable (fun w => kernelLiftedCutoff χ w • g w) KernelFundamentalVolume :=
    (kernelLiftedCutoff_continuous χ).aestronglyMeasurable.smul (Lp.aestronglyMeasurable g)
  refine (Lp.memLp g).of_le_mul (c := C) hm (Eventually.of_forall (fun w => ?_))
  change ‖kernelLiftedCutoff χ w • g w‖≤C*‖g w‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC w) (norm_nonneg (g w))

def kernelCutoffGradient (χ : PositiveChartCutoff) (g : KernelGradientL2) : KernelGradientL2 :=
  (kernelCutoffGradient_memLp χ g).toLp (fun w => kernelLiftedCutoff χ w • g w)

lemma kernelCutoffGradient_coe (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    (kernelCutoffGradient χ g : HyperbolicSpace→EuclideanSpace ℂ (Fin 3))=ᵐ[KernelFundamentalVolume]
      fun w => kernelLiftedCutoff χ w • g w := (kernelCutoffGradient_memLp χ g).coeFn_toLp

def kernelCutoffGradientLinear (χ : PositiveChartCutoff) : KernelGradientL2 →ₗ[ℂ] KernelGradientL2 where
  toFun := kernelCutoffGradient χ
  map_add' g h := by
    apply Lp.ext
    filter_upwards [kernelCutoffGradient_coe χ (g+h),kernelCutoffGradient_coe χ g,
      kernelCutoffGradient_coe χ h,Lp.coeFn_add g h,
      Lp.coeFn_add (kernelCutoffGradient χ g) (kernelCutoffGradient χ h)] with w hgh hg hh ha ha'
    simp only [hgh,ha',ha,Pi.add_apply,hg,hh,smul_add]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [kernelCutoffGradient_coe χ (c•g),kernelCutoffGradient_coe χ g,
      Lp.coeFn_smul c g,Lp.coeFn_smul c (kernelCutoffGradient χ g)] with w hcg hg ha ha'
    simp only [RingHom.id_apply,hcg,ha',ha,Pi.smul_apply,hg]
    exact smul_comm _ _ _

lemma kernelCutoffGradient_bound (χ : PositiveChartCutoff) :
    ∃C : ℝ,∀g : KernelGradientL2,‖kernelCutoffGradientLinear χ g‖≤C*‖g‖ := by
  obtain ⟨C,hC⟩ := kernelLiftedCutoff_bounded χ
  refine ⟨C,fun g => ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [kernelCutoffGradient_coe χ g] with w hw
  change ‖kernelCutoffGradient χ g w‖≤_
  rw [hw,norm_smul]
  exact mul_le_mul_of_nonneg_right (hC w) (norm_nonneg _)

def kernelCutoffGradientCLM (χ : PositiveChartCutoff) : KernelGradientL2 →L[ℂ] KernelGradientL2 :=
  (kernelCutoffGradientLinear χ).mkContinuousOfExistsBound (kernelCutoffGradient_bound χ)

lemma kernelCutoffGradient_norm_sq (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    ‖kernelCutoffGradientCLM χ g‖^2=
      ∫w,(kernelLiftedCutoff χ w)^2*‖g w‖^2∂KernelFundamentalVolume := by
  calc
    ‖kernelCutoffGradientCLM χ g‖^2=inner ℝ (kernelCutoffGradientCLM χ g) (kernelCutoffGradientCLM χ g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫w,inner ℝ (kernelCutoffGradient χ g w) (kernelCutoffGradient χ g w)∂KernelFundamentalVolume := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [kernelCutoffGradient_coe χ g] with w hw
      rw [hw,real_inner_self_eq_norm_sq,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

lemma kernelCutoffGradient_core_norm_sq (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2=
      ∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂KernelFundamentalVolume := by
  rw [kernelCutoffGradient_norm_sq]
  apply integral_congr_ae
  filter_upwards [kernelGradientToL2_coe f] with w hw
  rw [hw,kernelGradientAt_norm_sq]

lemma kernelLocalizedField_reverse_energy (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)≤
      2*(p 2)^2*kernelLocalizedDensity χ f p+
      2*(p 2)^2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
  have hsum : (χ.func p)^2*(∑j : Fin 3,‖fderiv ℝ (kernelTestField f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤
      2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)+
      2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
    simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have he := kernelLocalizedField_fderiv χ f p hp (EuclideanSpace.basisFun (Fin 3) ℝ j)
    have he' : χ.func p • fderiv ℝ (kernelTestField f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)=
        fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)-
        fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p := by rw [he]; abel
    have hb := complex_norm_add_sq_le
      (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
      (- (fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p))
    rw [←sub_eq_add_neg,←he'] at hb
    simpa only [norm_smul,norm_neg,mul_pow,Real.norm_eq_abs,sq_abs,mul_assoc] using hb
  have hc := hyperbolicEuclideanCoordinates_toHyperbolic p hp
  have hv : hyperbolicHeight (euclideanToHyperbolic p)=p 2 := congrArg (fun q : EuclideanSpatial => q 2) hc
  rw [kernelTestEnergyDensity_eq_partials,hv]
  simp only [kernelTestPartial,hc]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (p 2))
  unfold kernelLocalizedDensity
  nlinarith [mul_nonneg (sq_nonneg (p 2)) (sq_nonneg ‖kernelLocalizedField χ f p‖)]

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal

lemma kernelLocalizedDensity_nonneg (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : 0≤kernelLocalizedDensity χ f p := by
  unfold kernelLocalizedDensity
  positivity

lemma hyperbolicVolume_le_densityBound (S : Set EuclideanSpatial) (hS : MeasurableSet S)
    (hpos : S⊆euclideanUpperHalf) (H : ℝ)
    (hH : ∀p∈S,((p 2)^3)⁻¹≤H) :
    hyperbolicEuclideanVolume.restrict S≤ENNReal.ofReal H • volume.restrict S := by
  rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
    Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos]
  have hh : hyperbolicDensity≤ᵐ[volume.restrict S] (fun _ => ENNReal.ofReal H) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    exact ENNReal.ofReal_le_ofReal (hH p hp)
  simpa only [MeasureTheory.withDensity_const] using MeasureTheory.withDensity_mono hh

instance hyperbolicVolume_finiteOnCompacts : IsFiniteMeasureOnCompacts hyperbolicVolume where
  lt_top_of_isCompact K hK := by
    let S := hyperbolicEuclideanCoordinates '' K
    have hSK : IsCompact S := hK.image hyperbolicEuclideanCoordinates_continuous
    have hS : MeasurableSet S := hSK.measurableSet
    have hpos : S⊆euclideanUpperHalf := by
      rintro p ⟨w,hw,rfl⟩
      exact hyperbolicHeight_pos w
    have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) S :=
      (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
        (fun p hp => pow_ne_zero _ (ne_of_gt (hpos hp)))
    obtain ⟨H,hH⟩ := hSK.bddAbove_image hrho
    have hb := hyperbolicVolume_le_densityBound S hS hpos H (fun p hp => hH ⟨p,hp,rfl⟩)
    have hm : hyperbolicEuclideanVolume S< (∞ : ℝ≥0∞) := by
      have hbu := Measure.le_iff.mp hb Set.univ MeasurableSet.univ
      simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Measure.smul_apply,
        smul_eq_mul] at hbu
      exact hbu.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSK.measure_lt_top)
    have heq : euclideanToHyperbolic ⁻¹' K=ᵐ[hyperbolicEuclideanVolume]S := by
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      apply propext
      constructor
      · intro h
        exact ⟨euclideanToHyperbolic p,h,hyperbolicEuclideanCoordinates_toHyperbolic p hp⟩
      · rintro ⟨w,hw,rfl⟩
        simpa only [Set.mem_preimage,euclideanToHyperbolic_coordinates] using hw
    rw [hyperbolicVolume,Measure.map_apply euclideanToHyperbolic_measurable hK.measurableSet,
      measure_congr heq]
    exact hm

private lemma integrable_sq_mul_of_compact (a b : HyperbolicSpace → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : HasCompactSupport a) :
    Integrable (fun w => (a w)^2*b w) hyperbolicVolume := by
  have hs : HasCompactSupport (fun w => (a w)^2) :=
    hc.comp_left (g := fun x : ℝ => x^2) (by simp)
  exact ((ha.pow 2).mul hb).integrable_of_hasCompactSupport hs.mul_right

lemma kernelLiftedCutoffEnergy_integrable (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    Integrable (fun w => (kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w) hyperbolicVolume :=
  integrable_sq_mul_of_compact (kernelLiftedCutoff χ) (kernelTestEnergyDensity f)
    (kernelLiftedCutoff_continuous χ) (kernelTestEnergyDensity_continuous f)
    (kernelLiftedCutoff_compact χ)

lemma kernelLiftedCutoffEnergy_integral (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    (∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂hyperbolicVolume)=
      ∫p,(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
  rw [hyperbolicVolume,integral_map euclideanToHyperbolic_measurable.aemeasurable
    (kernelLiftedCutoffEnergy_integrable χ f).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
  simp only [kernelLiftedCutoff,hyperbolicEuclideanCoordinates_toHyperbolic p hp]

lemma kernelCutoffGradient_core_estimate (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (B D H : ℝ) (_hB : 0≤B) (hD : 0≤D) (hH : 0≤H)
    (hheight : ∀p∈tsupport χ.func,p 2≤B)
    (hderiv : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H)
    (f : kernelSmoothTests) :
    ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2≤
      2*B^2*(H*‖kernelLocalizedH1 χ f‖^2+D*‖kernelSmoothTestsToL2 f‖^2) := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hpos : S⊆euclideanUpperHalf := χ.positive
  have hmeasure := hyperbolicVolume_le_densityBound S hS hpos H hdensity
  have hloc : IntegrableOn (kernelLocalizedDensity χ f) S hyperbolicEuclideanVolume :=
    (((kernelLocalizedDensity_integrable χ f).integrableOn).smul_measure
      (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top).mono_measure hmeasure
  have hmass : IntegrableOn (fun p => ‖kernelTestField f p‖^2) S hyperbolicEuclideanVolume := by
    exact (kernelEuclideanProjection_measurePreserving_on S hS hpos hinj).integrable_comp_of_integrable
      ((kernelSmoothTests_memLp f).norm.integrable_sq.integrableOn)
  have hweight : IntegrableOn (fun p => (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p))
      S hyperbolicEuclideanVolume := by
    have hh := (kernelLiftedCutoffEnergy_integrable χ f).comp_measurable euclideanToHyperbolic_measurable
    have heq : (fun p => (kernelLiftedCutoff χ (euclideanToHyperbolic p))^2*
        kernelTestEnergyDensity f (euclideanToHyperbolic p))=ᵐ[hyperbolicEuclideanVolume]
        fun p => (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p) := by
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      simp only [kernelLiftedCutoff,hyperbolicEuclideanCoordinates_toHyperbolic p hp]
    exact (hh.congr heq).integrableOn
  have hlocBound : (∫p in S,kernelLocalizedDensity χ f p∂hyperbolicEuclideanVolume)≤
      H*‖kernelLocalizedH1 χ f‖^2 := by
    have hh := integral_mono_measure hmeasure
      (Eventually.of_forall (kernelLocalizedDensity_nonneg χ f))
      (((kernelLocalizedDensity_integrable χ f).integrableOn).smul_measure
        (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top)
    rw [integral_smul_measure,ENNReal.toReal_ofReal hH] at hh
    rw [kernelLocalizedH1_norm_sq]
    exact hh.trans (mul_le_mul_of_nonneg_left
      (setIntegral_le_integral (kernelLocalizedDensity_integrable χ f)
        (Eventually.of_forall (kernelLocalizedDensity_nonneg χ f))) hH)
  rw [kernelCutoffGradient_core_norm_sq]
  calc
    _ ≤ ∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂hyperbolicVolume :=
      setIntegral_le_integral (kernelLiftedCutoffEnergy_integrable χ f)
        (Eventually.of_forall (fun w => mul_nonneg (sq_nonneg _) (kernelTestEnergyDensity_nonneg f w)))
    _ = ∫p in S,(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
      rw [kernelLiftedCutoffEnergy_integral]
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro p hp
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).self_of_nhds
      simp only [hz,Pi.zero_apply,zero_pow (by decide : 2≠0),zero_mul]
    _ ≤ ∫p in S,(2*B^2*kernelLocalizedDensity χ f p+2*B^2*D*‖kernelTestField f p‖^2)
        ∂hyperbolicEuclideanVolume := by
      apply setIntegral_mono_on hweight ((hloc.const_mul _).add (hmass.const_mul _)) hS
      intro p hp
      refine (kernelLocalizedField_reverse_energy χ f p (hpos hp)).trans ?_
      simp only [Pi.add_apply]
      gcongr
      · exact kernelLocalizedDensity_nonneg _ _ _
      · exact (hpos hp).le
      · exact hheight p hp
      · exact (hpos hp).le
      · exact hheight p hp
      · exact hderiv p hp
    _ = 2*B^2*((∫p in S,kernelLocalizedDensity χ f p∂hyperbolicEuclideanVolume)+
        D*(∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)) := by
      rw [integral_add (hloc.const_mul _) (hmass.const_mul _),integral_const_mul,integral_const_mul]
      ring
    _ ≤ _ := by
      gcongr
      exact kernelLocalMass_le S hS hpos hinj f

lemma kernelCutoffGradient_core_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2≤
        C*(‖kernelLocalizedH1 χ f‖^2+‖kernelSmoothTestsToL2 f‖^2) := by
  have hgrad : Continuous (fun p : EuclideanSpatial =>
      ∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) := by
    apply continuous_finsetSum
    intro j hj
    exact (((χ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) (tsupport χ.func) :=
    (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.positive hp)))
  obtain ⟨d,hd⟩ := χ.compact.bddAbove_image hgrad.continuousOn
  obtain ⟨r,hr⟩ := χ.compact.bddAbove_image hrho
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let D := max 0 d
  let H := max 0 r
  let B := max 0 b
  have hD : 0≤D := le_max_left _ _
  have hH : 0≤H := le_max_left _ _
  have hB : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hderiv : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D := fun p hp =>
    (hd ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H := fun p hp =>
    (hr ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  refine ⟨2*B^2*(H+D),by positivity,fun f => ?_⟩
  refine (kernelCutoffGradient_core_estimate χ hinj B D H hB hD hH hheight hderiv hdensity f).trans ?_
  rw [mul_assoc (2*B^2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [mul_nonneg hH (sq_nonneg ‖kernelSmoothTestsToL2 f‖),
    mul_nonneg hD (sq_nonneg ‖kernelLocalizedH1 χ f‖)]

lemma kernelEnergyCutoffGradient_eq_zero (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph)
    (hu : kernelEnergyMass u=0) : kernelCutoffGradientCLM χ (kernelEnergyGradient u)=0 := by
  obtain ⟨C,hC,hbound⟩ := kernelCutoffGradient_core_bounded χ hinj
  have hh : ‖kernelCutoffGradientCLM χ (kernelEnergyGradient u)‖^2≤
      C*(‖kernelEnergyLocalize χ u‖^2+‖kernelEnergyMass u‖^2) :=
    kernelEnergyGraphCore_dense.induction_on u (isClosed_le (by fun_prop) (by fun_prop))
      (fun f => by simpa only [kernelEnergyGradient_core,kernelEnergyMass_core,
        kernelEnergyLocalize_core χ hinj] using hbound f)
  rw [kernelEnergyLocalize_eq_zero_of_mass_zero χ hinj u hu,hu] at hh
  have hz : ‖kernelCutoffGradientCLM χ (kernelEnergyGradient u)‖=0 := by simpa using hh
  exact norm_eq_zero.mp hz

lemma kernelCutoffGradient_faithful (g : KernelGradientL2)
    (hg : ∀χ : PositiveChartCutoff,
      Set.InjOn kernelEuclideanProjection (tsupport χ.func) → kernelCutoffGradientCLM χ g=0) : g=0 := by
  let Cutoff := {χ : PositiveChartCutoff // Set.InjOn kernelEuclideanProjection (tsupport χ.func)}
  let U : Cutoff→Set HyperbolicSpace := fun χ => {w | kernelLiftedCutoff χ.1 w≠0}
  have hU : ∀χ,IsOpen (U χ) := fun χ =>
    isOpen_ne.preimage (kernelLiftedCutoff_continuous χ.1)
  have hcover : (Set.univ : Set HyperbolicSpace)⊆⋃χ,U χ := by
    intro w hw
    obtain ⟨χ,hχ,hrange,hinj⟩ :=
      kernelChartCutoff_exists (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
    refine Set.mem_iUnion.mpr ⟨⟨χ,hinj⟩,?_⟩
    change χ.func (hyperbolicEuclideanCoordinates w)≠0
    rw [hχ]
    norm_num
  obtain ⟨r,hr,hcov⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let : Countable r := hr.to_subtype
  have heach (χ : Cutoff) : ∀ᵐw∂KernelFundamentalVolume,kernelLiftedCutoff χ.1 w • g w=0 := by
    have hzero := hg χ.1 χ.2
    change kernelCutoffGradient χ.1 g=0 at hzero
    filter_upwards [kernelCutoffGradient_coe χ.1 g,
      (Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin 3)) (p := (2:ℝ≥0∞)) («μ» := KernelFundamentalVolume))]
      with w hw hz
    rw [hzero] at hw
    exact hw.symm.trans hz
  have hall : ∀ᵐw∂KernelFundamentalVolume,∀χ : r,kernelLiftedCutoff χ.1.1 w • g w=0 :=
    ae_all_iff.mpr (fun χ => heach χ.1)
  apply Lp.ext
  filter_upwards [hall,
    (Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin 3)) (p := (2:ℝ≥0∞)) («μ» := KernelFundamentalVolume))]
    with w hw hz
  obtain ⟨χ,hχ⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ w))
  obtain ⟨hχr,hχw⟩ := Set.mem_iUnion.mp hχ
  have hsm := hw ⟨χ,hχr⟩
  have hne : kernelLiftedCutoff χ.1 w≠0 := hχw
  exact ((smul_eq_zero.mp hsm).resolve_left hne).trans hz.symm

theorem kernelEnergyMass_eq_zero (u : KernelEnergyGraph) (hu : kernelEnergyMass u=0) : u=0 := by
  have hgrad : kernelEnergyGradient u=0 :=
    kernelCutoffGradient_faithful _ (fun χ hinj => kernelEnergyCutoffGradient_eq_zero χ hinj u hu)
  apply norm_eq_zero.mp
  have hn := kernelEnergyGraph_norm_sq u
  simp only [hu,hgrad,norm_zero,zero_pow (by decide : 2≠0),add_zero] at hn
  nlinarith [norm_nonneg u]

theorem kernelEnergyMass_injective : Function.Injective kernelEnergyMass := by
  intro u v huv
  apply sub_eq_zero.mp
  apply kernelEnergyMass_eq_zero
  rw [map_sub,huv,sub_self]

lemma kernelInitialGradient_closure_unique (x : KernelQuotientL2 × KernelGradientL2)
    (hx : x∈kernelInitialGradient.graph.topologicalClosure) (hz : x.1=0) : x.2=0 := by
  let J := (WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).symm
  have hi : J '' (kernelInitialGradientGraph : Set (KernelQuotientL2 × KernelGradientL2))=
      Set.range kernelEnergyCore := by
    ext y
    constructor
    · rintro ⟨z,⟨f,rfl⟩,rfl⟩
      exact ⟨f,rfl⟩
    · rintro ⟨f,rfl⟩
      exact ⟨(kernelSmoothTestsToL2 f,kernelGradientLinear f),⟨f,rfl⟩,rfl⟩
  rw [kernelInitialGradient_graph] at hx
  change x∈closure (kernelInitialGradientGraph : Set (KernelQuotientL2 × KernelGradientL2)) at hx
  have hh := image_closure_subset_closure_image J.continuous ⟨x,hx,rfl⟩
  rw [hi] at hh
  let u : KernelEnergyGraph := ⟨J x,hh⟩
  have hu : kernelEnergyMass u=0 := hz
  have hu0 := kernelEnergyMass_eq_zero u hu
  have hv := congrArg kernelEnergyGradient hu0
  change x.2=kernelEnergyGradient 0 at hv
  simpa only [map_zero] using hv

theorem kernelInitialGradient_isClosable : kernelInitialGradient.IsClosable := by
  refine ⟨kernelInitialGradient.graph.topologicalClosure.toLinearPMap,?_⟩
  exact (Submodule.toLinearPMap_graph_eq _ kernelInitialGradient_closure_unique).symm

def kernelWeakGradient : KernelQuotientL2 →ₗ.[ℂ] KernelGradientL2 := kernelInitialGradient.closure

theorem kernelWeakGradient_closed : kernelWeakGradient.IsClosed :=
  kernelInitialGradient_isClosable.closure_isClosed

theorem kernelWeakGradient_dense_domain : Dense (kernelWeakGradient.domain : Set KernelQuotientL2) :=
  kernelInitialGradient_dense_domain.mono (LinearPMap.le_closure kernelInitialGradient).1

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff InnerProductSpace

lemma kernelEnergyGraph_inner (u v : KernelEnergyGraph) :
    inner ℂ u v=inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
      inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v) := rfl

lemma kernelEnergyMass_norm_le (u : KernelEnergyGraph) : ‖kernelEnergyMass u‖≤‖u‖ := by
  have hh := kernelEnergyGraph_norm_sq u
  nlinarith [sq_nonneg ‖kernelEnergyGradient u‖,norm_nonneg (kernelEnergyMass u),norm_nonneg u]

lemma kernelEnergyMass_opNorm_le : ‖kernelEnergyMass‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using kernelEnergyMass_norm_le)

def kernelVariationalSolution : KernelQuotientL2 →L[ℂ] KernelEnergyGraph :=
  kernelEnergyMass.adjoint

lemma kernelVariationalSolution_equation (F : KernelQuotientL2) (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyMass (kernelVariationalSolution F)) (kernelEnergyMass v)+
      inner ℂ (kernelEnergyGradient (kernelVariationalSolution F)) (kernelEnergyGradient v)=
        inner ℂ F (kernelEnergyMass v) := by
  rw [←kernelEnergyGraph_inner]
  exact kernelEnergyMass.adjoint_inner_left v F

lemma kernelVariationalSolution_unique (F : KernelQuotientL2) (u : KernelEnergyGraph)
    (hu : ∀v : KernelEnergyGraph,
      inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ F (kernelEnergyMass v)) :
    u=kernelVariationalSolution F := by
  apply ext_inner_right ℂ
  intro v
  rw [kernelEnergyGraph_inner,kernelEnergyGraph_inner]
  exact (hu v).trans (kernelVariationalSolution_equation F v).symm

theorem kernelVariationalSolution_existsUnique (F : KernelQuotientL2) :
    ∃!u : KernelEnergyGraph,∀v : KernelEnergyGraph,
      inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ F (kernelEnergyMass v) :=
  ⟨kernelVariationalSolution F,kernelVariationalSolution_equation F,
    fun u hu => kernelVariationalSolution_unique F u hu⟩

lemma kernelVariationalSolution_norm_le (F : KernelQuotientL2) :
    ‖kernelVariationalSolution F‖≤‖F‖ := by
  have hnorm : ‖kernelVariationalSolution‖=‖kernelEnergyMass‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  calc
    ‖kernelVariationalSolution F‖≤‖kernelVariationalSolution‖*‖F‖ :=
      kernelVariationalSolution.le_opNorm F
    _ ≤1*‖F‖ := mul_le_mul_of_nonneg_right (hnorm ▸ kernelEnergyMass_opNorm_le) (norm_nonneg F)
    _ = _ := one_mul _

def kernelVariationalResolvent : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  kernelEnergyMass.comp kernelVariationalSolution

lemma kernelVariationalResolvent_norm_le (F : KernelQuotientL2) :
    ‖kernelVariationalResolvent F‖≤‖F‖ :=
  (kernelEnergyMass_norm_le _).trans (kernelVariationalSolution_norm_le F)

private lemma selfAdjoint_comp_adjoint {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) : IsSelfAdjoint (A.comp A.adjoint) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

lemma kernelVariationalResolvent_selfAdjoint : IsSelfAdjoint kernelVariationalResolvent :=
  selfAdjoint_comp_adjoint kernelEnergyMass

lemma kernelVariationalResolvent_positive (F : KernelQuotientL2) :
    0≤(inner ℂ F (kernelVariationalResolvent F)).re := by
  change 0≤(inner ℂ F (kernelEnergyMass (kernelEnergyMass.adjoint F))).re
  rw [←kernelEnergyMass.adjoint_inner_left]
  exact inner_self_nonneg (𝕜 := ℂ) (x := kernelEnergyMass.adjoint F)

lemma kernelVariationalResolvent_injective : Function.Injective kernelVariationalResolvent := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro F hF
  change kernelEnergyMass (kernelVariationalSolution F)=0 at hF
  have hu : kernelVariationalSolution F=0 := kernelEnergyMass_injective (by
    rw [map_zero]
    exact hF)
  have he : (fun g : KernelQuotientL2 => inner ℂ F g)=(fun _ => (0 : ℂ)) :=
    kernelEnergyMass_dense.equalizer (by fun_prop) continuous_const (by
      funext v
      change inner ℂ F (kernelEnergyMass v)=0
      rw [←kernelEnergyMass.adjoint_inner_left]
      change inner ℂ (kernelVariationalSolution F) v=0
      rw [hu,inner_zero_left])
  exact inner_self_eq_zero.mp (congrFun he F)

lemma kernelVariationalResolvent_dense : DenseRange kernelVariationalResolvent := by
  change Dense (kernelVariationalResolvent.range : Set KernelQuotientL2)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hh := kernelVariationalResolvent.orthogonal_ker
  rw [LinearMap.ker_eq_bot.mpr kernelVariationalResolvent_injective,Submodule.bot_orthogonal_eq_top,
    kernelVariationalResolvent_selfAdjoint.adjoint_eq] at hh
  exact hh.symm

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelLaplacianEquation : (KernelQuotientL2 × KernelQuotientL2) →L[ℂ] KernelQuotientL2 :=
  kernelVariationalResolvent.comp ((ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelQuotientL2)+
    (ContinuousLinearMap.snd ℂ KernelQuotientL2 KernelQuotientL2))-
      (ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelQuotientL2)

def kernelLaplacianGraph : Submodule ℂ (KernelQuotientL2 × KernelQuotientL2) :=
  kernelLaplacianEquation.ker

lemma mem_kernelLaplacianGraph (u f : KernelQuotientL2) :
    (u,f)∈kernelLaplacianGraph ↔ kernelVariationalResolvent (u+f)=u := by
  change kernelVariationalResolvent (u+f)-u=0 ↔ _
  exact sub_eq_zero

lemma kernelLaplacianGraph_unique (x : KernelQuotientL2 × KernelQuotientL2)
    (hx : x∈kernelLaplacianGraph) (hz : x.1=0) : x.2=0 := by
  have hh := (mem_kernelLaplacianGraph x.1 x.2).mp hx
  rw [hz,zero_add] at hh
  apply kernelVariationalResolvent_injective
  rw [map_zero]
  exact hh

def kernelEnergyLaplacian : KernelQuotientL2 →ₗ.[ℂ] KernelQuotientL2 :=
  kernelLaplacianGraph.toLinearPMap

lemma kernelEnergyLaplacian_graph : kernelEnergyLaplacian.graph=kernelLaplacianGraph :=
  Submodule.toLinearPMap_graph_eq _ kernelLaplacianGraph_unique

lemma kernelEnergyLaplacian_closed : kernelEnergyLaplacian.IsClosed := by
  rw [LinearPMap.IsClosed,kernelEnergyLaplacian_graph]
  exact kernelLaplacianEquation.isClosed_ker

lemma kernelEnergyLaplacian_resolvent_graph (F : KernelQuotientL2) :
    (kernelVariationalResolvent F,F-kernelVariationalResolvent F)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  congr 1
  abel

lemma kernelEnergyLaplacian_resolvent_domain (F : KernelQuotientL2) :
    kernelVariationalResolvent F∈kernelEnergyLaplacian.domain :=
  LinearPMap.mem_domain_of_mem_graph (kernelEnergyLaplacian_resolvent_graph F)

lemma kernelEnergyLaplacian_resolvent_apply (F : KernelQuotientL2) :
    kernelEnergyLaplacian ⟨kernelVariationalResolvent F,kernelEnergyLaplacian_resolvent_domain F⟩=
      F-kernelVariationalResolvent F :=
  kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph _)
    (kernelEnergyLaplacian_resolvent_graph F) rfl

lemma kernelEnergyLaplacian_dense_domain :
    Dense (kernelEnergyLaplacian.domain : Set KernelQuotientL2) := by
  apply kernelVariationalResolvent_dense.mono
  rintro _ ⟨F,rfl⟩
  exact kernelEnergyLaplacian_resolvent_domain F

lemma kernelEnergyLaplacian_resolvent_relation (u : kernelEnergyLaplacian.domain) :
    kernelVariationalResolvent (kernelEnergyLaplacian u+u)=u := by
  have hh := kernelEnergyLaplacian.mem_graph u
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hh
  simpa only [add_comm] using hh

lemma kernelEnergyLaplacian_isFormalAdjoint :
    kernelEnergyLaplacian.IsFormalAdjoint kernelEnergyLaplacian := by
  intro u v
  have hh := kernelVariationalResolvent_selfAdjoint.isSymmetric
    (kernelEnergyLaplacian u+u) (kernelEnergyLaplacian v+v)
  simp only [ContinuousLinearMap.coe_coe] at hh
  rw [kernelEnergyLaplacian_resolvent_relation,kernelEnergyLaplacian_resolvent_relation] at hh
  simp only [inner_add_left,inner_add_right] at hh
  exact add_right_cancel hh.symm

lemma kernelEnergyLaplacian_form (u : kernelEnergyLaplacian.domain) (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyLaplacian u) (kernelEnergyMass v)=
      inner ℂ (kernelEnergyGradient (kernelVariationalSolution (kernelEnergyLaplacian u+u)))
        (kernelEnergyGradient v) := by
  have hh := kernelVariationalSolution_equation (kernelEnergyLaplacian u+u) v
  have he : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  rw [he,inner_add_left] at hh
  exact (add_left_cancel (hh.trans (add_comm _ _))).symm

lemma kernelEnergyLaplacian_nonnegative (u : kernelEnergyLaplacian.domain) :
    0≤(inner ℂ (kernelEnergyLaplacian u) (u : KernelQuotientL2)).re := by
  have hh := kernelEnergyLaplacian_form u
    (kernelVariationalSolution (kernelEnergyLaplacian u+u))
  have he : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  rw [he] at hh
  rw [hh]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem kernelEnergyLaplacian_selfAdjoint : IsSelfAdjoint kernelEnergyLaplacian := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro x hx
    obtain ⟨u,hu,hv⟩ := (kernelEnergyLaplacian.adjoint.mem_graph_iff).mp hx
    change (x.1,x.2)∈kernelEnergyLaplacian.graph
    rw [←hu,←hv,kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
    apply ext_inner_right ℂ
    intro F
    have ha := LinearPMap.adjoint_isFormalAdjoint kernelEnergyLaplacian_dense_domain u
      ⟨kernelVariationalResolvent F,kernelEnergyLaplacian_resolvent_domain F⟩
    rw [kernelEnergyLaplacian_resolvent_apply] at ha
    have hs := kernelVariationalResolvent_selfAdjoint.isSymmetric
      ((u : KernelQuotientL2)+kernelEnergyLaplacian.adjoint u) F
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [hs,inner_add_left,ha,inner_sub_right]
    abel
  · exact LinearPMap.IsFormalAdjoint.le_adjoint kernelEnergyLaplacian_dense_domain
      kernelEnergyLaplacian_isFormalAdjoint

end CubicEisenstein

end

end OAI
