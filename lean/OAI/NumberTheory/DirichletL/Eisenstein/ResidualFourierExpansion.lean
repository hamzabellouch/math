import OAI.NumberTheory.DirichletL.Eisenstein.ScatteringResidues
import OAI.NumberTheory.DirichletL.Eisenstein.OppositeCusp

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
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma cubicResidualFullMode_density_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => cubicResidualFullModeAmplitude v h/(v:ℂ)^3)
      (Set.Icc a b) volume := by
  by_cases hh : h=0
  · subst h
    have hi : IntegrableOn (fun v : ℝ =>
        (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)))
        (Set.Icc a b) volume := by
      apply ContinuousOn.integrableOn_Icc
      intro v hv
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const v
        (-(7/3:ℂ)) (Or.inr (ha.trans_le hv.1).ne'))).continuousWithinAt
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (cubicResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)).symm
  · apply ((cubicBesselHeight_integrable a b ha h hh).const_mul
      (cubicResidualFourierCoefficient h)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (cubicResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh).symm

lemma cubicEisensteinResidue_slice_coefficient_ae (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    kernelCuspSliceCoefficient cubicEisensteinResidue h =ᵐ[volume.restrict (Set.Icc a b)]
      (fun v => ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  apply interval_ae_eq_of_boundedContinuous_height_tests a b _ _
    (kernelCuspSliceCoefficient_integrable a b ha h cubicEisensteinResidue)
    ((cubicResidualFullMode_density_integrable a b ha h).const_mul _)
  intro ρ
  rw [←kernelCuspHeightFourier_eq_slice_integral a b ha ρ h cubicEisensteinResidue,
    kernelCuspHeightFourier_residue_full a b ha ρ h,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by ring)

lemma cubicEisensteinResidue_all_slice_coefficients_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      kernelCuspSliceCoefficient cubicEisensteinResidue h v =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  exact ae_all_iff.mpr (fun h => cubicEisensteinResidue_slice_coefficient_ae a b ha h)

lemma cubicEisensteinResidue_all_fourier_integrals_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,
        cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
          ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFullModeAmplitude v h := by
  filter_upwards [cubicEisensteinResidue_all_slice_coefficients_ae a b ha,
    ae_restrict_mem measurableSet_Icc] with v hv hvmem
  intro h
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hvmem.1).ne'
  have he := hv h
  unfold kernelCuspSliceCoefficient at he
  rw [←mul_div_assoc] at he
  exact (div_left_inj' (pow_ne_zero 3 hv0)).mp he

end

local notation "O" => ActualEisensteinCubic.O

lemma cubicResidualFunction_fourier_full (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFullModeAmplitude v h := by
  rw [cubicResidualFunction_fourier v hv h]
  congr 1
  by_cases hh : h=0
  · simp only [hh,cubicResidualFullModeAmplitude,ite_true]
  · simp only [hh,cubicResidualFullModeAmplitude,cubicResidualModeAmplitude,ite_false]

lemma cubicResidualFunction_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => cubicResidualFunction (upperPoint z v hv)) := by
  have hc := cubicResidualNonzeroSeries_height_continuous v hv
  simp only [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  fun_prop

lemma cubicResidualFunction_height_memLp (v : ℝ) (hv : 0<v) :
    MemLp (fun z : ℂ => cubicResidualFunction (cuspCoordinateLift (v,z))) 2
      (volume.restrict periodDomain) := by
  simp_rw [cuspCoordinateLift_positive v _ hv]
  have hc := cubicResidualFunction_height_continuous v hv
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hn : Continuous (fun z : ℂ => ‖cubicResidualFunction (upperPoint z v hv)‖^2) := by
    fun_prop
  apply (hn.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

theorem cubicEisensteinResidue_cell_slices_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b),
      (fun z : ℂ => cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z))))
      =ᵐ[volume.restrict periodDomain]
        (fun z => cubicResidualFunction (cuspCoordinateLift (v,z))) := by
  filter_upwards [cubicEisensteinResidue_all_fourier_integrals_ae a b ha,
    kernelCuspSections_memLp a b ha cubicEisensteinResidue,
    ae_restrict_mem measurableSet_Icc] with v hfour hL hv
  have hpos : 0<v := ha.trans_le hv.1
  apply periodDomain_L2_ext _ _ hL (cubicResidualFunction_height_memLp v hpos)
  intro h
  rw [hfour h]
  symm
  simpa only [cuspCoordinateLift_positive v _ hpos] using
    cubicResidualFunction_fourier_full v hpos h

theorem cubicEisensteinResidue_cell_product_ae (a b : ℝ) (ha : 0<a) :
    (fun q : ℝ × ℂ => cubicEisensteinResidue
      (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift q)))
    =ᵐ[(volume.restrict (Set.Icc a b)).prod (volume.restrict periodDomain)]
      (fun q => cubicResidualFunction (cuspCoordinateLift q)) := by
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · exact cubicEisensteinResidue_cell_slices_ae a b ha
  · exact measurableSet_eq_fun
      ((MeasureTheory.Lp.stronglyMeasurable cubicEisensteinResidue).measurable.comp
        ((measurable_integralOrbitProjection _).comp cuspCoordinateLift_measurable))
      (cubicResidualFunction_continuous.measurable.comp cuspCoordinateLift_measurable)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal Pointwise MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota

lemma periodDomain_memLp_of_continuous (f : ℂ→ℂ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict periodDomain) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable.restrict).mpr
  apply (((hf.norm.pow 2).continuousOn).integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

lemma upperTranslation_mem_kernel (n : ActualEisensteinCubic.O) :
    (upperTranslation n : SL(2,ActualEisensteinCubic.O))∈globalKubotaKernel := by
  exact (globalKubotaKernel_mem _).mpr
    ⟨(upperTranslation n).property,complexCharacter_upperTranslation n⟩

lemma kernelProjection_upper_period (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    integralOrbitProjection globalKubotaKernel (upperPoint (z+3*eisEmbedding n) v hv)=
      integralOrbitProjection globalKubotaKernel (upperPoint z v hv) := by
  let M : globalKubotaKernel := ⟨upperTranslation n,upperTranslation_mem_kernel n⟩
  have ha : integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • upperPoint z v hv=
      upperPoint (z+3*eisEmbedding n) v hv := by
    change (QuotientGroup.mk (complexMatrix (upperTranslation n)*upperSection z v hv) : HyperbolicSpace)=_
    rw [upperTranslation_section]
    rfl
  rw [←ha,integralOrbitProjection_eq]

lemma ae_eq_of_periodDomain_eq (f g : ℂ→ℂ)
    (hf : ∀(n : ActualEisensteinCubic.O)(z : ℂ),f (z+3*eisEmbedding n)=f z)
    (hg : ∀(n : ActualEisensteinCubic.O)(z : ℂ),g (z+3*eisEmbedding n)=g z)
    (he : f=ᵐ[volume.restrict periodDomain]g) : f=ᵐ[volume]g := by
  have hp (p : periodLattice) (z : ℂ) : f (p+ᵥz)=f z ∧ g (p+ᵥz)=g z := by
    obtain ⟨n,rfl⟩ := periodEquiv.surjective p
    change f (3*eisEmbedding n+z)=f z ∧ g (3*eisEmbedding n+z)=g z
    rw [add_comm]
    exact ⟨hf n z,hg n z⟩
  have hi : ∀p : periodLattice,p+ᵥ{z : ℂ | f z≠g z}={z : ℂ | f z≠g z} := by
    intro p
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change (f ((-p)+ᵥz)≠g ((-p)+ᵥz)) ↔ f z≠g z
    rw [(hp (-p) z).1,(hp (-p) z).2]
  have hz : volume ({z : ℂ | f z≠g z}∩periodDomain)=0 := by
    change ∀ᵐz ∂volume.restrict periodDomain,f z=g z at he
    rw [ae_restrict_iff' periodDomain_measurable] at he
    rw [ae_iff] at he
    have hs : {z : ℂ | f z≠g z}∩periodDomain =
        {z : ℂ | ¬(z∈periodDomain → f z=g z)} := by
      ext z
      simp only [Set.mem_ofPred_eq,Set.mem_inter_iff]
      tauto
    rw [hs]
    exact he
  change ∀ᵐz ∂volume,f z=g z
  rw [ae_iff]
  exact periodDomain_fundamental.measure_zero_of_invariant _ hi hz

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

lemma positive_height_interval_cover :
    Set.Ioi (0:ℝ) = ⋃n : ℕ,Set.Icc (1/((n:ℝ)+1)) ((n:ℝ)+1) := by
  ext v
  constructor
  · intro hv
    obtain ⟨n,hn⟩ := exists_nat_gt (max v (1/v))
    have hN : 0<(n:ℝ)+1 := by positivity
    have hvp : 0<v := hv
    have hvN : v≤(n:ℝ)+1 := by linarith [le_max_left v (1/v)]
    have hinv : 1/v≤(n:ℝ)+1 := by linarith [le_max_right v (1/v)]
    have hlow : 1/((n:ℝ)+1)≤v := by
      apply (div_le_iff₀ hN).mpr
      have hh := (div_le_iff₀ hvp).mp hinv
      nlinarith
    exact Set.mem_iUnion.mpr ⟨n,hlow,hvN⟩
  · intro hv
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
    exact lt_of_lt_of_le (by positivity : 0<(1:ℝ)/((n:ℝ)+1)) hn.1

lemma hyperbolic_ae_of_coordinate_ae (f g : HyperbolicSpace→ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ᵐq ∂(volume.restrict (Set.Ioi (0:ℝ))).prod (volume : Measure ℂ),
      f (cuspCoordinateLift q)=g (cuspCoordinateLift q)) : f=ᵐ[hyperbolicVolume]g := by
  have hm := spatialComplexSplit_preserves_volume.restrict_preimage
    (s := Set.Ioi (0:ℝ) ×ˢ (Set.univ : Set ℂ)) (measurableSet_Ioi.prod MeasurableSet.univ)
  have htarget : (volume : Measure (ℝ × ℂ)).restrict (Set.Ioi 0 ×ˢ (Set.univ : Set ℂ)) =
      (volume.restrict (Set.Ioi (0:ℝ))).prod (volume : Measure ℂ) := by
    rw [Measure.volume_eq_prod,←Measure.prod_restrict,Measure.restrict_univ]
  have hsource : spatialComplexSplit ⁻¹' (Set.Ioi (0:ℝ) ×ˢ (Set.univ : Set ℂ)) = euclideanUpperHalf := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true,Set.mem_Ioi,
      spatialComplexSplit_fst,euclideanUpperHalf,Set.mem_ofPred_eq]
  rw [htarget,hsource] at hm
  have heuc := hm.quasiMeasurePreserving.ae he
  have heuc' : ∀ᵐp ∂volume.restrict euclideanUpperHalf,
      f (euclideanToHyperbolic p)=g (euclideanToHyperbolic p) := by
    simpa only [cuspCoordinateLift,spatialComplexSplit.symm_apply_apply] using heuc
  have hweighted : ∀ᵐp ∂hyperbolicEuclideanVolume,
      f (euclideanToHyperbolic p)=g (euclideanToHyperbolic p) :=
    heuc'.filter_mono (withDensity_absolutelyContinuous
      (volume.restrict euclideanUpperHalf) hyperbolicDensity).ae_le
  change ∀ᵐw ∂Measure.map euclideanToHyperbolic hyperbolicEuclideanVolume,f w=g w
  exact (ae_map_iff euclideanToHyperbolic_measurable.aemeasurable (measurableSet_eq_fun hf hg)).mpr hweighted

lemma hyperbolic_eq_ae_of_period_cells (f g : HyperbolicSpace→ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (hfp : ∀(v : ℝ)(hv : 0<v)(z : ℂ)(n : ActualEisensteinCubic.O),
      f (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=f (upperPoint z v hv))
    (hgp : ∀(v : ℝ)(hv : 0<v)(z : ℂ)(n : ActualEisensteinCubic.O),
      g (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=g (upperPoint z v hv))
    (he : ∀(a b : ℝ)(_ha : 0<a),∀ᵐv ∂volume.restrict (Set.Icc a b),
      (fun z => f (cuspCoordinateLift (v,z)))=ᵐ[volume.restrict periodDomain]
        (fun z => g (cuspCoordinateLift (v,z)))) : f=ᵐ[hyperbolicVolume]g := by
  have hplanes (a b : ℝ) (ha : 0<a) : ∀ᵐv ∂volume.restrict (Set.Icc a b),
      ∀ᵐz ∂volume,f (cuspCoordinateLift (v,z))=g (cuspCoordinateLift (v,z)) := by
    filter_upwards [he a b ha,ae_restrict_mem measurableSet_Icc] with v hv hvm
    have hvp : 0<v := ha.trans_le hvm.1
    apply ae_eq_of_periodDomain_eq _ _ _ _ hv
    · intro n z
      simpa only [cuspCoordinateLift_positive v _ hvp] using hfp v hvp z n
    · intro n z
      simpa only [cuspCoordinateLift_positive v _ hvp] using hgp v hvp z n
  have hheights : ∀ᵐv ∂volume.restrict (Set.Ioi (0:ℝ)),
      ∀ᵐz ∂volume,f (cuspCoordinateLift (v,z))=g (cuspCoordinateLift (v,z)) := by
    rw [positive_height_interval_cover,ae_restrict_iUnion_iff]
    intro n
    exact hplanes _ _ (by positivity)
  apply hyperbolic_ae_of_coordinate_ae f g hf hg
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (hf.comp cuspCoordinateLift_measurable) (hg.comp cuspCoordinateLift_measurable))).mpr hheights

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

theorem cubicEisensteinResidue_continuous_representative :
    (fun w => cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] cubicResidualFunction := by
  apply hyperbolic_eq_ae_of_period_cells _ _
    ((MeasureTheory.Lp.stronglyMeasurable cubicEisensteinResidue).measurable.comp
      (measurable_integralOrbitProjection _)) cubicResidualFunction_continuous.measurable
  · intro v hv z n
    exact congrArg cubicEisensteinResidue (kernelProjection_upper_period v hv z n)
  · exact cubicResidualFunction_period
  · exact cubicEisensteinResidue_cell_slices_ae

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding

lemma kernelProjection_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      hyperbolicVolume (integralQuotientVolume globalKubotaKernel) := by
  let proj := integralOrbitProjection globalKubotaKernel
  have hp : Measurable proj := measurable_integralOrbitProjection _
  refine ⟨hp,Measure.AbsolutelyContinuous.mk fun S hS hzero => ?_⟩
  rw [Measure.map_apply hp hS]
  have hd : hyperbolicVolume ((proj ⁻¹' S)∩hyperbolicFundamentalSet globalKubotaKernel)=0 := by
    simpa only [integralQuotientVolume,proj,
      Measure.map_apply (measurable_integralOrbitProjection _) hS,
      Measure.restrict_apply ((measurable_integralOrbitProjection _) hS)] using hzero
  have hinv : ∀M : globalKubotaKernel,M • (proj ⁻¹' S)=proj ⁻¹' S := by
    intro M
    ext w
    constructor
    · rintro ⟨u,hu,rfl⟩
      change proj (M • u)∈S
      change proj u∈S at hu
      rwa [show proj (M • u)=proj u from integralOrbitProjection_eq _ M u]
    · intro hw
      refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
      change proj (M⁻¹ • w)∈S
      rwa [show proj (M⁻¹ • w)=proj w from integralOrbitProjection_eq _ M⁻¹ w]
  exact globalKubotaKernel_isFundamentalDomain.measure_zero_of_invariant (proj ⁻¹' S) hinv hd

lemma kernelLevel_character_ae_on_hyperbolic (F : KernelQuotientL2)
    (M : CubicKubota.levelThree)
    (hchar : kernelLevelPullback M F=CubicKubota.complexCharacter M • F) :
    (fun w : HyperbolicSpace => F (integralOrbitProjection globalKubotaKernel
      (complexMatrix M • w))) =ᵐ[hyperbolicVolume]
      (fun w => CubicKubota.complexCharacter M*
        F (integralOrbitProjection globalKubotaKernel w)) := by
  have he : (fun q => F (kernelLevelAction M q))
      =ᵐ[integralQuotientVolume globalKubotaKernel]
        (fun q => CubicKubota.complexCharacter M*F q) := by
    filter_upwards [kernelLevelPullback_ae_eq M F,
      Lp.coeFn_smul (CubicKubota.complexCharacter M) F] with q hq hs
    rw [hchar] at hq
    exact hq.symm.trans hs
  have hl := kernelProjection_quasiMeasurePreserving.ae_eq_comp he
  simpa only [Function.comp_def,kernelLevelAction_mk] using hl

lemma kernelLevel_character_continuous_representative (F : KernelQuotientL2)
    (f : HyperbolicSpace→ℂ) (hf : Continuous f)
    (hrep : (fun w => F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] f)
    (M : CubicKubota.levelThree)
    (hchar : kernelLevelPullback M F=CubicKubota.complexCharacter M • F)
    (w : HyperbolicSpace) :
    f (complexMatrix M • w)=CubicKubota.complexCharacter M*f w := by
  have hcomp := (measurePreserving_smul (complexMatrix M)
    hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp hrep
  have he : (fun p : HyperbolicSpace => f (complexMatrix M • p))
      =ᵐ[hyperbolicVolume] (fun p => CubicKubota.complexCharacter M*f p) := by
    filter_upwards [hcomp,kernelLevel_character_ae_on_hyperbolic F M hchar,hrep] with p hp hc hr
    exact hp.symm.trans (hc.trans (congrArg (fun z => CubicKubota.complexCharacter M*z) hr))
  have hfun := Measure.eq_of_ae_eq he
    (hf.comp (continuous_hyperbolic_action (complexMatrix M)))
    (continuous_const.mul hf)
  exact congrFun hfun w

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

theorem cubicResidualFunction_automorphy (M : CubicKubota.levelThree) (w : HyperbolicSpace) :
    cubicResidualFunction (complexMatrix M • w)=
      CubicKubota.complexCharacter M*cubicResidualFunction w :=
  kernelLevel_character_continuous_representative cubicEisensteinResidue
    cubicResidualFunction cubicResidualFunction_continuous
    cubicEisensteinResidue_continuous_representative M (cubicEisensteinResidue_character M) w

lemma cubicResidualFunction_ne_zero : cubicResidualFunction≠0 := by
  intro hz
  have he := cubicResidualFunction_fourier_full 1 (by norm_num) 0
  have hconst : (((9*Real.sqrt 3/2:ℝ):ℂ)*
      ((3*(Real.pi:ℂ))*constantArithmeticResidue))≠0 := by
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (by positivity)
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        constantArithmeticResidue_ne_zero
  apply hconst
  simpa only [hz,Pi.zero_apply,zero_mul,integral_zero,
    cubicResidualFullModeAmplitude_zero,Complex.ofReal_one,Complex.one_cpow,mul_one] using he.symm

lemma cubicResidualFunction_exists_ne_zero : ∃w : HyperbolicSpace,cubicResidualFunction w≠0 := by
  by_contra h
  apply cubicResidualFunction_ne_zero
  funext w
  exact not_not.mp (not_exists.mp h w)

open CubicKubota

lemma sourceProjection_continuous (f : HyperbolicSpace→ℂ) (hf : Continuous f) :
    Continuous (sourceProjection f) := by
  unfold sourceProjection
  apply continuous_const.mul
  apply continuous_finsetSum
  intro q hq
  exact hf.comp (continuous_hyperbolic_action _)

lemma sourceProjection_congr_ae (f g : HyperbolicSpace→ℂ)
    (h : f=ᵐ[hyperbolicVolume]g) : sourceProjection f=ᵐ[hyperbolicVolume]sourceProjection g := by
  have htrans (q : levelTwo ⧸ levelThreeInTwo) :
      (fun w => f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w))
        =ᵐ[hyperbolicVolume]
      (fun w => g (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w)) :=
    (measurePreserving_smul _ hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [ae_all_iff.mpr htrans] with w hw
  unfold sourceProjection
  congr 1
  exact Finset.sum_congr rfl (fun q _ => hw q)

lemma kernelSourceProjection_hyperbolic_representative (F : KernelQuotientL2)
    (f : HyperbolicSpace→ℂ)
    (hrep : (fun w => F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] f) :
    (fun w => kernelSourceProjection F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] sourceProjection f := by
  have he := kernelProjection_quasiMeasurePreserving.ae_eq_comp
    (kernelSourceProjection_ae_eq F)
  change (fun w => kernelSourceProjection F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume]
      sourceProjection (fun w => F (integralOrbitProjection globalKubotaKernel w)) at he
  exact he.trans (sourceProjection_congr_ae _ _ hrep)

def cubicSourceResidualFunction : HyperbolicSpace→ℂ := sourceProjection cubicResidualFunction

lemma cubicSourceResidualFunction_continuous : Continuous cubicSourceResidualFunction :=
  sourceProjection_continuous cubicResidualFunction cubicResidualFunction_continuous

theorem cubicSourceResidualFunction_automorphy (M : levelTwo) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter M*cubicSourceResidualFunction w :=
  sourceProjection_automorphy cubicResidualFunction cubicResidualFunction_automorphy M w

lemma cubicSourceResidualFunction_rational_invariant (M : SL(2,ℤ)) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (rationalEmbedding M) • w)=
      cubicSourceResidualFunction w := by
  have he := cubicSourceResidualFunction_automorphy (rationalLift M) w
  rw [levelTwoComplexCharacter_rationalLift,one_mul] at he
  exact he

theorem cubicSourceResidualFunction_represents_projection :
    (fun w => kernelSourceProjection cubicEisensteinResidue
      (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] cubicSourceResidualFunction :=
  kernelSourceProjection_hyperbolic_representative cubicEisensteinResidue
    cubicResidualFunction cubicEisensteinResidue_continuous_representative

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def rationalUnipotent (t : ℤ) : SL(2,ℤ) :=
  ⟨!![1,t;0,1],by simp [Matrix.det_fin_two]⟩

lemma rationalUnipotent_add (a b : ℤ) :
    rationalUnipotent (a+b)=rationalUnipotent a*rationalUnipotent b := by
  apply Subtype.ext
  change (!![1,a+b;0,1] : Matrix (Fin 2) (Fin 2) ℤ) =
    (!![1,a;0,1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1,b;0,1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

lemma rationalUnipotent_zero : rationalUnipotent 0=1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rationalUnipotent]

lemma rationalUnipotent_neg (a : ℤ) : rationalUnipotent (-a)=(rationalUnipotent a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←rationalUnipotent_add,neg_add_cancel,rationalUnipotent_zero]

lemma rationalUnipotent_one : rationalUnipotent 1=ModularGroup.T := rfl

lemma row_unipotent_conjugate (t : ℤ) (M : levelThree) :
    row (levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M)=
      Matrix.vecMul (row M) (rationalEmbedding (rationalUnipotent t):SL(2,ActualEisensteinCubic.O)) := by
  have hmap (u : ℤ) :
      (rationalEmbedding (rationalUnipotent u) : Matrix (Fin 2) (Fin 2) O) =
        !![1,(u : O);0,1] := by
    apply Matrix.ext
    intro i j
    change (Int.castRingHom O) ((!![1,u;0,1] : Matrix (Fin 2) (Fin 2) ℤ) i j) = _
    fin_cases i <;> fin_cases j <;> simp
  change ((rationalEmbedding (rationalUnipotent (-t)) * (M : SL(2,O)) *
      (rationalEmbedding (rationalUnipotent (-t)))⁻¹ : SL(2,O)) : Matrix (Fin 2) (Fin 2) O) 1 =
    Matrix.vecMul ((M : SL(2,O)) 1)
      (rationalEmbedding (rationalUnipotent t) : Matrix (Fin 2) (Fin 2) O)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    hmap, Matrix.adjugate_fin_two]
  funext j
  fin_cases j <;> simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

def cuspUnipotentTranslate (t : ℤ) : CuspCosets→CuspCosets :=
  Quotient.map (fun M => levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M) (by
    intro M N h
    change row (levelThreeConjugate _ M)=row (levelThreeConjugate _ N)
    rw [row_unipotent_conjugate,row_unipotent_conjugate,show row M=row N from h])

lemma cuspUnipotentTranslate_inverse (t : ℤ) (x : CuspCosets) :
    cuspUnipotentTranslate (-t) (cuspUnipotentTranslate t x)=x := by
  induction x using Quotient.inductionOn with
  | _ M =>
    change cosetOf (levelThreeConjugate (rationalEmbedding (rationalUnipotent (- -t)))
      (levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M))=cosetOf M
    rw [←levelThreeConjugate_mul,←map_mul,←rationalUnipotent_add]
    simp only [neg_neg,add_neg_cancel,rationalUnipotent_zero,map_one,levelThreeConjugate_one]

def cuspUnipotentEquiv (t : ℤ) : CuspCosets≃CuspCosets where
  toFun := cuspUnipotentTranslate t
  invFun := cuspUnipotentTranslate (-t)
  left_inv := cuspUnipotentTranslate_inverse t
  right_inv x := by simpa only [neg_neg] using cuspUnipotentTranslate_inverse (-t) x

lemma cosetRow_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    cosetRow (cuspUnipotentEquiv t x)=
      Matrix.vecMul (cosetRow x) (rationalEmbedding (rationalUnipotent t):SL(2,ActualEisensteinCubic.O)) := by
  induction x using Quotient.inductionOn with
  | _ M => exact row_unipotent_conjugate t M

lemma cosetCharacter_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    cosetCharacter (cuspUnipotentEquiv t x)=cosetCharacter x := by
  induction x using Quotient.inductionOn with
  | _ M => exact complexCharacter_conjugate_rational (rationalUnipotent (-t)) M

lemma embeddedRow_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    embeddedRow (cuspUnipotentEquiv t x)=
      Matrix.vecMul (embeddedRow x) (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)):SL(2,ℂ)) := by
  funext j
  simp only [embeddedRow,Function.comp_def,cosetRow_cuspUnipotentEquiv,
    Matrix.vecMul,dotProduct,map_sum,map_mul,integralComplexMatrix_apply]

lemma summand_unipotent (t : ℤ) (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    summand (integralComplexMatrix (rationalEmbedding (rationalUnipotent t))*g) s x=
      summand g s (cuspUnipotentEquiv t x) := by
  rw [summand,summand,cosetCharacter_cuspUnipotentEquiv,
    embeddedRow_cuspUnipotentEquiv,←rowOperator_apply,rowOperator_mul]

theorem eisenstein_unipotent (t : ℤ) (g : SL(2,ℂ)) (s : ℂ) :
    eisenstein (integralComplexMatrix (rationalEmbedding (rationalUnipotent t))*g) s=eisenstein g s := by
  unfold eisenstein
  simp_rw [summand_unipotent]
  exact (cuspUnipotentEquiv t).tsum_eq _

theorem hyperbolicEisenstein_unipotent (t : ℤ) (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)) • w)=
      hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with
  | _ g => exact eisenstein_unipotent t g s

end CubicEisenstein

end

end OAI
