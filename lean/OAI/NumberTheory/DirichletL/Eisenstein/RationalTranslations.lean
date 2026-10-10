import OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierExpansion

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
open scoped BigOperators Classical MatrixGroups

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def rationalComplex : SL(2,ℤ) →* SL(2,ℂ) := integralComplexMatrix.comp rationalEmbedding

lemma rationalUnipotent_nat (n : ℕ) : rationalUnipotent (n:ℤ)=ModularGroup.T^n := by
  induction n with
  | zero => simpa using rationalUnipotent_zero
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,rationalUnipotent_add,ih,rationalUnipotent_one,pow_succ]

lemma rationalComplex_S_sq_row (v : Fin 2→ℂ) :
    rowOperator (rationalComplex (ModularGroup.S^2)) v = -v := by
  have hS : ((ModularGroup.S ^ 2 : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-1,0;0,-1] := by decide
  have hC : (rationalComplex (ModularGroup.S ^ 2) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![-1,0;0,-1] := by
    apply Matrix.ext
    intro i j
    change eisEmbedding ((Int.castRingHom O) ((ModularGroup.S ^ 2 : SL(2,ℤ)) i j)) = _
    rw [congrFun (congrFun hS i) j]
    fin_cases i <;> fin_cases j <;> simp
  rw [rowOperator_apply,hC]
  funext j
  fin_cases j <;> simp [Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma hyperbolicEisenstein_S_sq (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.S^2) • w)=hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    change eisenstein (rationalComplex (ModularGroup.S^2)*g) s=eisenstein g s
    apply tsum_congr
    intro x
    unfold summand
    rw [←rowOperator_mul,rationalComplex_S_sq_row,map_neg]
    simp [rowEnergy]

lemma hyperbolicEisenstein_T_pow (s : ℂ) (n : ℕ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.T^n) • w)=hyperbolicEisenstein s w := by
  simpa only [rationalUnipotent_nat,rationalComplex,MonoidHom.comp_apply] using hyperbolicEisenstein_unipotent (n:ℤ) s w

lemma hyperbolicEisenstein_S_even (s : ℂ) (e : Fin 2) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.S^(2*e.val)) • w)=hyperbolicEisenstein s w := by
  fin_cases e
  · simp
  · exact hyperbolicEisenstein_S_sq s w

lemma hyperbolicEisenstein_bruhat (s : ℂ) (e : Fin 2) (a : Fin 3⊕(Fin 3×Fin 3)) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (rationalBruhatRep (e,a)) • w)=
      match a with
      | Sum.inl _ => hyperbolicEisenstein s w
      | Sum.inr ab => hyperbolicEisenstein s
          (rationalComplex ModularGroup.S • (rationalComplex (ModularGroup.T^ab.2.val) • w)) := by
  simp only [rationalBruhatRep,map_mul,mul_smul,hyperbolicEisenstein_S_even]
  cases a with
  | inl a => exact hyperbolicEisenstein_T_pow s a.val w
  | inr ab => simp only [map_mul,mul_smul,hyperbolicEisenstein_T_pow]

theorem sourceEisenstein_four_cusps (s : ℂ) (w : HyperbolicSpace) :
    sourceEisenstein s w = (4:ℂ)⁻¹ * (hyperbolicEisenstein s w +
      ∑ b : Fin 3, hyperbolicEisenstein s
        (rationalComplex ModularGroup.S • (rationalComplex (ModularGroup.T^b.val) • w))) := by
  rw [sourceEisenstein,sourceProjection_eq_twentyFour]
  change (24:ℂ)⁻¹ * (∑ i : RationalBruhatIndex,
    hyperbolicEisenstein s (rationalComplex (rationalBruhatRep i) • w)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hyperbolicEisenstein_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  ring

end

section

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def translatedCuspCompact (M:levelTwo):Set KernelQuotient:=
  kernelSourceAction M '' kernelCuspAverageCompact

lemma translatedCuspCompact_isCompact (M:levelTwo):IsCompact (translatedCuspCompact M):=
  kernelCuspAverageCompact_isCompact.image (kernelSourceAction_continuous M)

def translatedCuspFourier (h:Eis) (M:levelTwo):KernelQuotientL2→L[ℂ]ℂ:=
  (kernelCuspFourier h).comp (kernelSourcePullback M).toContinuousLinearMap

lemma translatedCuspFourier_integral (h:Eis) (M:levelTwo) (F:KernelQuotientL2):
    translatedCuspFourier h M F=∫w in cuspPeriodStrip 5 6,
      F (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
        cuspFourierPhase h w∂hyperbolicVolume:=by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,kernelCuspFourier_integral]
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelSourcePullback_ae_eq M F) (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w) hw

lemma translatedCuspFourier_restrict (h:Eis) (M:levelTwo) (F:KernelQuotientL2):
    translatedCuspFourier h M
      (kernelMassRestrictionCLM (translatedCuspCompact M)
        (translatedCuspCompact_isCompact M).measurableSet F)=translatedCuspFourier h M F:=by
  rw [translatedCuspFourier_integral,translatedCuspFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe (translatedCuspCompact M)
      (translatedCuspCompact_isCompact M).measurableSet F)
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  have hmem:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedCuspCompact M:=
    ⟨_,kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem hmem _))

def translatedCuspFamily (h:Eis) (M:levelTwo) (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ):ℂ:=
  translatedCuspFourier h M
    (kernelLocalCorrectedSeed (translatedCuspCompact M) (translatedCuspCompact_isCompact M) a b ha hab s)

lemma translatedCuspFamily_meromorphicAt (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b):
    MeromorphicAt (translatedCuspFamily h M a b ha hab) (4/3:ℂ):=
  meromorphicAt_clm (translatedCuspFourier h M)
    (kernelLocalCorrectedSeed_meromorphicAt _ (translatedCuspCompact_isCompact M) a b ha hab)

lemma translatedCuspFamily_analyticAt_nonreal (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ) (hs:s.re≠1) (hi:s.im≠0):
    AnalyticAt ℂ (translatedCuspFamily h M a b ha hab) s:=by
  exact (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (translatedCuspFourier h M) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (translatedCuspCompact_isCompact M)
        a b ha hab s hs hi) rfl

lemma translatedCuspFamily_residue_limit (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b):
    Tendsto (fun s:ℂ=>(s-4/3)*translatedCuspFamily h M a b ha hab s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (translatedCuspFourier h M (kernelEisensteinResidueVector a b ha hab))):=by
  have hh:=(translatedCuspFourier h M).continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit _ (translatedCuspCompact_isCompact M) a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,translatedCuspFourier_restrict,
    translatedCuspFamily] using hh

lemma translatedCuspFamily_actual_integral (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ):
    translatedCuspFamily h M a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s
        (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
          cuspFourierPhase h w∂hyperbolicVolume:=by
  rw [translatedCuspFamily,translatedCuspFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelLocalCorrectedSeed_ae_eq _ (translatedCuspCompact_isCompact M) a b ha hab s)
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  have hmem:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedCuspCompact M:=
    ⟨_,kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem hmem _))

theorem translatedCuspFamily_initial (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (ha1:1<a) (s:ℂ) (hs:4<s.re) (hi:0<s.im):
    translatedCuspFamily h M a b ha hab s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspFourierPhase h w∂hyperbolicVolume:=by
  have hcorrected:kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith):=by
    filter_upwards [kernelEisensteinL2Correction_initial_overlap a b ha1 hab s hs hi] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hcorrected
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  rw [translatedCuspFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (by dsimp only [Function.comp_def];rw [kernelSourceAction_mk,kernelQuotientEisenstein_mk]))

end

section

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix
open CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def oppositeSource:levelTwo:=rationalLift ModularGroup.S

lemma oppositeSource_matrix:sourceComplexMatrix oppositeSource=oppositeMatrix:=by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oppositeSource,sourceComplexMatrix,rationalLift,rationalEmbedding,
      integralComplexMatrix,Matrix.SpecialLinearGroup.map_apply_coe,ModularGroup.coe_S,oppositeMatrix]

lemma hyperbolicEisenstein_opposite_upper (s:ℂ) (z:ℂ) (v:ℝ) (hv:0<v):
    hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • upperPoint z v hv)=
      oppositeEisenstein z v hv s:=by
  rw [oppositeSource_matrix]
  rfl

theorem opposite_cusp_fourier_average (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
        cuspFourierPhase h w∂hyperbolicVolume)=
      unramifiedCubicGaussSeries s (9*h)*cuspWhittakerHeightFactor s h:=by
  let g:HyperbolicSpace→ℂ:=fun w=>
    hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*cuspFourierPhase h w
  have hg:Continuous g:=((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable g hg)]
  have heq:(∫v in Set.Icc (5:ℝ) 6,
      (∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,unramifiedCubicGaussSeries s (9*h)*
        ((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)):=by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0:0<v:=by linarith [hv.1]
    have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
    have hslice:(∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
          unramifiedCubicGaussSeries s (9*h):=by
      simp_rw [g,cuspCoordinateLift_positive v _ hv0,hyperbolicEisenstein_opposite_upper,
        cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      exact oppositeEisenstein_fourier v hv0 s hs h
    have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3:=by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [hslice,hp]
    ring
  rw [heq,integral_const_mul]
  rfl

lemma translatedCuspFamily_opposite_initial (h:Eis) (s:ℂ)
    (hs:4<s.re) (hi:0<s.im):
    translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num) s=
      unramifiedCubicGaussSeries s h*cuspWhittakerHeightFactor s (3*h):=by
  rw [translatedCuspFamily_initial (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num) (by norm_num) s hs hi,
    opposite_cusp_fourier_average s (by linarith),
    show (9:Eis)*(3*h)=27*h by ring,unramifiedCubicGaussSeries_twentySeven]

def continuedUnramifiedGauss (h:Eis) (s:ℂ):ℂ:=
  translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num) s/
    cuspWhittakerHeightFactor s (3*h)

def unramifiedGaussResidue (h:Eis):ℂ:=
  translatedCuspFourier (3*h) oppositeSource cubicEisensteinResidue/
    cuspWhittakerHeightFactor (4/3:ℂ) (3*h)

theorem continuedUnramifiedGauss_meromorphicAt_center (h:Eis):
    MeromorphicAt (continuedUnramifiedGauss h) (4/3:ℂ):=by
  exact (translatedCuspFamily_meromorphicAt (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num)).div
      (cuspWhittakerHeightFactor_analyticAt (3*h) (4/3) (by norm_num)).meromorphicAt

theorem continuedUnramifiedGauss_meromorphicOn_upper (h:Eis):
    MeromorphicOn (continuedUnramifiedGauss h) {s:ℂ|1<s.re ∧ 0<s.im}:=by
  intro s hs
  exact (translatedCuspFamily_analyticAt_nonreal (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num) s (ne_of_gt hs.1) (ne_of_gt hs.2)).meromorphicAt.div
      (cuspWhittakerHeightFactor_analyticAt (3*h) s hs.1).meromorphicAt

theorem continuedUnramifiedGauss_residue_limit (h:Eis):
    Tendsto (fun s:ℂ=>(s-4/3)*continuedUnramifiedGauss h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (unramifiedGaussResidue h)):=by
  have hd:Tendsto (fun s:ℂ=>cuspWhittakerHeightFactor s (3*h))
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) (3*h))):=
    (cuspWhittakerHeightFactor_analyticAt (3*h) (4/3) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hh:=(translatedCuspFamily_residue_limit (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num)).div hd (cuspWhittakerHeightFactor_center_ne_zero (3*h))
  convert hh using 1
  · funext s
    simp only [continuedUnramifiedGauss,Pi.div_apply]
    ring
  · rfl

theorem continuedUnramifiedGauss_initial (h:Eis) (s:ℂ)
    (hs:4<s.re) (hi:0<s.im) (hH:cuspWhittakerHeightFactor s (3*h)≠0):
    continuedUnramifiedGauss h s=unramifiedCubicGaussSeries s h:=by
  rw [continuedUnramifiedGauss,translatedCuspFamily_opposite_initial h s hs hi,
    mul_div_cancel_right₀ _ hH]

theorem continuedUnramifiedGauss_initial_open (h:Eis):
    ∃U:Set ℂ,IsOpen U ∧ U.Nonempty ∧ U⊆{s:ℂ|4<s.re ∧ 0<s.im} ∧
      Set.EqOn (continuedUnramifiedGauss h) (fun s=>unramifiedCubicGaussSeries s h) U:=by
  obtain ⟨ε,hε,hball⟩:=Metric.eventually_nhds_iff.mp (cuspWhittakerHeightFactor_ne_zero_near_five (3*h))
  let z:ℂ:=5+(ε/2:ℝ)*Complex.I
  have hz:dist z (5:ℂ)<ε:=by
    have he:dist z (5:ℂ)=ε/2:=by simp [z,dist_eq_norm,hε.le]
    rw [he]
    linarith
  have hzim:0<z.im:=by simpa [z] using half_pos hε
  refine ⟨Metric.ball (5:ℂ) ε ∩ {s:ℂ|0<s.im},
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im),
    ⟨z,hz,hzim⟩,?_,?_⟩
  · intro s hs
    exact ⟨(hball hs.1).1,hs.2⟩
  · intro s hs
    exact continuedUnramifiedGauss_initial h s (hball hs.1).1 hs.2 (hball hs.1).2

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma gaussRep_mk_congr (c d : Eis) :
    c ∣ GaussianShiftedPartition.representative c (Ideal.Quotient.mk (Ideal.span {c}) d)-d := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact GaussianShiftedPartition.representative_spec c _

def cubicUnitCRTMap (a b : Eis) (r : CubicUnitResidue (a*b)) :
    CubicUnitResidue a × CubicUnitResidue b :=
  let d:=GaussianShiftedPartition.representative (a*b) r.1
  let hd:IsCoprime (a*b) d:=by
    apply (isUnit_quotient_span_iff (a*b) d).mp
    simpa only [d,GaussianShiftedPartition.representative_spec] using r.2
  (⟨Ideal.Quotient.mk (Ideal.span {a}) d,
      (isUnit_quotient_span_iff a d).mpr hd.of_mul_left_left⟩,
   ⟨Ideal.Quotient.mk (Ideal.span {b}) d,
      (isUnit_quotient_span_iff b d).mpr hd.of_mul_left_right⟩)

lemma cubicUnitCRTMap_injective (a b : Eis) (hab : IsCoprime a b) :
    Function.Injective (cubicUnitCRTMap a b) := by
  intro r t he
  have h1:=congrArg (fun z : CubicUnitResidue a × CubicUnitResidue b=>z.1.1) he
  have h2:=congrArg (fun z : CubicUnitResidue a × CubicUnitResidue b=>z.2.1) he
  change Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) t.1) at h1
  change Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) t.1) at h2
  have hdiv : a*b ∣ GaussianShiftedPartition.representative (a*b) r.1-
      GaussianShiftedPartition.representative (a*b) t.1 :=
    hab.mul_dvd
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1))
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2))
  apply Subtype.ext
  rw [←GaussianShiftedPartition.representative_spec (a*b) r.1,
    ←GaussianShiftedPartition.representative_spec (a*b) t.1]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hdiv)

lemma cubicUnitCRTMap_surjective (a b : Eis) (hab : IsCoprime a b) :
    Function.Surjective (cubicUnitCRTMap a b) := by
  rintro ⟨r,t⟩
  obtain ⟨u,v,huv⟩:=hab
  let delta:=GaussianShiftedPartition.representative a r.1
  let xi:=GaussianShiftedPartition.representative b t.1
  let d:=v*b*delta+u*a*xi
  have hda:a∣d-delta:=⟨u*(xi-delta),by dsimp [d];linear_combination delta*huv⟩
  have hdb:b∣d-xi:=⟨v*(delta-xi),by dsimp [d];linear_combination xi*huv⟩
  have had:IsCoprime a delta:=by
    apply (isUnit_quotient_span_iff a delta).mp
    simpa only [delta,GaussianShiftedPartition.representative_spec] using r.2
  have hbd:IsCoprime b xi:=by
    apply (isUnit_quotient_span_iff b xi).mp
    simpa only [xi,GaussianShiftedPartition.representative_spec] using t.2
  have hd:IsCoprime (a*b) d:=
    ((isCoprime_right_congr_of_dvd a d delta hda).mpr had).mul_left
      ((isCoprime_right_congr_of_dvd b d xi hdb).mpr hbd)
  let q:CubicUnitResidue (a*b):=⟨Ideal.Quotient.mk (Ideal.span {a*b}) d,
    (isUnit_quotient_span_iff (a*b) d).mpr hd⟩
  refine ⟨q,Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · change Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) q.1)=r.1
    rw [←GaussianShiftedPartition.representative_spec a r.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh:a∣GaussianShiftedPartition.representative (a*b) q.1-d:=
      (dvd_mul_right a b).trans (gaussRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hda
  · change Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) q.1)=t.1
    rw [←GaussianShiftedPartition.representative_spec b t.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh:b∣GaussianShiftedPartition.representative (a*b) q.1-d:=
      (dvd_mul_left b a).trans (gaussRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hdb

def cubicUnitCRTEquiv (a b:Eis) (hab:IsCoprime a b):
    CubicUnitResidue (a*b)≃CubicUnitResidue a×CubicUnitResidue b:=
  Equiv.ofBijective (cubicUnitCRTMap a b)
    ⟨cubicUnitCRTMap_injective a b hab,cubicUnitCRTMap_surjective a b hab⟩

lemma residueAdditive_unit_crt (h a b alpha beta d:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1):
    residueAdditive (3*h) (a*b) d=
      residueAdditive (3*(h*alpha)) a d*residueAdditive (3*(h*beta)) b d:=by
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  have hbeq:=congrArg eisEmbedding hbez
  simp only [map_add,map_mul,map_one] at hbeq
  simp only [cuspFrequency,map_mul,map_ofNat]
  field_simp [hae,hbe,eisLam_ne_zero]
  linear_combination -(eisEmbedding h*eisEmbedding d)*hbeq

lemma cubicUnitCRT_summand (h a b alpha beta:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1) (r:CubicUnitResidue (a*b)):
    eisEmbedding (symbol (GaussianShiftedPartition.representative (a*b) r.1) (a*b))*
      residueAdditive (3*h) (a*b) (GaussianShiftedPartition.representative (a*b) r.1)=
    (eisEmbedding (symbol (GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1) a)*
      residueAdditive (3*(h*alpha)) a (GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1))*
    (eisEmbedding (symbol (GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1) b)*
      residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1)):=by
  let d:=GaussianShiftedPartition.representative (a*b) r.1
  let delta:=GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1
  let xi:=GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1
  have hdelta:a∣delta-d:=gaussRep_mk_congr a d
  have hxi:b∣xi-d:=gaussRep_mk_congr b d
  change eisEmbedding (symbol d (a*b))*residueAdditive (3*h) (a*b) d=
    (eisEmbedding (symbol delta a)*residueAdditive (3*(h*alpha)) a delta)*
    (eisEmbedding (symbol xi b)*residueAdditive (3*(h*beta)) b xi)
  rw [symbol_mul_denominator,map_mul,symbol_congr hdelta,symbol_congr hxi,
    residueAdditive_unit_crt h a b alpha beta d ha hb hbez,
    residueAdditive_three_congr (h*alpha) a delta d ha hdelta,
    residueAdditive_three_congr (h*beta) b xi d hb hxi]
  ring

theorem cubicUnitGaussSum_crt (h a b alpha beta:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1):
    cubicUnitGaussSum h (a*b)=
      cubicUnitGaussSum (h*alpha) a*cubicUnitGaussSum (h*beta) b:=by
  have hab:IsCoprime a b:=⟨beta,alpha,by linear_combination hbez⟩
  let f:CubicUnitResidue a→ℂ:=fun r=>eisEmbedding
    (symbol (GaussianShiftedPartition.representative a r.1) a)*
    residueAdditive (3*(h*alpha)) a (GaussianShiftedPartition.representative a r.1)
  let g:CubicUnitResidue b→ℂ:=fun r=>eisEmbedding
    (symbol (GaussianShiftedPartition.representative b r.1) b)*
    residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b r.1)
  have he:cubicUnitGaussSum h (a*b)=∑'r:CubicUnitResidue (a*b),
      f (cubicUnitCRTEquiv a b hab r).1*g (cubicUnitCRTEquiv a b hab r).2:=by
    unfold cubicUnitGaussSum
    apply tsum_congr
    intro r
    exact cubicUnitCRT_summand h a b alpha beta ha hb hbez r
  rw [he,(cubicUnitCRTEquiv a b hab).tsum_eq (fun r=>f r.1*g r.2)]
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span ha
  let:Finite (Eis⧸Ideal.span {b}):=finite_quotient_span hb
  let:Fintype (CubicUnitResidue a):=Fintype.ofFinite _
  let:Fintype (CubicUnitResidue b):=Fintype.ofFinite _
  change (∑'r:CubicUnitResidue a×CubicUnitResidue b,f r.1*g r.2)=
    (∑'r:CubicUnitResidue a,f r)*(∑'r:CubicUnitResidue b,g r)
  simp only [tsum_fintype,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

theorem cubicUnitGaussSum_coprime_product (h a b:Eis) (ha:a≠0) (hb:b≠0)
    (hap:lambda^2∣a-1) (hbp:lambda^2∣b-1) (hab:IsCoprime a b):
    cubicUnitGaussSum h (a*b)=cubicUnitGaussSum h a*cubicUnitGaussSum (h*a) b:=by
  obtain ⟨beta,alpha,hbez⟩:=hab
  have hbez':alpha*b+beta*a=1:=by linear_combination hbez
  have hab':IsCoprime a b:=⟨beta,alpha,hbez⟩
  have hA:=cubicUnitGaussSum_frequency_twist (h*alpha) a b ha hap hab'
  rw [cubicUnitGaussSum_frequency_congr _ h a ha
    (show a∣(h*alpha)*b-h from ⟨-h*beta,by linear_combination h*hbez'⟩)] at hA
  have hB:=cubicUnitGaussSum_frequency_twist (h*beta) b a hb hbp hab'.symm
  rw [cubicUnitGaussSum_frequency_congr _ h b hb
    (show b∣(h*beta)*a-h from ⟨-h*alpha,by linear_combination h*hbez'⟩)] at hB
  rw [cubicUnitGaussSum_crt h a b alpha beta ha hb hbez',←hA,←hB,
    symbol_reciprocity b a hb ha hbp hap]
  have hshift:=cubicUnitGaussSum_frequency_twist h b a hb hbp hab'.symm
  have hc:(eisEmbedding (symbol a b))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime a b hbp hab',map_one]
  rw [←hshift]
  calc
    _=(eisEmbedding (symbol a b))^3*cubicUnitGaussSum h a*cubicUnitGaussSum (h*a) b:=by ring
    _=_:=by rw [hc,one_mul]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedCongruence_zero (j : Fin 3) (n : ℕ) :
    ramifiedCongruence (0:Eis) j.val n ↔ j=0 ∧ 3∣n := by
  have hz : ActualEisensteinCoordinates.coords (0:Eis)=(0,0) := by
    have hh:=ShortDraftLatticeCount.coords_eval 0 0
    simpa [ActualEisensteinCoordinates.eval] using hh
  simp only [ramifiedCongruence,hz,add_zero,sub_zero]
  rw [←Int.natCast_dvd_natCast]
  constructor
  · rintro ⟨h1,h2⟩
    have hj : j.val=0 := by omega
    exact ⟨Fin.ext hj,by simpa only [hj,Nat.cast_zero,Nat.cast_ofNat,mul_zero,zero_add] using h1⟩
  · rintro ⟨rfl,hn⟩
    simpa using And.intro hn (dvd_zero (3:ℤ))

lemma arithmeticResidueSum_zero_ramified (u : Eisˣ) (n : ℕ) :
    arithmeticResidueSum 0 (u.val*lambda^(n+2))=
      if u=1 ∨ u= -1 then if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0 else 0 := by
  have hp : residueAdditive (0:Eis) 3 1=1 := by
    simp [residueAdditive,cuspFrequency]
  by_cases hu : u=1 ∨ u= -1
  · have hs : (u:Eis)=omega^0 ∨ (u:Eis)=-(omega^0) := by
      rcases hu with rfl|rfl <;> simp
    rw [ramified_arithmetic_explicit_table 0 0 u (n+2) 0 (by omega) hs (by simp),
      show ramifiedCongruence (0:Eis) 0 (n+2) ↔ 3∣n+2 by
        simpa using ramifiedCongruence_zero (0:Fin 3) (n+2),hp,mul_one,ite_eq_left hu]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
  · obtain ⟨j,hj⟩:=unit_eq_sign_omega u
    have hj0 : j≠0 := by
      intro he
      subst j
      apply hu
      rcases hj with hj|hj
      · left; apply Units.ext; simpa using hj
      · right; apply Units.ext; simpa using hj
    rw [ramified_arithmetic_explicit_table 0 0 u (n+2) j.val (by omega) hj (by simp),
      ramifiedCongruence_zero,ite_eq_right (by simp [hj0]),ite_eq_right hu]

lemma arithmeticDirichletSeries_zero_separate (s : ℂ) (hs : 2<s.re) :
    arithmeticDirichletSeries s 0=
      (∑'u:Eisˣ,∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
        arithmeticResidueSum 0 (u.val*lambda^(n+2)))*unramifiedCubicGaussSeries s 0 := by
  rw [arithmeticDirichletSeries_ramified_reindex s hs 0,←tsum_mul_right]
  apply tsum_congr
  intro u
  rw [←tsum_mul_right]
  apply tsum_congr
  intro n
  rw [unramifiedCubicGaussSeries,←tsum_mul_left]
  apply tsum_congr
  intro I
  change (if ramifiedLower u n I=0 then 0 else
    ((‖eisEmbedding (ramifiedLower u n I)‖^2:ℝ):ℂ)^(-s)*
      arithmeticResidueSum 0 (ramifiedLower u n I))=_
  rw [ite_eq_right (ramifiedLower_ne_zero u n I),eisEmbedding_norm_sq_eq_absNorm_span,
    Complex.ofReal_natCast,ramifiedLower_span,map_mul,map_pow,ramifiedIdeal_absNorm,
    Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have hp:lambda^2∣primaryGenerator I.1-1:=(primaryGenerator_spec I.1 I.2).2
  rw [show arithmeticResidueSum 0 (ramifiedLower u n I)=
      eisEmbedding (symbol (u.val*lambda^(n+2)) (primaryGenerator I.1))*
      eisEmbedding (symbol (3*(u.val*lambda^(n+2))) (primaryGenerator I.1))*
      arithmeticResidueSum 0 (u.val*lambda^(n+2))*cubicUnitGaussSum 0 (primaryGenerator I.1) from
    arithmeticResidueSum_ramified_split 0 u (n+2) (by omega) _ hp]
  have hg:=cubicUnitGaussSum_phase_shift 0 (u.val*lambda^(n+2)) (primaryGenerator I.1)
    I.2 hp (ramified_primary_coprime u (n+2) _ hp)
  simp only [zero_mul] at hg
  linear_combination ((3^(n+2):ℕ):ℂ)^(-s)*(Ideal.absNorm I.1:ℂ)^(-s)*
    arithmeticResidueSum 0 (u.val*lambda^(n+2))*hg

def ramifiedCubeExponent : ℕ ≃ {n:ℕ // 3∣n+2} :=
  Equiv.ofBijective (fun k=>⟨3*k+1,by use k+1;omega⟩) ⟨by
    intro a b h
    have hh:=congrArg Subtype.val h
    dsimp at hh
    omega,by
    rintro ⟨n,k,hk⟩
    refine ⟨k-1,Subtype.ext ?_⟩
    dsimp
    omega⟩

lemma zero_ramified_geometric (s : ℂ) (hs : 1<s.re) :
    (∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
      (if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0))=((3:ℂ)^(3*s-3)-1)⁻¹ := by
  let F : ℕ→ℂ := fun n=>((3^(n+2):ℕ):ℂ)^(-s)*
    (if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0)
  have hsup:Function.support F⊆{n:ℕ|3∣n+2} := by
    intro n hn
    by_contra h
    change ¬3∣n+2 at h
    exact hn (by simp [F,h])
  change (∑'n,F n)=_
  rw [←tsum_subtype_eq_of_support_subset hsup]
  change (∑'n : {n:ℕ // 3∣n+2},F n.val)=_
  rw [←ramifiedCubeExponent.tsum_eq]
  have he (k:ℕ) : F (ramifiedCubeExponent k).val=ramifiedRatio s^(k+1) := by
    change ((3^(3*k+1+2):ℕ):ℂ)^(-s)*(if 3∣3*k+1+2 then ((3^(3*k+1+2):ℕ):ℂ) else 0)=_
    rw [ite_eq_left (by use k+1;omega),show 3*k+1+2=3*(k+1) by omega]
    simpa using cube_norm_weight_algebra s k 1 (by decide)
  simp_rw [he]
  exact ramified_geometric_sum s hs

lemma zero_ramified_factor (s : ℂ) (hs : 1<s.re) :
    (∑'u:Eisˣ,∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
      arithmeticResidueSum 0 (u.val*lambda^(n+2)))=
      2*((3:ℂ)^(3*s-3)-1)⁻¹ := by
  have hne : (1:Eisˣ)≠ -1 := by
    intro h
    have hh:=congrArg Units.val h
    norm_num at hh
  rw [tsum_eq_sum (s:={1,-1}) (fun u hu=>by
    have hn : ¬(u=1 ∨ u= -1):=by simpa using hu
    simp [arithmeticResidueSum_zero_ramified,hn])]
  simp only [Finset.sum_insert,Finset.mem_singleton,hne,not_false_eq_true,Finset.sum_singleton]
  simp only [arithmeticResidueSum_zero_ramified,true_or,or_true,ite_true]
  rw [zero_ramified_geometric s hs]
  ring

theorem arithmeticDirichletSeries_zero_unramified (s : ℂ) (hs : 2<s.re) :
    arithmeticDirichletSeries s 0=
      (2*((3:ℂ)^(3*s-3)-1)⁻¹)*unramifiedCubicGaussSeries s 0 := by
  rw [arithmeticDirichletSeries_zero_separate s hs,zero_ramified_factor s (by linarith)]

end CubicEisenstein

end

end OAI
