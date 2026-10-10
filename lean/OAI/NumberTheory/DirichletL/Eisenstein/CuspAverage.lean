import OAI.NumberTheory.DirichletL.Eisenstein.RationalTranslations

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
open scoped BigOperators Classical Topology

lemma ramified_denominator_ne_zero (s : ℂ) (hs : 1<s.re) :
    (3:ℂ)^(3*s-3)-1≠0 := by
  intro he
  have hpow : (3:ℂ)^(3*s-3)=1 := sub_eq_zero.mp he
  have hnorm : 1<‖(3:ℂ)^(3*s-3)‖ := by
    rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    apply Real.one_lt_rpow (by norm_num)
    norm_num
    linarith
  rw [hpow,norm_one] at hnorm
  exact lt_irrefl _ hnorm

theorem unramifiedCubicGaussSeries_zero (s : ℂ) (hs : 2<s.re) :
    unramifiedCubicGaussSeries s 0=unramifiedTotientSeries (3*s-2) := by
  have he:=arithmeticDirichletSeries_zero_unramified s hs
  rw [arithmeticDirichletSeries_zero_totient s (by linarith)] at he
  exact (mul_left_cancel₀ (mul_ne_zero (by norm_num) (inv_ne_zero (ramified_denominator_ne_zero s (by linarith)))) he).symm

lemma cuspWhittakerHeightFactor_zero (s : ℂ) (hs : 1<s.re) :
    cuspWhittakerHeightFactor s 0=((Real.pi:ℂ)/(s-1))*cuspScatterHeightFactor s := by
  have hs0 : s≠0 := by intro he;subst s;norm_num at hs
  unfold cuspWhittakerHeightFactor
  simp only [cuspFrequency,map_zero,zero_div,zero_mul,sourceFourierKernel_zero s hs]
  rw [integral_mul_const,cuspScatterHeightFactor_integral s hs0]
  ring

lemma opposite_zero_initial_cross (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s=
      ((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s := by
  have hb : kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s=cuspConstantAverage s := by
    apply (kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num)
      s (by linarith) (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi)).trans
    exact hyperbolicEisenstein_cusp_average_eq s (by linarith)
  have ht:=translatedCuspFamily_opposite_initial 0 s hs hi
  simp only [mul_zero] at ht
  rw [ht,cuspWhittakerHeightFactor_zero s (by linarith),baseOutgoingConstant,hb,
    cuspConstantAverage,scatteringCoefficient,arithmeticDirichletSeries_zero_unramified s (by linarith)]
  have hs1 : s-1≠0 := by intro he;have hsx : s=1:=sub_eq_zero.mp he;subst s;norm_num at hs
  have halg (D V A P H U : ℂ) (hD:D≠0) (hV:V≠0) :
      2*(U*(P*H))=D*(V*(A+P*((2*D⁻¹)*U/V)*H)-V*A) := by
    field_simp
    ; ring
  exact halg _ _ _ _ _ _ (ramified_denominator_ne_zero s (by linarith)) cusp_volume_ne_zero

lemma opposite_zero_cross_identity :
    Set.EqOn (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s)
      (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s)
      {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s) domain := by
    intro s hs
    exact analyticAt_const.mul (translatedCuspFamily_analyticAt_nonreal 0 oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
  have hright : AnalyticOnNhd ℂ
      (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s) domain := by
    intro s hs
    have hp : AnalyticAt ℂ (fun z:ℂ=>(3:ℂ)^(3*z-3)-1) s := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      exact Eventually.of_forall fun z=>
        ((((differentiableAt_const (3:ℂ)).mul differentiableAt_id).sub_const 3).const_cpow
          (Or.inl (by norm_num))).sub_const 1
    exact hp.mul (baseOutgoingConstant_analyticAt s hs.1 hs.2)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact opposite_zero_initial_cross s hs.1 hs.2
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

theorem translatedCuspFourier_opposite_zero_residue :
    translatedCuspFourier 0 oppositeSource cubicEisensteinResidue=cuspConstantAverageResidue := by
  have hd : Tendsto (fun s:ℂ=>(3:ℂ)^(3*s-3)-1) (𝓝[≠] (4/3:ℂ)) (𝓝 (2:ℂ)) := by
    have hc : Continuous (fun s:ℂ=>(3:ℂ)^(3*s-3)-1) :=
      (((continuous_const.mul continuous_id).sub continuous_const).const_cpow
        (Or.inl (by norm_num))).sub continuous_const
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  have hl := ((translatedCuspFamily_residue_limit 0 oppositeSource 2 3
    (by norm_num) (by norm_num)).const_mul 2).comp upperVertical_tendsto_cubic_punctured
  have hr := (hd.mul baseOutgoingConstant_residue_limit).comp upperVertical_tendsto_cubic_punctured
  have hevent : (fun t:ℝ=>2*((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I)))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((3:ℂ)^(3*((4/3:ℂ)+(t:ℂ)*Complex.I)-3)-1)*
        ((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*baseOutgoingConstant ((4/3:ℂ)+(t:ℂ)*Complex.I))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=opposite_zero_cross_identity (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : 2*translatedCuspFourier 0 oppositeSource cubicEisensteinResidue=2*cuspConstantAverageResidue :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hevent
  exact mul_left_cancel₀ (by norm_num : (2:ℂ)≠0) heq

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rationalComplex_conjugate (r:SL(2,ℤ)) (M:levelThree) :
    complexMatrix (levelThreeConjugate (rationalEmbedding r) M)*rationalComplex r=
      rationalComplex r*complexMatrix M := by
  rw [←integralComplexMatrix_levelThree,←integralComplexMatrix_levelThree]
  change integralComplexMatrix ((rationalEmbedding r)*(M:SL(2,Eis))*(rationalEmbedding r)⁻¹)*
    integralComplexMatrix (rationalEmbedding r)=
      integralComplexMatrix (rationalEmbedding r)*integralComplexMatrix (M:SL(2,Eis))
  rw [←map_mul,inv_mul_cancel_right,map_mul]

lemma hyperbolicEisenstein_rational_automorphy (r:SL(2,ℤ)) (M:levelThree)
    (s:ℂ) (hs:2<s.re) (w:HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex r • (complexMatrix M • w))=
      complexCharacter M*hyperbolicEisenstein s (rationalComplex r • w) := by
  rw [←mul_smul,←rationalComplex_conjugate,mul_smul,hyperbolicEisenstein_automorphy _ _ hs,
    complexCharacter_conjugate_rational]

lemma hyperbolicEisenstein_rational_periodic (r:SL(2,ℤ)) (a:Eis)
    (s:ℂ) (hs:2<s.re) (z:ℂ) (v:ℝ) (hv:0<v) :
    hyperbolicEisenstein s (rationalComplex r • upperPoint (z+3*eisEmbedding a) v hv)=
      hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv) := by
  have he : upperPoint (z+3*eisEmbedding a) v hv=complexMatrix (upperTranslation a) • upperPoint z v hv :=
    congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace)) (upperTranslation_section a z v hv).symm
  rw [he,hyperbolicEisenstein_rational_automorphy r _ s hs,complexCharacter_upperTranslation,one_mul]

lemma rationalComplex_unipotent_coe (t : ℤ) :
    (rationalComplex (rationalUnipotent t) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1,(t : ℂ);0,1] := by
  apply Matrix.ext
  intro i j
  change eisEmbedding ((Int.castRingHom Eis) ((!![1,t;0,1] : Matrix (Fin 2) (Fin 2) ℤ) i j)) = _
  fin_cases i <;> fin_cases j <;> simp

lemma rationalUnipotent_section (t:ℤ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex (rationalUnipotent t)*upperSection z v hv=upperSection (z+t) v hv := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, rationalComplex_unipotent_coe]
  change (!![1,(t : ℂ);0,1] *
    !![(Real.sqrt v : ℂ),z/(Real.sqrt v : ℂ);0,(Real.sqrt v : ℂ)⁻¹] :
      Matrix (Fin 2) (Fin 2) ℂ) =
    !![(Real.sqrt v : ℂ),(z+t)/(Real.sqrt v : ℂ);0,(Real.sqrt v : ℂ)⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring

lemma rationalComplex_T_pow_upper (n:ℕ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex (ModularGroup.T^n) • upperPoint z v hv=upperPoint (z+n) v hv := by
  change ((rationalComplex (ModularGroup.T^n)*upperSection z v hv):HyperbolicSpace)=
    (upperSection (z+(n:ℂ)) v hv:HyperbolicSpace)
  have he:=congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace)) (rationalUnipotent_section (n:ℤ) z v hv)
  simpa only [rationalUnipotent_nat,Int.cast_natCast] using he

theorem rational_cusp_average_right_T (r:SL(2,ℤ)) (n:ℕ) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)∂hyperbolicVolume)=
    ∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex r • w)∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (rationalComplex r • w)
  have hf : Continuous f := (hyperbolicEisenstein_continuous s hs).comp (continuous_hyperbolic_action _)
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).comp (continuous_hyperbolic_action _)
  change (∫w in cuspPeriodStrip 5 6,f w∂hyperbolicVolume)=∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates f hf.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable f hf),
    cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  dsimp only
  apply congrArg (fun q:ℂ=>q/(v:ℂ)^3)
  simp_rw [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper]
  have hh:=period_integral_translation
    (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0))
    (fun a z=>hyperbolicEisenstein_rational_periodic r a s hs z v hv0) (n:ℂ)
  simpa only [add_comm] using hh

lemma cuspFourierPhase_zero (w:HyperbolicSpace) : cuspFourierPhase (0:Eis) w=1 := by
  simp [cuspFourierPhase,cuspFrequency]

lemma kernelCuspFourier_zero (F:KernelQuotientL2) :
    kernelCuspFourier (0:Eis) F=kernelCuspStripAverage F := by
  rw [kernelCuspFourier_integral,kernelCuspStripAverage_hyperbolic]
  simp only [cuspFourierPhase_zero,mul_one]

theorem translatedCuspFourier_residue_eq_of_initial (M N:levelTwo)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix M • w)∂hyperbolicVolume)=
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix N • w)∂hyperbolicVolume) :
    translatedCuspFourier 0 M cubicEisensteinResidue=
      translatedCuspFourier 0 N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedCuspFamily 0 M 2 3 (by norm_num) (by norm_num)
  let g : ℂ→ℂ := translatedCuspFamily 0 N 2 3 (by norm_num) (by norm_num)
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal 0 M 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal 0 N 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedCuspFamily_initial 0 M 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      translatedCuspFamily_initial 0 N 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2]
    simp only [cuspFourierPhase_zero,mul_one]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedCuspFamily_residue_limit 0 M 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  have hr := (translatedCuspFamily_residue_limit 0 N 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  exact congrArg (fun z:ℂ=>((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*z) hv

end

open CubicKubota

lemma sourceComplexMatrix_rationalLift (r:SL(2,ℤ)) :
    sourceComplexMatrix (rationalLift r)=rationalComplex r := rfl

lemma translatedCuspFourier_one_residue :
    translatedCuspFourier 0 1 cubicEisensteinResidue=cuspConstantAverageResidue := by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one,
    kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average]

lemma translatedCuspFourier_bruhat_residue (i:RationalBruhatIndex) :
    translatedCuspFourier 0 (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue=
      cuspConstantAverageResidue := by
  rcases i with ⟨e,a|⟨a,b⟩⟩
  · calc
      _=translatedCuspFourier 0 1 cubicEisensteinResidue := by
        apply translatedCuspFourier_residue_eq_of_initial
        intro s hs hi
        simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
        simp only [map_one,one_smul]
      _=cuspConstantAverageResidue := translatedCuspFourier_one_residue
  · calc
      _=translatedCuspFourier 0 oppositeSource cubicEisensteinResidue := by
        apply translatedCuspFourier_residue_eq_of_initial
        intro s hs hi
        simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
        change (∫w in cuspPeriodStrip 5 6,
          hyperbolicEisenstein s (rationalComplex ModularGroup.S •
            (rationalComplex (ModularGroup.T^b.val) • w))∂hyperbolicVolume)=
          ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)∂hyperbolicVolume
        simpa only [map_mul,mul_smul] using
          rational_cusp_average_right_T ModularGroup.S b.val s (by linarith)
      _=cuspConstantAverageResidue := translatedCuspFourier_opposite_zero_residue

theorem kernelSourceProjection_residue_cusp_average :
    kernelCuspStripAverage (kernelSourceProjection cubicEisensteinResidue)=
      cuspConstantAverageResidue := by
  rw [←kernelCuspFourier_zero,kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  have he (i:RationalBruhatIndex) :
      kernelCuspFourier 0 (kernelSourcePullback (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=
        cuspConstantAverageResidue := translatedCuspFourier_bruhat_residue i
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_sum,
    Fintype.card_fin,smul_eq_mul,nsmul_eq_mul]
  norm_num
  ring

theorem kernelSourceProjection_cubicEisensteinResidue_ne_zero :
    kernelSourceProjection cubicEisensteinResidue≠0 := by
  intro hz
  have hh:=kernelSourceProjection_residue_cusp_average
  rw [hz,map_zero] at hh
  exact cuspConstantAverageResidue_ne_zero hh.symm

theorem cubicSourceResidualFunction_cusp_average :
    (∫w in cuspPeriodStrip 5 6,cubicSourceResidualFunction w∂hyperbolicVolume)=
      cuspConstantAverageResidue := by
  rw [←kernelSourceProjection_residue_cusp_average,kernelCuspStripAverage_hyperbolic]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae cubicSourceResidualFunction_represents_projection] with w hw
  exact hw.symm

theorem cubicSourceResidualFunction_ne_zero : cubicSourceResidualFunction≠0 := by
  intro hz
  have he:=cubicSourceResidualFunction_cusp_average
  rw [hz] at he
  simp only [Pi.zero_apply,integral_zero] at he
  exact cuspConstantAverageResidue_ne_zero he.symm

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

lemma complex_gaussian_power_integrable (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0<r) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2))
      (Set.Ioi 0) volume := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have hbase : MellinConvergent (fun t : ℝ => Complex.exp (-(t:ℂ))) (s/2) := by
    simpa only [MellinConvergent,smul_eq_mul,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm]
      using Complex.GammaIntegral_convergent hs2
  have hlinear := (MellinConvergent.comp_mul_left
    (f := fun t : ℝ => Complex.exp (-(t:ℂ))) (s := s/2) hr).mpr hbase
  have hgaussian := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) (s := s) (a := 2)
      (by norm_num)).mpr hlinear
  simpa only [MellinConvergent,smul_eq_mul,Real.rpow_two,
    Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using hgaussian

lemma complex_gaussian_power_integral (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0<r) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2)) =
      (1/2:ℂ)*((1/(r:ℂ))^(s/2)*Complex.Gamma (s/2)) := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have he := mellin_comp_rpow (fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) s 2
  simp only [mellin,smul_eq_mul,Real.rpow_two,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.real_smul] at he
  norm_num only [Complex.ofReal_ofNat] at he
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs2 hr] at he
  simpa [neg_mul] using he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def cubicMellinMixture (s : ℂ) (t x : ℝ) : ℂ :=
  (t:ℂ)^(-(2:ℂ)/3)*Complex.exp (-(t:ℂ))*
    ((x:ℂ)^((s-1/3)-1)*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2))

lemma cubicMellinMixture_slice_integrable (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    IntegrableOn (cubicMellinMixture s t) (Set.Ioi 0) volume := by
  apply (complex_gaussian_power_integrable (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)).const_mul

lemma cubicMellinMixture_integral_x (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
  simp only [cubicMellinMixture,integral_const_mul]
  rw [complex_gaussian_power_integral (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)]
  have hb : (1/(((1/(4*t):ℝ):ℂ)))=(4:ℂ)*(t:ℂ) := by
    push_cast
    field_simp
  have hm : ((4:ℂ)*(t:ℂ))^((s-1/3)/2)=
      (4:ℂ)^((s-1/3)/2)*(t:ℂ)^((s-1/3)/2) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : 0≤(4:ℝ)) ht.le ((s-1/3)/2)
  rw [hb,hm]
  have hp : (t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2)=
      (t:ℂ)^((s+1/3)/2-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  calc
    _ = ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        (((t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2))*Complex.exp (-(t:ℂ))) := by ring
    _ = _ := by rw [hp]

lemma cubicMellinMixture_norm (s : ℂ) (t x : ℝ) (ht : 0<t) (hx : 0<x) :
    ‖cubicMellinMixture s t x‖ =
      (t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
  have he : -((1/(4*t):ℝ):ℂ)*(x:ℂ)^2=(-(1/(4*t))*x^2:ℝ) := by
    push_cast
    rfl
  simp only [cubicMellinMixture,norm_mul,he,
    Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp,Complex.ofReal_re,Complex.neg_re]
  norm_num

lemma real_gaussian_power_integral (sigma r : ℝ) (hs : 0<sigma) (hr : 0<r) :
    (∫x : ℝ in Set.Ioi 0,x^(sigma-1)*Real.exp (-r*x^2)) =
      r^(-sigma/2)*(1/2)*Real.Gamma (sigma/2) := by
  simpa only [Real.rpow_two,sub_add_cancel] using
    (_root_.integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=sigma-1) (b:=r)
      (by norm_num) (by linarith) hr)

lemma cubicMellinMixture_integral_norm (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,‖cubicMellinMixture s t x‖) =
      ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
        (t^((s.re+1/3)/2-1)*Real.exp (-t)) := by
  calc
    _ = ∫x : ℝ in Set.Ioi 0,(t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact cubicMellinMixture_norm s t x ht hx
    _ = _ := by
      rw [integral_const_mul,real_gaussian_power_integral (s.re-1/3) (1/(4*t))
        (by linarith) (by positivity)]
      have hpow : (1/(4*t):ℝ)^(-(s.re-1/3)/2)=(4:ℝ)^((s.re-1/3)/2)*t^((s.re-1/3)/2) := by
        rw [show -(s.re-1/3)/2=-((s.re-1/3)/2) by ring,
          Real.rpow_neg_eq_inv_rpow,one_div,inv_inv,
          Real.mul_rpow (by norm_num : 0≤(4:ℝ)) ht.le]
      rw [hpow]
      have hp : t^(-(2:ℝ)/3)*t^((s.re-1/3)/2)=t^((s.re+1/3)/2-1) := by
        rw [←Real.rpow_add ht]
        congr 1
        ring
      calc
        _ = ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
            ((t^(-(2:ℝ)/3)*t^((s.re-1/3)/2))*Real.exp (-t)) := by ring
        _ = _ := by rw [hp]

lemma cubicMellinMixture_integrable (s : ℂ) (hs : 1/3<s.re) :
    Integrable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    unfold cubicMellinMixture
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicMellinMixture_slice_integrable s hs t ht
  · have hg := (Real.GammaIntegral_convergent
        (show 0<(s.re+1/3)/2 by linarith)).const_mul
        ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))
    apply hg.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [cubicMellinMixture_integral_norm s hs t ht]
    ring

lemma cubicMellinMixture_integral_t (s : ℂ) (x : ℝ) :
    (∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      (x:ℂ)^((s-1/3)-1)*schlafliIntegral (1/3) x := by
  rw [schlafliIntegral,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have he : Complex.exp (-(t:ℂ))*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2)=
      Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t)) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [show (1/3:ℂ)-1=-(2:ℂ)/3 by ring]
  unfold cubicMellinMixture
  linear_combination (t:ℂ)^(-(2:ℂ)/3)*(x:ℂ)^((s-1/3)-1)*he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma schlafliBesselK_cubic_mellin_mixture (s : ℂ) (x : ℝ) (hx : 0<x) :
    (x:ℂ)^(s-1)*schlafliBesselK (1/3) x =
      ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*(∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
  rw [schlafliBesselK,cubicMellinMixture_integral_t]
  have hdiv : (x/2:ℂ)^(-(1/3:ℂ))=(x:ℂ)^(-(1/3:ℂ))/(2:ℂ)^(-(1/3:ℂ)) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.div_cpow_ofReal_nonneg hx.le (by norm_num : 0≤(2:ℝ)) (-(1/3:ℂ))
  rw [hdiv,Complex.cpow_neg (2:ℂ) (1/3),div_inv_eq_mul]
  have hp : (x:ℂ)^(s-1)*(x:ℂ)^(-(1/3:ℂ))=(x:ℂ)^((s-1/3)-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 1
    ring
  linear_combination (1/2:ℂ)*(2:ℂ)^(1/3:ℂ)*schlafliIntegral (1/3) x*hp

lemma schlafliBesselK_cubic_mellin_integrable (s : ℂ) (hs : 1/3<s.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*schlafliBesselK (1/3) x)
      (Set.Ioi 0) volume := by
  apply ((cubicMellinMixture_integrable s hs).integral_prod_right.const_mul
    ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (schlafliBesselK_cubic_mellin_mixture s x hx).symm

lemma cubicMellinMixture_double_integral (s : ℂ) (hs : 1/3<s.re) :
    (∫t : ℝ in Set.Ioi 0,∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        Complex.Gamma ((s+1/3)/2) := by
  have hB : 0<((s+1/3)/2).re := by norm_num; linarith
  calc
    _ = ∫t : ℝ in Set.Ioi 0,
        ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact cubicMellinMixture_integral_x s hs t ht
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [Complex.GammaIntegral,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm] using
        (Complex.Gamma_eq_integral hB).symm

theorem schlafliBesselK_cubic_mellin (s : ℂ) (hs : 1/3<s.re) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*schlafliBesselK (1/3) x) =
      (2:ℂ)^(s-2)*Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by
  have hmix : Integrable (Function.uncurry (cubicMellinMixture s))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    convert cubicMellinMixture_integrable s hs using 1
    funext p
    rcases p with ⟨t,x⟩
    rfl
  have hswap := (integral_integral_swap hmix).symm
  have h4 : (4:ℂ)^((s-1/3)/2)=(2:ℂ)^(2*((s-1/3)/2)) := by
    have hh := (Complex.natCast_cpow_natCast_mul 2 2 ((s-1/3)/2)).symm
    norm_num at hh
    exact hh
  have hprod : (2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)=(2:ℂ)^s := by
    rw [h4,←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  have hscale : (1/4:ℂ)*(2:ℂ)^s=(2:ℂ)^(s-2) := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2:ℂ)≠0)]
    norm_num
    ring
  calc
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (∫x : ℝ in Set.Ioi 0,∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact schlafliBesselK_cubic_mellin_mixture s x hx
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          Complex.Gamma ((s+1/3)/2)) := by
      rw [hswap,cubicMellinMixture_double_integral s hs]
    _ = ((1/4:ℂ)*((2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)))*
        Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by ring
    _ = _ := by rw [hprod,hscale]

end CubicEisenstein

end

end OAI
