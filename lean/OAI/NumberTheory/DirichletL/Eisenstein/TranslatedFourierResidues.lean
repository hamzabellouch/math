import OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage

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
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma period_integral_fourier_translation (f:ℂ→ℂ)
    (hp:∀(n:Eis)(z:ℂ),f (z+3*eisEmbedding n)=f z) (h:Eis) (b:ℂ) :
    (∫z in periodDomain,f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ShortDraftTrace.breveE (cuspFrequency h*b)*
        ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  let g : ℂ→ℂ := fun z=>f z*ShortDraftTrace.breveE (-cuspFrequency h*z)
  have hg : ∀(n:Eis)(z:ℂ),g (z+3*eisEmbedding n)=g z := by
    intro n z
    dsimp only [g]
    rw [hp,cuspFrequency_negative_period]
  have he (z:ℂ) : f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z)=
      ShortDraftTrace.breveE (cuspFrequency h*b)*g (b+z) := by
    dsimp only [g]
    rw [mul_left_comm,←AddChar.map_add_eq_mul]
    congr 1
    · rw [add_comm]
    · congr 1
      ring
  simp_rw [he]
  rw [integral_const_mul,period_integral_translation g hg b]

theorem rational_cusp_fourier_right_T (r:SL(2,ℤ)) (n:ℕ) (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)*
        cuspFourierPhase h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*
        ∫w in cuspPeriodStrip 5 6,
          hyperbolicEisenstein s (rationalComplex r • w)*cuspFourierPhase h w∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex (r*ModularGroup.T^n) • w)*cuspFourierPhase h w
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex r • w)*cuspFourierPhase h w
  have hf : Continuous f := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  change (∫w in cuspPeriodStrip 5 6,f w∂hyperbolicVolume)=
    ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates f hf.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable f hf),
    cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg),
    ←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  dsimp only
  simp_rw [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper,
    cuspFourierPhase,hyperbolicHorizontal_upperPoint]
  rw [period_integral_fourier_translation
    (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0))
    (fun a z=>hyperbolicEisenstein_rational_periodic r a s hs z v hv0) h (n:ℂ)]
  ring

lemma translatedCuspFourier_residue_scaled_of_initial (h:Eis) (M N:levelTwo) (c:ℂ)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspFourierPhase h w∂hyperbolicVolume)=
      c*∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix N • w)*cuspFourierPhase h w∂hyperbolicVolume) :
    translatedCuspFourier h M cubicEisensteinResidue=
      c*translatedCuspFourier h N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedCuspFamily h M 2 3 (by norm_num) (by norm_num)
  let g : ℂ→ℂ := fun s=>c*translatedCuspFamily h N 2 3 (by norm_num) (by norm_num) s
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal h M 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>analyticAt_const.mul
    (translatedCuspFamily_analyticAt_nonreal h N 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedCuspFamily_initial h M 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      translatedCuspFamily_initial h N 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedCuspFamily_residue_limit h M 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  have hr := ((translatedCuspFamily_residue_limit h N 2 3 (by norm_num) (by norm_num)).const_mul c).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  dsimp only [f,g] at hv
  dsimp only [Function.comp_def]
  linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hv

lemma translatedCuspFourier_one (h:Eis) (F:KernelQuotientL2) :
    translatedCuspFourier h 1 F=kernelCuspFourier h F := by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one]

lemma translatedCuspFourier_bruhat (h:Eis) (e:Fin 2) (a:Fin 3⊕(Fin 3×Fin 3)) :
    translatedCuspFourier h (rationalLift (rationalBruhatRep (e,a))) cubicEisensteinResidue=
      match a with
      | Sum.inl _=>kernelCuspFourier h cubicEisensteinResidue
      | Sum.inr ab=>ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
        translatedCuspFourier h oppositeSource cubicEisensteinResidue := by
  cases a with
  | inl a =>
    rw [←one_mul (kernelCuspFourier h cubicEisensteinResidue),←translatedCuspFourier_one h]
    apply translatedCuspFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    simp only [map_one,one_smul,one_mul]
  | inr ab =>
    apply translatedCuspFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    change (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex ModularGroup.S •
        (rationalComplex (ModularGroup.T^ab.2.val) • w))*cuspFourierPhase h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)*
        cuspFourierPhase h w∂hyperbolicVolume
    simpa only [map_mul,mul_smul] using
      rational_cusp_fourier_right_T ModularGroup.S ab.2.val h s (by linarith)

def sourceRayPhaseSum (h:Eis) : ℂ :=
  ∑ b:Fin 3,ShortDraftTrace.breveE (cuspFrequency h*(b.val:ℂ))

theorem kernelSourceProjection_residue_fourier (h:Eis) :
    kernelCuspFourier h (kernelSourceProjection cubicEisensteinResidue)=
      (4:ℂ)⁻¹*(kernelCuspFourier h cubicEisensteinResidue+
        sourceRayPhaseSum h*translatedCuspFourier h oppositeSource cubicEisensteinResidue) := by
  rw [kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  change (24:ℂ)⁻¹*(∑i:RationalBruhatIndex,
    translatedCuspFourier h (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=_
  rw [Fintype.sum_prod_type]
  simp_rw [translatedCuspFourier_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  rw [←Finset.sum_mul]
  change (24:ℂ)⁻¹*((2:ℂ)*(3*kernelCuspFourier h cubicEisensteinResidue+
    3*(sourceRayPhaseSum h*translatedCuspFourier h oppositeSource cubicEisensteinResidue)))=_
  ring

end

section
open CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_cube (h:Eis) :
    ShortDraftTrace.breveE (cuspFrequency h)^3=1 := by
  rw [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  have hp:=cuspFrequency_period h (1:Eis)
  simpa only [map_one,mul_one,one_mul,Nat.cast_ofNat,mul_comm] using hp

lemma sourceRayPhaseSum_formula (h:Eis) :
    sourceRayPhaseSum h=1+ShortDraftTrace.breveE (cuspFrequency h)+
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
  unfold sourceRayPhaseSum
  simp only [Fin.sum_univ_succ,Fin.val_zero,Nat.cast_zero,mul_zero,AddChar.map_zero_eq_one,
    Fin.val_succ,Nat.cast_add,Nat.cast_one,zero_add,mul_one,Fin.sum_univ_zero,add_zero]
  have he : ShortDraftTrace.breveE (cuspFrequency h*(1+1))=
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
    rw [mul_add,mul_one,AddChar.map_add_eq_mul,pow_two]
  rw [he]
  ring

lemma sourceRayPhaseSum_eq (h:Eis) :
    sourceRayPhaseSum h=if ShortDraftTrace.breveE (cuspFrequency h)=1 then 3 else 0 := by
  rw [sourceRayPhaseSum_formula]
  split_ifs with he
  · rw [he]
    norm_num
  · have hc:=sourceRayPhase_cube h
    have hz : (ShortDraftTrace.breveE (cuspFrequency h)-1)*
        (1+ShortDraftTrace.breveE (cuspFrequency h)+ShortDraftTrace.breveE (cuspFrequency h)^2)=0 := by
      linear_combination hc
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr he)

lemma kernelCuspFourier_residue_horizontal (h:Eis) :
    kernelCuspFourier h cubicEisensteinResidue=
      ShortDraftTrace.breveE (cuspFrequency h)*kernelCuspFourier h cubicEisensteinResidue := by
  have hh:=translatedCuspFourier_residue_scaled_of_initial h 1 1
    (ShortDraftTrace.breveE (cuspFrequency h)) (by
      intro s hs hi
      have he:=rational_cusp_fourier_right_T (1:SL(2,ℤ)) 1 h s (by linarith)
      have hT (w:HyperbolicSpace) : hyperbolicEisenstein s (rationalComplex ModularGroup.T • w)=hyperbolicEisenstein s w := by
        simpa only [pow_one] using hyperbolicEisenstein_T_pow s 1 w
      simpa only [one_mul,pow_one,map_one,one_smul,Nat.cast_one,mul_one,hT] using he)
  simpa only [translatedCuspFourier_one] using hh

lemma kernelCuspFourier_residue_eq_zero_of_not_horizontal (h:Eis)
    (hh:ShortDraftTrace.breveE (cuspFrequency h)≠1) :
    kernelCuspFourier h cubicEisensteinResidue=0 := by
  have he:=kernelCuspFourier_residue_horizontal h
  have hz : (ShortDraftTrace.breveE (cuspFrequency h)-1)*
      kernelCuspFourier h cubicEisensteinResidue=0 := by linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hh)

theorem kernelSourceProjection_residue_fourier_mask (h:Eis) :
    kernelCuspFourier h (kernelSourceProjection cubicEisensteinResidue)=
      if ShortDraftTrace.breveE (cuspFrequency h)=1 then
        (4:ℂ)⁻¹*(kernelCuspFourier h cubicEisensteinResidue+
          3*translatedCuspFourier h oppositeSource cubicEisensteinResidue)
      else 0 := by
  rw [kernelSourceProjection_residue_fourier,sourceRayPhaseSum_eq]
  split_ifs with hh
  · rfl
  · rw [kernelCuspFourier_residue_eq_zero_of_not_horizontal h hh]
    ring

end

open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma oppositeFrequency_cross_identity (h:Eis) :
    Set.EqOn (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s (3*(9*h)))
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) {s:ℂ|1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s (3*(9*h))) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt (3*(9*h)) s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
      cuspWhittakerHeightFactor s (3*(9*h)))=ᶠ[𝓝 (5+Complex.I:ℂ)]
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num)
      (by norm_num) s hs.1 hs.2,opposite_cusp_fourier_average s (by linarith [hs.1]),
      translatedCuspFamily_opposite_initial (9*h) s hs.1 hs.2]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev

theorem translatedCuspFourier_unramified_residue (h:Eis) :
    translatedCuspFourier h oppositeSource cubicEisensteinResidue=
      unramifiedGaussResidue (9*h)*cuspWhittakerHeightFactor (4/3:ℂ) h := by
  have hh (k:Eis) : Tendsto (fun s:ℂ=>cuspWhittakerHeightFactor s k)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) k)) :=
    (cuspWhittakerHeightFactor_analyticAt k (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hl := ((translatedCuspFamily_residue_limit h oppositeSource 2 3
    (by norm_num) (by norm_num)).mul (hh (3*(9*h)))).comp upperVertical_tendsto_cubic_punctured
  have hr := ((translatedCuspFamily_residue_limit (3*(9*h)) oppositeSource 2 3
    (by norm_num) (by norm_num)).mul (hh h)).comp upperVertical_tendsto_cubic_punctured
  have hev : (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) (3*(9*h)))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=oppositeFrequency_cross_identity h (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : translatedCuspFourier h oppositeSource cubicEisensteinResidue*
      cuspWhittakerHeightFactor (4/3:ℂ) (3*(9*h))=
      translatedCuspFourier (3*(9*h)) oppositeSource cubicEisensteinResidue*
        cuspWhittakerHeightFactor (4/3:ℂ) h := tendsto_nhds_unique_of_eventuallyEq hl hr hev
  unfold unramifiedGaussResidue
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff (cuspWhittakerHeightFactor_center_ne_zero (3*(9*h)))).mpr heq

def principalArithmeticResidue (h:Eis) : ℂ :=
  if h=0 then constantArithmeticResidue else nonzeroScatteringResidue h

lemma kernelCuspFourier_principal_residue (h:Eis) :
    kernelCuspFourier h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*principalArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  by_cases hh:h=0
  · subst h
    rw [kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average,principalArithmeticResidue,ite_eq_left rfl,
      cuspWhittakerHeightFactor_zero (4/3) (by norm_num),cuspConstantAverageResidue]
    ring
  · rw [principalArithmeticResidue,ite_eq_right hh,nonzeroScatteringResidue]
    field_simp [cusp_volume_ne_zero,cuspWhittakerHeightFactor_center_ne_zero h]

def sourceArithmeticResidue (h:Eis) : ℂ :=
  if ShortDraftTrace.breveE (cuspFrequency h)=1 then
    (4:ℂ)⁻¹*(principalArithmeticResidue h+
      3*unramifiedGaussResidue (9*h)/((9*Real.sqrt 3/2:ℝ):ℂ))
  else 0

theorem kernelSourceProjection_gauss_residue (h:Eis) :
    kernelCuspFourier h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  rw [kernelSourceProjection_residue_fourier_mask,sourceArithmeticResidue]
  split_ifs with hh
  · rw [kernelCuspFourier_principal_residue,translatedCuspFourier_unramified_residue]
    field_simp [cusp_volume_ne_zero]

  · ring

theorem cubicSourceResidualFunction_fourier_average (h:Eis) :
    (∫w in cuspPeriodStrip 5 6,cubicSourceResidualFunction w*cuspFourierPhase h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  rw [←kernelSourceProjection_gauss_residue,kernelCuspFourier_integral]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae cubicSourceResidualFunction_represents_projection] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w) hw.symm

lemma unramifiedGaussResidue_zero :
    unramifiedGaussResidue 0=((9*Real.sqrt 3/2:ℝ):ℂ)*constantArithmeticResidue := by
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero (0:Eis))
  have ht:=translatedCuspFourier_unramified_residue (0:Eis)
  simp only [mul_zero] at ht
  rw [←ht,translatedCuspFourier_opposite_zero_residue]
  have hp:=kernelCuspFourier_principal_residue (0:Eis)
  rw [kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average] at hp
  simpa [principalArithmeticResidue] using hp

lemma sourceArithmeticResidue_zero : sourceArithmeticResidue 0=constantArithmeticResidue := by
  rw [sourceArithmeticResidue]
  simp only [cuspFrequency,map_zero,zero_div,AddChar.map_zero_eq_one,
    principalArithmeticResidue,mul_zero,unramifiedGaussResidue_zero,ite_true]
  field_simp [cusp_volume_ne_zero]
  ; ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def horizontalPhaseMultiplier (freq direction : ℂ) : ℂ :=
  (2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))

lemma brevePhase_hasDerivAt (freq z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ShortDraftTrace.breveE (freq*(z+(x:ℂ)*direction)))
      (horizontalPhaseMultiplier freq direction*
        ShortDraftTrace.breveE (freq*(z+(t:ℂ)*direction))) t := by
  have hz : HasDerivAt (fun x : ℝ => freq*(z+(x:ℂ)*direction)) (freq*direction) t := by
    convert (((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const direction).const_add z).const_mul freq using 1 <;>
      simp
  have he := ((hz.add hz.star).const_mul (2*Real.pi*Complex.I)).cexp
  change HasDerivAt (fun x : ℝ => Complex.exp ((2*Real.pi*Complex.I)*
    (freq*(z+(x:ℂ)*direction)+star (freq*(z+(x:ℂ)*direction)))))
    ((2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))*
      Complex.exp ((2*Real.pi*Complex.I)*
        (freq*(z+(t:ℂ)*direction)+star (freq*(z+(t:ℂ)*direction))))) t
  simpa only [Pi.add_apply,mul_comm] using he

lemma horizontalPhaseMultiplier_norm (freq direction : ℂ) :
    ‖horizontalPhaseMultiplier freq direction‖≤4*Real.pi*‖freq‖*‖direction‖ := by
  have hc : ‖(2*Real.pi*Complex.I:ℂ)‖=2*Real.pi := by
    norm_num [norm_mul,abs_of_pos Real.pi_pos]
  unfold horizontalPhaseMultiplier
  rw [norm_mul,hc]
  calc
    _ ≤ (2*Real.pi)*(‖freq*direction‖+‖star (freq*direction)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = _ := by rw [norm_star,norm_mul];ring

lemma horizontalPhaseMultiplier_wirtinger (freq : ℂ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq 1+
      Complex.I*horizontalPhaseMultiplier freq Complex.I)=2*Real.pi*Complex.I*star freq := by
  simp only [horizontalPhaseMultiplier,mul_one,star_mul,Complex.star_def,
    Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ring

lemma norm_mul_exp_neg_bound (a r : ℝ) (ha : 0<a) :
    r*Real.exp (-a*r)≤(2/a)*Real.exp (-(a/2)*r) := by
  have hbase := Real.add_one_le_exp ((a/2)*r)
  have hr : r≤(2/a)*Real.exp ((a/2)*r) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    nlinarith
  calc
    _ ≤ ((2/a)*Real.exp ((a/2)*r))*Real.exp (-a*r) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring

lemma summable_norm_mul_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => ‖cuspFrequency h‖*Real.exp (-a*‖cuspFrequency h‖)) := by
  apply Summable.of_nonneg_of_le (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (fun h => norm_mul_exp_neg_bound a _ ha)
  exact (summable_exp_neg_cuspFrequency_norm (a/2) (half_pos ha)).mul_left (2/a)

local notation "O" => ActualEisensteinCubic.O

def cubicResidualDirectionalTerm (h : ActualEisensteinCubic.O) (v : ℝ) (z direction : ℂ) : ℂ :=
  horizontalPhaseMultiplier (cuspFrequency h) direction*cubicResidualNonzeroTerm h (v,z)

lemma cubicResidualNonzeroTerm_horizontal_hasDerivAt (h : ActualEisensteinCubic.O) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => cubicResidualNonzeroTerm h (v,z+(x:ℂ)*direction))
      (cubicResidualDirectionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (brevePhase_hasDerivAt (cuspFrequency h) z direction t).const_mul
    (cubicResidualModeAmplitude v h)
  have hf : (fun x : ℝ => cubicResidualNonzeroTerm h (v,z+(x:ℂ)*direction))=
      (fun x : ℝ => cubicResidualModeAmplitude v h*
        ShortDraftTrace.breveE (cuspFrequency h*(z+(x:ℂ)*direction))) := by
    funext x
    exact cubicResidualNonzeroTerm_eq_amplitude v hv h _
  rw [hf]
  convert hh using 1
  rw [cubicResidualDirectionalTerm,cubicResidualNonzeroTerm_eq_amplitude v hv h]
  ring

lemma cubicResidualDirectionalTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),v∈Set.Icc a b →
      ‖cubicResidualDirectionalTerm h v z direction‖≤
        C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_slab_bound a b ha hab
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hv
  rw [cubicResidualDirectionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h (v,z) hv)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma cubicResidualDirectionalTerm_summable (v : ℝ) (hv : 0<v) (z direction : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => cubicResidualDirectionalTerm h v z direction) := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualDirectionalTerm_slab_bound v v hv le_rfl direction
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h v z ⟨le_rfl,le_rfl⟩)
  exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C

lemma cubicResidualNonzeroSeries_horizontal_hasDerivAt (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => cubicResidualNonzeroSeries (v,z+(x:ℂ)*direction))
      (∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualDirectionalTerm_slab_bound v v hv le_rfl direction
  have hs := (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C
  have hz : Summable (fun h : ActualEisensteinCubic.O => cubicResidualNonzeroTerm h (v,z+(0:ℂ)*direction)) := by
    simpa only [zero_mul,add_zero] using cubicResidualNonzeroTerm_summable (v,z) hv
  exact hasDerivAt_tsum hs (fun h x => cubicResidualNonzeroTerm_horizontal_hasDerivAt h v hv z direction x)
    (fun h x => hbound h v (z+(x:ℂ)*direction) ⟨le_rfl,le_rfl⟩) hz t

lemma cubicResidualFunction_horizontal_hasDerivAt (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => cubicResidualFunction (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (cubicResidualNonzeroSeries_horizontal_hasDerivAt v hv z direction t).const_add
    ((3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ))
  simpa only [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint] using hh

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def horizontalWirtingerBar (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ => f (z+(t:ℂ))) 0+
    Complex.I*deriv (fun t : ℝ => f (z+(t:ℂ)*Complex.I)) 0)

lemma horizontalWirtingerBar_brevePhase (freq z : ℂ) :
    horizontalWirtingerBar (fun w => ShortDraftTrace.breveE (freq*w)) z=
      (2*Real.pi*Complex.I*star freq)*ShortDraftTrace.breveE (freq*z) := by
  have h1 := (brevePhase_hasDerivAt freq z 1 0).deriv
  have hI := (brevePhase_hasDerivAt freq z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI]
  linear_combination ShortDraftTrace.breveE (freq*z)*horizontalPhaseMultiplier_wirtinger freq

theorem cubicResidualFunction_wirtingerBar (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (fun w => cubicResidualFunction (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*star (cuspFrequency h))*cubicResidualNonzeroTerm h (v,z) := by
  have h1 := (cubicResidualFunction_horizontal_hasDerivAt v hv z 1 0).deriv
  have hI := (cubicResidualFunction_horizontal_hasDerivAt v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI]
  have hs1 := cubicResidualDirectionalTerm_summable v hv z 1
  have hsI := (cubicResidualDirectionalTerm_summable v hv z Complex.I).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_add hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold cubicResidualDirectionalTerm
  linear_combination cubicResidualNonzeroTerm h (v,z)*horizontalPhaseMultiplier_wirtinger (cuspFrequency h)

lemma cubicResidualFunction_wirtingerBar_summable (v : ℝ) (hv : 0<v) (z : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => (2*Real.pi*Complex.I*star (cuspFrequency h))*cubicResidualNonzeroTerm h (v,z)) := by
  have hs := ((cubicResidualDirectionalTerm_summable v hv z 1).add
    ((cubicResidualDirectionalTerm_summable v hv z Complex.I).mul_left Complex.I)).mul_left (1/2:ℂ)
  apply hs.congr
  intro h
  unfold cubicResidualDirectionalTerm
  linear_combination cubicResidualNonzeroTerm h (v,z)*horizontalPhaseMultiplier_wirtinger (cuspFrequency h)

end CubicEisenstein

end

end OAI
