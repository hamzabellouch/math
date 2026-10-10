import OAI.NumberTheory.DirichletL.Eisenstein.ResidualOrthogonality

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
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

theorem integralCoverTraceFunction_integral_cusp_decay (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H→ℂ) (C : ℝ)
    (hdec : ∀M : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (integralComplexMatrix M•upperPoint z v hv))‖≤C/v^3)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖integralCoverTraceFunction H K f
      (integralOrbitProjection K (integralComplexMatrix M•upperPoint z v hv))‖≤
        (H.relIndex K:ℝ)*C/v^3 := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  change ‖∑q : IntegralCoverCosets H K,
    f (integralCoverFiberPoint H K q (integralComplexMatrix M•upperPoint z v hv))‖≤_
  calc
    _ ≤ ∑q : IntegralCoverCosets H K,
        ‖f (integralCoverFiberPoint H K q (integralComplexMatrix M•upperPoint z v hv))‖ :=
      norm_sum_le _ _
    _ ≤ ∑_q : IntegralCoverCosets H K,C/v^3 := by
      apply Finset.sum_le_sum
      intro q _
      let r := integralCoverRep H K q
      have he : integralCoverFiberPoint H K q (integralComplexMatrix M•upperPoint z v hv)=
          integralOrbitProjection H (integralComplexMatrix ((r:SL(2,ActualEisensteinCubic.O))⁻¹*M)•upperPoint z v hv) := by
        rw [integralCoverFiberPoint_rep,integralSubgroup_smul,map_mul,mul_smul]
        rfl
      rw [he]
      exact hdec _ z v hv hlarge
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hc : Fintype.card (IntegralCoverCosets H K)=H.relIndex K := by
        rw [Subgroup.relIndex,Subgroup.index,Nat.card_eq_fintype_card]
      rw [hc]
      ring

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCoverLegAdjointFunction (f : IntegralOrbitQuotient H→ℂ) : KernelQuotient→ℂ :=
  integralCoverTraceFunction J globalKubotaKernel
    (fun q=>f (integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) q))

lemma kernelCoverLegAdjointFunction_measurable (f : IntegralOrbitQuotient H→ℂ)
    (hf : Measurable f) : Measurable (kernelCoverLegAdjointFunction e g he f) :=
  integralCoverTraceFunction_measurable J globalKubotaKernel _
    (hf.comp (integralConjugateMap_measurable _ _ _))

theorem kernelCoverLegAdjointFunction_represents (D : IntegralQuotientL2 H)
    (f : IntegralOrbitQuotient H→ℂ) (hf : Measurable f)
    (hrep : D=ᵐ[integralQuotientVolume H]f) :
    ContinuousLinearMap.adjoint (kernelCoverLeg hHK hJK e g he) D
      =ᵐ[integralQuotientVolume globalKubotaKernel]kernelCoverLegAdjointFunction e g he f := by
  rw [kernelCoverLeg_adjoint_apply]
  have hconj := (integralConjugatePullback_ae e.symm g⁻¹
    (integralCoverIntertwines_inverse e g he)
    (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree) D).trans
    ((integralConjugateMap_measurePreserving e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he)
      (hJK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hrep)
  exact integralCoverTrace_representative hJK globalKubotaKernel_le_levelThree _ _
    (hf.comp (integralConjugateMap_measurable _ _ _)) hconj

theorem kernelCoverLegAdjointFunction_cusp_decay (f : IntegralOrbitQuotient H→ℂ) (C : ℝ)
    (hdec : ∀M : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (g⁻¹•(integralComplexMatrix M•upperPoint z v hv)))‖≤C/v^3)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖kernelCoverLegAdjointFunction e g he f
      (integralOrbitProjection globalKubotaKernel (integralComplexMatrix M•upperPoint z v hv))‖≤
        (J.relIndex globalKubotaKernel:ℝ)*C/v^3 := by
  apply integralCoverTraceFunction_integral_cusp_decay J globalKubotaKernel _ C _ M z v hv hlarge
  intro N zz vv hvv hl
  exact hdec N zz vv hvv hl

end

local notation "O" => ActualEisensteinCubic.O

theorem commonCover_source_sum_eq_zero_of_inverse_cusp_decay
    {H : Subgroup (SL(2,ActualEisensteinCubic.O))} {ι : Type*} [Fintype ι]
    (J : ι→Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hHK : H≤globalKubotaKernel) (hJK : ∀i,J i≤globalKubotaKernel)
    [∀i,(J i).IsFiniteRelIndex globalKubotaKernel]
    (e : ∀i,H≃*J i) (g : ι→SL(2,ℂ)) (he : ∀i,IntegralCoverIntertwines (e i) (g i))
    (c : ι→ℂ) (D : IntegralQuotientL2 H)
    (hD : D=∑i,c i • kernelCoverLeg hHK (hJK i) (e i) (g i) (he i)
      (kernelSourceProjection cubicEisensteinResidue))
    (f : IntegralOrbitQuotient H→ℂ) (hf : Measurable f)
    (hrep : D=ᵐ[integralQuotientVolume H]f)
    (C : ι→ℝ) (hC : ∀i,0≤C i)
    (hdec : ∀i,∀M : SL(2,ActualEisensteinCubic.O),∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H ((g i)⁻¹•(integralComplexMatrix M•upperPoint z v hv)))‖≤C i/v^3) :
    D=0 := by
  let leg (i : ι) := kernelCoverLeg hHK (hJK i) (e i) (g i) (he i)
  apply commonCover_source_span_vanish leg c D hD
    (f:=fun i=>kernelCoverLegAdjointFunction (e i) (g i) (he i) f)
    (C:=fun i=>(J i).relIndex globalKubotaKernel*C i)
  · intro i
    rw [hD]
    exact kernelCoverLeg_adjoint_sum_eigenvector J hHK hJK e g he
      (kernelSourceProjection cubicEisensteinResidue) (8/9:ℂ)
      kernelSourceProjection_cubicEisensteinResidue_eigenvector c i
  · intro i
    exact kernelCoverLegAdjointFunction_represents hHK (hJK i) (e i) (g i) (he i) D f hf hrep
  · intro i
    exact mul_nonneg (Nat.cast_nonneg _) (hC i)
  · intro i M z v hv hlarge
    exact kernelCoverLegAdjointFunction_cusp_decay (e i) (g i) (he i) f (C i) (hdec i) M z v hv hlarge

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise

local notation "Eis" => ActualEisensteinCubic.O

lemma integralProjection_quasiMeasurePreserving (H:Subgroup (SL(2,Eis)))
    (hH:H≤CubicKubota.levelThree) :
    Measure.QuasiMeasurePreserving (integralOrbitProjection H)
      hyperbolicVolume (integralQuotientVolume H) := by
  let proj:=integralOrbitProjection H
  have hp:Measurable proj:=measurable_integralOrbitProjection H
  refine ⟨hp,Measure.AbsolutelyContinuous.mk fun S hS hzero=>?_⟩
  rw [Measure.map_apply hp hS]
  have hd:hyperbolicVolume ((proj ⁻¹' S)∩hyperbolicFundamentalSet H)=0:=by
    simpa only [integralQuotientVolume,proj,
      Measure.map_apply (measurable_integralOrbitProjection _) hS,
      Measure.restrict_apply ((measurable_integralOrbitProjection _) hS)] using hzero
  have hinv:∀M:H,M • (proj ⁻¹' S)=proj ⁻¹' S:=by
    intro M
    ext w
    constructor
    · rintro ⟨u,hu,rfl⟩
      change proj (M • u)∈S
      change proj u∈S at hu
      rwa [show proj (M • u)=proj u from integralOrbitProjection_eq H M u]
    · intro hw
      refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
      change proj (M⁻¹ • w)∈S
      rwa [show proj (M⁻¹ • w)=proj w from integralOrbitProjection_eq H M⁻¹ w]
  exact (hyperbolicFundamentalSet_isFundamentalDomain H hH).measure_zero_of_invariant
    (proj ⁻¹' S) hinv hd

theorem integralQuotient_continuous_lifts_eq (H:Subgroup (SL(2,Eis)))
    (hH:H≤CubicKubota.levelThree) (F G:IntegralOrbitQuotient H→ℂ)
    (f g:HyperbolicSpace→ℂ) (hf:Continuous f) (hg:Continuous g)
    (hF:∀w,F (integralOrbitProjection H w)=f w)
    (hG:∀w,G (integralOrbitProjection H w)=g w)
    (he:F=ᵐ[integralQuotientVolume H]G) : f=g := by
  have hl: f=ᵐ[hyperbolicVolume]g:=by
    have hh:=(integralProjection_quasiMeasurePreserving H hH).ae_eq_comp he
    simpa only [Function.comp_def,hF,hG] using hh
  exact Measure.eq_of_ae_eq hl hf hg

theorem integralQuotient_zero_continuous_lift (H:Subgroup (SL(2,Eis)))
    (hH:H≤CubicKubota.levelThree) (F:IntegralOrbitQuotient H→ℂ)
    (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (hF:∀w,F (integralOrbitProjection H w)=f w)
    (hzero:F=ᵐ[integralQuotientVolume H]0) : ∀w,f w=0 := by
  have he:f=0:=integralQuotient_continuous_lifts_eq H hH F 0 f 0 hf
    continuous_const hF (fun _=>rfl) hzero
  intro w
  exact congrFun he w

end

section
open Filter MeasureTheory
open scoped Classical MatrixGroups BigOperators

open CubicKubota ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

theorem cubeDifferenceL2_eq_zero (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) :
    cubeDifferenceL2 p hp.ne_zero=0 := by
  let : Finite (CubeResidues p) := finite_quotient_span (pow_ne_zero 3 hp.ne_zero)
  let : Fintype (CubeResidues p) := Fintype.ofFinite _
  let : ∀i : CubeLegIndex p,(cubeLegTarget p hp.ne_zero i).FiniteIndex :=
    cubeLegTarget_finiteIndex p hp.ne_zero
  let : ∀i : CubeLegIndex p,(cubeLegTarget p hp.ne_zero i).IsFiniteRelIndex globalKubotaKernel :=
    fun i=>Subgroup.isFiniteRelIndex_of_finiteIndex
  obtain ⟨C0,hC0,h0⟩ := cubeSourceDifference_cubic_decay p hp hprimary
  obtain ⟨C1,hC1,h1⟩ := cubeSourceDifference_inverse_cubic_decay p hp hprimary
  let C : CubeLegIndex p→ℝ := fun i=>i.elim C0 (fun _=>C1)
  apply commonCover_source_sum_eq_zero_of_inverse_cusp_decay
    (cubeLegTarget p hp.ne_zero) (cubeCommonCover_le p hp.ne_zero)
    (cubeLegTarget_le p hp.ne_zero) (cubeLegEquiv p hp.ne_zero)
    (cubeLegMatrix p hp.ne_zero) (cubeLeg_intertwines p hp.ne_zero)
    (cubeLegCoefficient p) (cubeDifferenceL2 p hp.ne_zero) ?_
    (cubeDifferenceQuotientFunction p hp.ne_zero)
    (cubeDifferenceQuotientFunction_measurable p hp.ne_zero)
    (cubeDifferenceL2_representative p hp.ne_zero) C ?_ ?_
  · simp only [cubeDifferenceL2,tsum_fintype,cubeLeg]
  · intro i
    cases i with
    | none => exact hC0
    | some r => exact hC1
  · intro i M z v hv hlarge
    rw [cubeDifferenceQuotientFunction_projection]
    cases i with
    | none =>
      simpa only [cubeLegMatrix,inv_one,one_smul,C,Option.elim] using h0 M z v hv hlarge.le
    | some r =>
      exact h1 (GaussianShiftedPartition.representative (p^3) r) M z v hv hlarge.le

theorem cubeSourceDifference_eq_zero (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) (w : HyperbolicSpace) :
    cubeSourceDifference p hp.ne_zero w=0 := by
  have hz : cubeDifferenceQuotientFunction p hp.ne_zero
      =ᵐ[integralQuotientVolume (cubeCommonCover p hp.ne_zero)]0 := by
    apply (cubeDifferenceL2_representative p hp.ne_zero).symm.trans
    rw [cubeDifferenceL2_eq_zero p hp hprimary]
    exact Lp.coeFn_zero ℂ 2 _
  exact integralQuotient_zero_continuous_lift (cubeCommonCover p hp.ne_zero)
    ((cubeCommonCover_le p hp.ne_zero).trans globalKubotaKernel_le_levelThree)
    (cubeDifferenceQuotientFunction p hp.ne_zero) (cubeSourceDifference p hp.ne_zero)
    (cubeSourceDifference_continuous p hp.ne_zero)
    (cubeDifferenceQuotientFunction_projection p hp.ne_zero) hz w

theorem cubicSource_cubeAverage (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) (w : HyperbolicSpace) :
    cubeAverage p hp.ne_zero cubicSourceResidualFunction w=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction w :=
  sub_eq_zero.mp (cubeSourceDifference_eq_zero p hp hprimary w)

theorem sourceArithmeticResidue_prime_cube (p : ActualEisensteinCubic.O) (hp : Prime p)
    (hprimary : ActualEisensteinCubic.lambda^2∣p-1) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    sourceArithmeticResidue (h*p^3)=sourceArithmeticResidue h :=
  sourceArithmeticResidue_cube_of_eigenrelation p hp.ne_zero
    (cubicSource_cubeAverage p hp hprimary) h hh

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma rational_inversion_complex :
    integralComplexMatrix (rationalEmbedding ModularGroup.S)=complexWeyl := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [integralComplexMatrix_apply, rationalEmbedding,
    Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.S, complexWeyl]

theorem exists_nonzero_sourceResidualFourierCoefficient :
    ∃h:Eis,h≠0 ∧ sourceResidualFourierCoefficient h≠0 := by
  by_contra hn
  have hz:∀h:Eis,h≠0→sourceResidualFourierCoefficient h=0:=by
    intro h hh
    by_contra hne
    exact hn ⟨h,hh,hne⟩
  let C:ℂ:=(3*(Real.pi:ℂ))*constantArithmeticResidue
  have hC:C≠0:=mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    constantArithmeticResidue_ne_zero
  have hprofile (z:ℂ) (v:ℝ) (hv:0<v) :
      cubicSourceResidualFunction (upperPoint z v hv)=C*(v:ℂ)^(2/3:ℂ):=by
    rw [cubicSourceResidualFunction_bessel]
    have hsum:(∑'h:Eis,(if h=0 then 0 else sourceResidualFourierCoefficient h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z))=0:=by
      calc
        _=∑' (_:Eis),(0:ℂ):=by
          apply tsum_congr
          intro h
          by_cases hh:h=0
          · simp [hh]
          · simp [hh,hz h hh]
        _=0:=tsum_zero
    rw [hsum,add_zero]
  have hpoint: integralComplexMatrix (rationalEmbedding ModularGroup.S) •
      upperPoint 0 2 (by norm_num)=upperPoint 0 (1/2) (by norm_num):=by
    rw [rational_inversion_complex,complexWeyl_action]
    apply upperPoint_congr <;> norm_num
  have hi:=cubicSourceResidualFunction_rational_invariant ModularGroup.S
    (upperPoint 0 2 (by norm_num))
  rw [hpoint,hprofile,hprofile] at hi
  have hc:(1/2:ℂ)^(2/3:ℂ)=(2:ℂ)^(2/3:ℂ):=by
    exact mul_left_cancel₀ hC (by simpa only [Complex.ofReal_div,Complex.ofReal_one,
      Complex.ofReal_ofNat] using hi)
  have hr:(1/2:ℝ)^(2/3:ℝ)=(2:ℝ)^(2/3:ℝ):=by
    apply Complex.ofReal_injective
    have h1:=Complex.ofReal_cpow (show (0:ℝ)≤1/2 by norm_num) (2/3:ℝ)
    have h2:=Complex.ofReal_cpow (show (0:ℝ)≤2 by norm_num) (2/3:ℝ)
    norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at h1 h2
    exact h1.trans (hc.trans h2.symm)
  have hlt:(1/2:ℝ)^(2/3:ℝ)<(2:ℝ)^(2/3:ℝ):=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
  exact hlt.ne hr

theorem exists_nonzero_sourceArithmeticResidue :
    ∃h:Eis,h≠0 ∧ sourceArithmeticResidue h≠0 := by
  obtain ⟨h,hh,hn⟩:=exists_nonzero_sourceResidualFourierCoefficient
  refine ⟨h,hh,?_⟩
  intro hz
  apply hn
  simp only [sourceResidualFourierCoefficient,hz,mul_zero]

end

section
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

abbrev PrincipalRamifiedIndex (h:Eis) := Eisˣ × Fin (ramifiedFrequencyBound h+1)

def principalRamifiedIndex (h:Eis) (i:PrincipalRamifiedIndex h) : Eis :=
  h*(9*(i.1.val*lambda^(i.2.val+2)))

def principalRamifiedWeight (h:Eis) (i:PrincipalRamifiedIndex h) (s:ℂ) : ℂ :=
  ((3^(i.2.val+2):ℕ):ℂ)^(-s)*explicitRamifiedCoefficient h i.1 (i.2.val+2)

lemma principalRamifiedWeight_analytic (h:Eis) (i:PrincipalRamifiedIndex h) (s:ℂ) :
    AnalyticAt ℂ (principalRamifiedWeight h i) s := by
  apply AnalyticAt.mul _ analyticAt_const
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall fun z=>(differentiableAt_id.neg).const_cpow
    (Or.inl (by exact_mod_cast (pow_ne_zero (i.2.val+2) (by norm_num : (3:ℕ)≠0))))

lemma scatteringCoefficient_eq_principalRamified (s:ℂ) (hs:2<s.re)
    (h:Eis) (hh:h≠0) :
    scatteringCoefficient s h=
      (∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i s*
        unramifiedCubicGaussSeries s (principalRamifiedIndex h i))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [scatteringCoefficient_explicit_ramified s hs h hh,tsum_fintype]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  rw [←Fin.sum_univ_eq_sum_range]
  rfl

theorem principalArithmeticResidue_eq_ramified_table (h:Eis) (hh:h≠0) :
    principalArithmeticResidue h=
      (∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i (4/3)*
        unramifiedGaussResidue (principalRamifiedIndex h i))/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  let coeff (i:PrincipalRamifiedIndex h) (s:ℂ) :=
    principalRamifiedWeight h i s*cuspWhittakerHeightFactor s h
  have he:=finite_unramified_residue (principalRamifiedIndex h) coeff
    (fun i s hs=>(principalRamifiedWeight_analytic h i s).mul
      (cuspWhittakerHeightFactor_analyticAt h s hs))
    (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num))
    (kernelCuspFourier h cubicEisensteinResidue)
    (fun s hs hi=>kernelCuspFourierFamily_analyticAt_nonreal h 2 3
      (by norm_num) (by norm_num) s hs.ne' hi.ne')
    (kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num))
    (fun s hs hi=>by
      rw [kernelCuspFourierFamily_eq_upper h hh ⟨by linarith,hi⟩]
      dsimp only
      rw [scatteringCoefficient_eq_principalRamified s (by linarith) h hh]
      simp only [coeff]
      rw [mul_div_cancel₀ _ cusp_volume_ne_zero,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi'
      ring)
  rw [kernelCuspFourier_principal_residue] at he
  have hH:=cuspWhittakerHeightFactor_center_ne_zero h
  apply (eq_div_iff cusp_volume_ne_zero).mpr
  apply mul_right_cancel₀ hH
  calc
    principalArithmeticResidue h*((9*Real.sqrt 3/2:ℝ):ℂ)*cuspWhittakerHeightFactor (4/3) h
        = kernelCuspFourier h cubicEisensteinResidue := by
          rw [kernelCuspFourier_principal_residue]
          ring
    _ = _ := by
      rw [kernelCuspFourier_principal_residue,he]
      simp only [coeff]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem sourceArithmeticResidue_eq_ramified_table (h:Eis) (hh:h≠0) :
    sourceArithmeticResidue h=
      if ShortDraftTrace.breveE (cuspFrequency h)=1 then
        ((∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i (4/3)*
            unramifiedGaussResidue (principalRamifiedIndex h i))+
          3*unramifiedGaussResidue (9*h))/(4*((9*Real.sqrt 3/2:ℝ):ℂ))
      else 0 := by
  rw [sourceArithmeticResidue,principalArithmeticResidue_eq_ramified_table h hh]
  split_ifs
  · ring
  · rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma arithmeticResidueSum_frequency_cube (h c p:Eis) (hc:c≠0)
    (hlevel:(3:Eis)∣c) (hprimary:lambda^2∣p-1) (hcp:IsCoprime c p) :
    arithmeticResidueSum (h*p^3) c=arithmeticResidueSum h c := by
  have ht:denominatorCondition c p:=⟨hcp,three_dvd_lambda_sq.trans hprimary⟩
  have hb:(eisEmbedding (symbol c p))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime c p hprimary hcp,map_one]
  have h1:=arithmeticResidueSum_frequency_twist h c p hc hlevel ht
  have h2:=arithmeticResidueSum_frequency_twist (h*p) c p hc hlevel ht
  have h3:=arithmeticResidueSum_frequency_twist (h*p*p) c p hc hlevel ht
  rw [show h*p^3=h*p*p*p by ring]
  calc
    _=eisEmbedding (symbol c p)^3*arithmeticResidueSum (h*p*p*p) c:=by rw [hb,one_mul]
    _=eisEmbedding (symbol c p)^2*arithmeticResidueSum (h*p*p) c:=by rw [pow_succ,mul_assoc,h3]
    _=eisEmbedding (symbol c p)*arithmeticResidueSum (h*p) c:=by rw [pow_two,mul_assoc,h2]
    _=arithmeticResidueSum h c:=h1

lemma ramified_prime_Gauss_cancel (h c p:Eis) (hc:c≠0) (hlevel:(3:Eis)∣c)
    (hp:Prime p) (hprimary:lambda^2∣p-1) (hcp:IsCoprime c p) :
    arithmeticResidueSum h c*primeCubicGauss p hp hprimary 1 (h*(9*c))=
      arithmeticResidueSum (h*p) c*primeCubicGauss p hp hprimary 1 (9*h) := by
  have ht:denominatorCondition c p:=⟨hcp,three_dvd_lambda_sq.trans hprimary⟩
  have hA:=arithmeticResidueSum_frequency_twist h c p hc hlevel ht
  have hG:=cubicUnitGaussSum_frequency_twist (9*h) p c hp.ne_zero hprimary hcp.symm
  rw [←primeCubicGauss_one_eq p hp hprimary,←primeCubicGauss_one_eq p hp hprimary] at hG
  rw [show (9*h)*c=h*(9*c) by ring] at hG
  have hb:eisEmbedding (symbol c p)≠0:=by
    have hcube:(eisEmbedding (symbol c p))^3=1:=by
      rw [←map_pow,symbol_cube_of_isCoprime c p hprimary hcp,map_one]
    intro hz
    simp only [hz,zero_pow (by decide : (3:ℕ)≠0)] at hcube
    exact zero_ne_one hcube
  apply mul_left_cancel₀ hb
  calc
    _=arithmeticResidueSum h c*(eisEmbedding (symbol c p)*
      primeCubicGauss p hp hprimary 1 (h*(9*c))):=by ring
    _=arithmeticResidueSum h c*primeCubicGauss p hp hprimary 1 (9*h):=by rw [hG]
    _=(eisEmbedding (symbol c p)*arithmeticResidueSum (h*p) c)*
      primeCubicGauss p hp hprimary 1 (9*h):=by rw [hA]
    _=_:=by ring

lemma ramified_prime_frequency_not_dvd (h p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    ¬p∣h*(9*(u.val*lambda^n)) := by
  intro hd
  rcases hp.dvd_mul.mp hd with hh|hc
  · exact hph hh
  have hcp: IsCoprime (9*(u.val*lambda^n)) p := by
    have h3: IsCoprime (3:Eis) p:=(primary_coprime_three p hprimary).symm
    have hram: IsCoprime (u.val*lambda^n) p:=
      (ramified_primary_coprime u n p hprimary).of_mul_left_right
    convert h3.pow_left (m:=2) |>.mul_left hram using 1 ; norm_num
  exact hp.not_isUnit (hcp.symm.isUnit_of_dvd hc)

lemma sourceRayPhase_mul_primary (h p:Eis) (hprimary:lambda^2∣p-1) :
    ShortDraftTrace.breveE (cuspFrequency (h*p))=
      ShortDraftTrace.breveE (cuspFrequency h) := by
  obtain ⟨d,hd⟩:=three_dvd_lambda_sq.trans hprimary
  have hp:p=1+3*d:=by linear_combination hd
  have he:cuspFrequency (h*p)=cuspFrequency h+cuspFrequency h*(3*eisEmbedding d):=by
    rw [hp,cuspFrequency,cuspFrequency,map_mul,map_add,map_mul,map_one,map_ofNat]
    ring
  rw [he,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def principalResidueTerm (h:Eis) (u:Eisˣ) (n:ℕ) : ℂ :=
  ((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum h (u.val*lambda^(n+2))*
    unramifiedGaussResidue (h*(9*(u.val*lambda^(n+2))))

lemma principalResidueTerm_vanish (h:Eis) (hh:h≠0) (u:Eisˣ) (n:ℕ)
    (hn:ramifiedFrequencyBound h<n+2) : principalResidueTerm h u n=0 := by
  have hA:arithmeticResidueSum h (u.val*lambda^(n+2))=0:=by
    by_contra hne
    have hb:=Nat.le_log_of_pow_le (by decide : 1<3)
      (ramified_arithmetic_norm_bound h hh u (n+2) (by omega) hne)
    exact (not_le_of_gt hn) hb
  simp only [principalResidueTerm,hA,mul_zero,zero_mul]

lemma principalArithmeticResidue_eq_sum (h:Eis) (hh:h≠0) (N:ℕ)
    (hN:ramifiedFrequencyBound h+1≤N) :
    principalArithmeticResidue h=
      (∑u:Eisˣ,∑n∈Finset.range N,principalResidueTerm h u n)/
        ((9*Real.sqrt 3/2:ℝ):ℂ) := by
  rw [principalArithmeticResidue_eq_ramified_table h hh,Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  change (∑n:Fin (ramifiedFrequencyBound h+1),
    principalRamifiedWeight h (u,n) (4/3)*unramifiedGaussResidue (principalRamifiedIndex h (u,n)))=_
  have hcoeff (n:ℕ) : explicitRamifiedCoefficient h u (n+2)=
      arithmeticResidueSum h (u.val*lambda^(n+2)):=
    (arithmeticResidueSum_eq_explicitRamifiedCoefficient h u (n+2) (by omega)).symm
  simp only [principalRamifiedWeight,principalRamifiedIndex,hcoeff]
  change (∑n:Fin (ramifiedFrequencyBound h+1),principalResidueTerm h u n.val)=_
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_subset (Finset.range_mono hN)
  intro n hn hn'
  exact principalResidueTerm_vanish h hh u n (by simp only [Finset.mem_range] at hn';omega)

lemma principalResidueTerm_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (h*p^3) u n=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalResidueTerm h u n-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
        principalResidueTerm (h*p) u n := by
  let c:=u.val*lambda^(n+2)
  have hc:c≠0:=ramifiedElement_ne_zero u (n+2)
  have hlevel:(3:Eis)∣c:=ramifiedElement_level u (n+2) (by omega)
  have hcp:IsCoprime c p:=(ramified_primary_coprime u (n+2) p hprimary).of_mul_left_right
  have hfreq:¬p∣h*(9*c):=ramified_prime_frequency_not_dvd h p hp hprimary hph u (n+2)
  have hA:=arithmeticResidueSum_frequency_cube h c p hc hlevel hprimary hcp
  have hG:=ramified_prime_Gauss_cancel h c p hc hlevel hp hprimary hcp
  change _*arithmeticResidueSum (h*p^3) c*unramifiedGaussResidue ((h*p^3)*(9*c))=_
  rw [hA,show (h*p^3)*(9*c)=(h*(9*c))*p^3 by ring,
    unramifiedGaussResidue_prime_recurrence p hp hprimary (h*(9*c)) hfreq]
  change _=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum h c*unramifiedGaussResidue (h*(9*c)))-
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum (h*p) c*unramifiedGaussResidue ((h*p)*(9*c)))
  rw [show (h*p)*(9*c)=(h*(9*c))*p by ring]
  linear_combination -(((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ)))*
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*unramifiedGaussResidue ((h*(9*c))*p)*hG

theorem principalArithmeticResidue_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    principalArithmeticResidue (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalArithmeticResidue h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
        principalArithmeticResidue (h*p) := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  let N:=max (ramifiedFrequencyBound (h*p^3)+1)
    (max (ramifiedFrequencyBound h+1) (ramifiedFrequencyBound (h*p)+1))
  rw [principalArithmeticResidue_eq_sum (h*p^3) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum h hh N (le_trans (le_max_left _ _) (le_max_right _ _)),
    principalArithmeticResidue_eq_sum (h*p) (mul_ne_zero hh hp.ne_zero) N
      (le_trans (le_max_right _ _) (le_max_right _ _))]
  simp_rw [principalResidueTerm_prime_recurrence p hp hprimary h hph,
    Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

theorem sourceArithmeticResidue_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*sourceArithmeticResidue h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*
        sourceArithmeticResidue (h*p) := by
  have hm:ShortDraftTrace.breveE (cuspFrequency (h*p^3))=
      ShortDraftTrace.breveE (cuspFrequency h):=by
    rw [show h*p^3=((h*p)*p)*p by ring]
    rw [sourceRayPhase_mul_primary _ p hprimary,sourceRayPhase_mul_primary _ p hprimary,
      sourceRayPhase_mul_primary _ p hprimary]
  have hp9:¬p∣9*h:=by
    have hh:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using hh
  simp only [sourceArithmeticResidue,hm,sourceRayPhase_mul_primary h p hprimary]
  split_ifs with hh
  · rw [principalArithmeticResidue_prime_recurrence p hp hprimary h hph,
      show 9*(h*p^3)=(9*h)*p^3 by ring,
      unramifiedGaussResidue_prime_recurrence p hp hprimary (9*h) hp9,
      show 9*(h*p)=(9*h)*p by ring]
    ring
  · ring

end CubicEisenstein

end

end OAI
