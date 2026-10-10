import OAI.NumberTheory.DirichletL.Eisenstein.SourceProjection

namespace OAI

noncomputable section

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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

open CubicKubota
local notation "O" => ActualEisensteinCubic.O

abbrev SourceKernelQuotient := IntegralOrbitQuotient globalKubotaKernel

def sourceComplexMatrix : levelTwo→*SL(2,ℂ) :=
  integralComplexMatrix.comp levelTwo.subtype

lemma globalKubotaKernel_source_conjugate_mem (M : levelTwo) (N : globalKubotaKernel) :
    (M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹∈globalKubotaKernel :=
  CubicKubota.globalKubotaKernel_conjugate M N N.property

def kernelSourceConjugate (M : levelTwo) : globalKubotaKernel ≃* globalKubotaKernel where
  toFun N := ⟨(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹,globalKubotaKernel_source_conjugate_mem M N⟩
  invFun N := ⟨(M⁻¹:levelTwo)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelTwo)⁻¹,globalKubotaKernel_source_conjugate_mem M⁻¹ N⟩
  left_inv N := by apply Subtype.ext; simp [mul_assoc]
  right_inv N := by apply Subtype.ext; simp [mul_assoc]
  map_mul' N P := by apply Subtype.ext; simp [mul_assoc]

lemma kernelSourceConjugate_coe (M : levelTwo) (N : globalKubotaKernel) :
    (kernelSourceConjugate M N : SL(2,ActualEisensteinCubic.O))=(M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹ := rfl

lemma source_action_respects_kernel (M : levelTwo) (u v : HyperbolicSpace)
    (h : (integralOrbitRel globalKubotaKernel).r u v) :
    (integralOrbitRel globalKubotaKernel).r (sourceComplexMatrix M • u) (sourceComplexMatrix M • v) := by
  obtain ⟨N,hN⟩ := h
  refine ⟨kernelSourceConjugate M N,?_⟩
  change integralComplexMatrix ((M:SL(2,ActualEisensteinCubic.O))*(N:SL(2,ActualEisensteinCubic.O))*(M:SL(2,ActualEisensteinCubic.O))⁻¹) •
    (sourceComplexMatrix M • u)=sourceComplexMatrix M • v
  rw [map_mul,map_mul,map_inv,mul_smul,mul_smul]
  change sourceComplexMatrix M • (integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) •
    ((sourceComplexMatrix M)⁻¹ • (sourceComplexMatrix M • u)))=_
  rw [inv_smul_smul,hN]

def kernelSourceAction (M : levelTwo) : SourceKernelQuotient→SourceKernelQuotient :=
  Quotient.map' (fun w => sourceComplexMatrix M • w) (source_action_respects_kernel M)

lemma kernelSourceAction_mk (M : levelTwo) (w : HyperbolicSpace) :
    kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)=
      integralOrbitProjection globalKubotaKernel (sourceComplexMatrix M • w) := rfl

lemma kernelSourceAction_one (q : SourceKernelQuotient) : kernelSourceAction 1 q=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (sourceComplexMatrix 1 • w)=integralOrbitProjection globalKubotaKernel w
    rw [map_one,one_smul]

lemma kernelSourceAction_mul (M N : levelTwo) (q : SourceKernelQuotient) :
    kernelSourceAction (M*N) q=kernelSourceAction M (kernelSourceAction N q) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection globalKubotaKernel (sourceComplexMatrix (M*N) • w)=
      integralOrbitProjection globalKubotaKernel (sourceComplexMatrix M • (sourceComplexMatrix N • w))
    rw [map_mul,mul_smul]

lemma kernelSourceAction_continuous (M : levelTwo) : Continuous (kernelSourceAction M) :=
  (continuous_hyperbolic_action (sourceComplexMatrix M)).quotient_map' (source_action_respects_kernel M)

def kernelSourceHomeomorph (M : levelTwo) : SourceKernelQuotient ≃ₜ SourceKernelQuotient where
  toFun := kernelSourceAction M
  invFun := kernelSourceAction M⁻¹
  left_inv q := by rw [←kernelSourceAction_mul,inv_mul_cancel,kernelSourceAction_one]
  right_inv q := by rw [←kernelSourceAction_mul,mul_inv_cancel,kernelSourceAction_one]
  continuous_toFun := kernelSourceAction_continuous M
  continuous_invFun := kernelSourceAction_continuous M⁻¹

lemma kernelSourceAction_fundamentalDomain (M : levelTwo) :
    IsFundamentalDomain globalKubotaKernel
      ((fun w : HyperbolicSpace => sourceComplexMatrix M • w) '' hyperbolicFundamentalSet globalKubotaKernel)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain globalKubotaKernel
    globalKubotaKernel_le_levelThree).image_of_equiv (MulAction.toPerm (sourceComplexMatrix M))
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm (sourceComplexMatrix M)).symm hyperbolicVolume hyperbolicVolume from by
      exact (measurePreserving_smul (sourceComplexMatrix M)⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    (kernelSourceConjugate M⁻¹).toEquiv
  intro N w
  change sourceComplexMatrix M • (integralComplexMatrix
    ((M⁻¹:levelTwo)*(N:SL(2,ActualEisensteinCubic.O))*(M⁻¹:levelTwo)⁻¹) • w)=
      integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O)) • (sourceComplexMatrix M • w)
  simp only [Subgroup.coe_inv,map_mul,map_inv]
  change sourceComplexMatrix M • (((sourceComplexMatrix M)⁻¹*integralComplexMatrix (N:SL(2,ActualEisensteinCubic.O))*
    ((sourceComplexMatrix M)⁻¹)⁻¹) • w)=_
  simp only [inv_inv,mul_smul,smul_inv_smul]

lemma kernelSourceAction_measurePreserving (M : levelTwo) :
    MeasurePreserving (kernelSourceAction M) (integralQuotientVolume globalKubotaKernel)
      (integralQuotientVolume globalKubotaKernel) := by
  refine ⟨(kernelSourceAction_continuous M).measurable,?_⟩
  let act : HyperbolicSpace→HyperbolicSpace := fun w => sourceComplexMatrix M • w
  have hmap := (measurePreserving_smul (sourceComplexMatrix M) hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul (sourceComplexMatrix M)) (hyperbolicFundamentalSet globalKubotaKernel)
  have heq : kernelSourceAction M ∘ integralOrbitProjection globalKubotaKernel=
      integralOrbitProjection globalKubotaKernel ∘ act := by ext w; rfl
  change Measure.map (kernelSourceAction M)
    (Measure.map (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [Measure.map_map (kernelSourceAction_continuous M).measurable
    (measurable_integralOrbitProjection _),heq,
    ←Measure.map_map (measurable_integralOrbitProjection _) (continuous_hyperbolic_action _).measurable]
  change Measure.map (integralOrbitProjection globalKubotaKernel)
    (Measure.map act (hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)))=_
  rw [hmap.map_eq]
  exact integralQuotientVolume_independent globalKubotaKernel globalKubotaKernel_le_levelThree _
    (kernelSourceAction_fundamentalDomain M)

end CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota

def kernelSourcePullback (M : levelTwo) : KernelQuotientL2 →ₗᵢ[ℂ] KernelQuotientL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (kernelSourceAction M) (kernelSourceAction_measurePreserving M)

lemma kernelSourcePullback_ae_eq (M : levelTwo) (F : KernelQuotientL2) :
    kernelSourcePullback M F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => F (kernelSourceAction M q) :=
  Lp.coeFn_compMeasurePreserving F (kernelSourceAction_measurePreserving M)

lemma kernelSourcePullback_one (F : KernelQuotientL2) : kernelSourcePullback 1 F=F := by
  apply Lp.ext
  filter_upwards [kernelSourcePullback_ae_eq 1 F] with q hq
  simpa only [kernelSourceAction_one] using hq

lemma kernelSourcePullback_comp (M N : levelTwo) (F : KernelQuotientL2) :
    kernelSourcePullback M (kernelSourcePullback N F)=kernelSourcePullback (N*M) F := by
  have hcomp := (kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelSourcePullback_ae_eq N F)
  apply Lp.ext
  filter_upwards [kernelSourcePullback_ae_eq M (kernelSourcePullback N F),hcomp,
    kernelSourcePullback_ae_eq (N*M) F] with q hp hn hnm
  rw [hp,hnm]
  exact hn.trans (congrArg F (kernelSourceAction_mul N M q).symm)

lemma kernelSourcePullback_surjective (M : levelTwo) : Function.Surjective (kernelSourcePullback M) := by
  intro F
  refine ⟨kernelSourcePullback M⁻¹ F,?_⟩
  rw [kernelSourcePullback_comp,inv_mul_cancel,kernelSourcePullback_one]

def kernelSourceUnitary (M : levelTwo) : KernelQuotientL2 ≃ₗᵢ[ℂ] KernelQuotientL2 :=
  LinearIsometryEquiv.ofSurjective (kernelSourcePullback M) (kernelSourcePullback_surjective M)

lemma kernelSourceUnitary_apply (M : levelTwo) (F : KernelQuotientL2) :
    kernelSourceUnitary M F=kernelSourcePullback M F := rfl

local notation "O" => ActualEisensteinCubic.O

lemma kernelSourceAction_of_kernel (g : levelTwo)
    (hg : (g:SL(2,ActualEisensteinCubic.O))∈globalKubotaKernel) (q : SourceKernelQuotient) :
    kernelSourceAction g q=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact integralOrbitProjection_eq globalKubotaKernel ⟨(g:SL(2,ActualEisensteinCubic.O)),hg⟩ w

lemma rationalCongruenceThree_in_kernel (r : SL(2,ℤ)) (hr : r∈rationalCongruenceThree) :
    rationalEmbedding r∈globalKubotaKernel := by
  have hr3 := (mem_rationalCongruenceThree r).mp hr
  exact (globalKubotaKernel_mem _).mpr ⟨hr3,complexCharacter_rational_intersection r hr3⟩

lemma kernelSourceAction_rational_eq (r s : SL(2,ℤ))
    (hrs : rationalReductionThree r=rationalReductionThree s) (q : SourceKernelQuotient) :
    kernelSourceAction (rationalLift r) q=kernelSourceAction (rationalLift s) q := by
  have hd : r*s⁻¹∈rationalCongruenceThree := by
    apply (rationalReductionThree_eq_one_iff _).mp
    rw [map_mul,map_inv,hrs,mul_inv_cancel]
  have hk := rationalCongruenceThree_in_kernel _ hd
  have he : rationalLift r=rationalLift (r*s⁻¹)*rationalLift s := by
    rw [←map_mul,inv_mul_cancel_right]
  rw [he,kernelSourceAction_mul]
  exact kernelSourceAction_of_kernel _ hk _

lemma kernelSourcePullback_rational_eq (r s : SL(2,ℤ))
    (hrs : rationalReductionThree r=rationalReductionThree s) (F : KernelQuotientL2) :
    kernelSourcePullback (rationalLift r) F=kernelSourcePullback (rationalLift s) F := by
  apply Lp.ext
  filter_upwards [kernelSourcePullback_ae_eq (rationalLift r) F,
    kernelSourcePullback_ae_eq (rationalLift s) F] with q hr hs
  rw [hr,hs,kernelSourceAction_rational_eq r s hrs]

def kernelSourceProjection : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  (24:ℂ)⁻¹ • ∑q : levelTwo ⧸ levelThreeInTwo,
    (kernelSourcePullback (rationalLift (sourceRationalSection q))).toContinuousLinearMap

lemma kernelSourceProjection_apply (F : KernelQuotientL2) :
    kernelSourceProjection F=(24:ℂ)⁻¹ • ∑q : levelTwo ⧸ levelThreeInTwo,
      kernelSourcePullback (rationalLift (sourceRationalSection q)) F := by
  simp only [kernelSourceProjection,_root_.smul_apply,_root_.sum_apply,
    LinearIsometry.coe_toContinuousLinearMap]

lemma kernelSourceProjection_eq_twentyFour (F : KernelQuotientL2) :
    kernelSourceProjection F=(24:ℂ)⁻¹ • ∑i : RationalBruhatIndex,
      kernelSourcePullback (rationalLift (rationalBruhatRep i)) F := by
  rw [kernelSourceProjection_apply]
  congr 1
  rw [←rationalCosetEquiv.sum_comp]
  simp only [sourceRationalSection,Equiv.symm_apply_apply]

lemma norm_kernelSourceProjection_apply (F : KernelQuotientL2) :
    ‖kernelSourceProjection F‖≤‖F‖ := by
  rw [kernelSourceProjection_apply,norm_smul]
  calc
    _ ≤ ‖(24:ℂ)⁻¹‖ * ∑q : levelTwo ⧸ levelThreeInTwo,
      ‖kernelSourcePullback (rationalLift (sourceRationalSection q)) F‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖F‖ := by
      simp only [LinearIsometry.norm_map,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hc : Fintype.card (levelTwo ⧸ levelThreeInTwo)=24 := by
        simpa only [Nat.card_eq_fintype_card] using sourceQuotient_card
      rw [hc]
      norm_num
      ring

lemma norm_kernelSourceProjection : ‖kernelSourceProjection‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun F => by simpa using norm_kernelSourceProjection_apply F)

lemma sourceSection_mul_reduction (q : levelTwo ⧸ levelThreeInTwo) (r : SL(2,ℤ)) :
    rationalReductionThree (sourceRationalSection q*r)=
      rationalReductionThree (sourceRationalSection (q*rationalQuotient r)) := by
  apply (rationalQuotient_eq_iff_reduction _ _).mp
  rw [map_mul,sourceRationalSection_spec,sourceRationalSection_spec]

lemma kernelSourcePullback_projection (r : SL(2,ℤ)) (F : KernelQuotientL2) :
    kernelSourcePullback (rationalLift r) (kernelSourceProjection F)=kernelSourceProjection F := by
  rw [kernelSourceProjection_apply,map_smul,map_sum]
  apply congrArg (fun v : KernelQuotientL2 => (24:ℂ)⁻¹ • v)
  simp_rw [kernelSourcePullback_comp,←map_mul]
  have he : ∀q : levelTwo ⧸ levelThreeInTwo,
      kernelSourcePullback (rationalLift (sourceRationalSection q*r)) F=
      kernelSourcePullback (rationalLift (sourceRationalSection (q*rationalQuotient r))) F :=
    fun q => kernelSourcePullback_rational_eq _ _ (sourceSection_mul_reduction q r) F
  simp_rw [he]
  exact Function.Bijective.sum_comp (Group.mulRight_bijective (rationalQuotient r))
    (fun q => kernelSourcePullback (rationalLift (sourceRationalSection q)) F)

lemma kernelSourceProjection_fixed (F : KernelQuotientL2)
    (hF : ∀r : SL(2,ℤ),kernelSourcePullback (rationalLift r) F=F) :
    kernelSourceProjection F=F := by
  rw [kernelSourceProjection_apply]
  simp only [hF,Finset.sum_const,Finset.card_univ]
  have hc : Fintype.card (levelTwo ⧸ levelThreeInTwo)=24 := by
    simpa only [Nat.card_eq_fintype_card] using sourceQuotient_card
  rw [hc]
  rw [←Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  norm_num

lemma kernelSourceProjection_idempotent (F : KernelQuotientL2) :
    kernelSourceProjection (kernelSourceProjection F)=kernelSourceProjection F :=
  kernelSourceProjection_fixed _ (fun r => kernelSourcePullback_projection r F)

end CubicEisenstein

namespace CubicKubota
open ActualEisensteinCubic

def sourceLevelInclusion : levelThree→*levelTwo where
  toFun n := ⟨(n:SL(2,ActualEisensteinCubic.O)),levelThree_le_levelTwo n.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

lemma sourceLevelInclusion_character (n : levelThree) :
    levelTwoComplexCharacter (sourceLevelInclusion n)=complexCharacter n :=
  levelTwoComplexCharacter_restrict n

lemma sourceSection_factor (q : levelTwo ⧸ levelThreeInTwo) (g : levelTwo) :
    ∃n : levelThree,
      rationalLift (sourceRationalSection q)*g=
        sourceLevelInclusion n*rationalLift (sourceRationalSection
          (q*QuotientGroup.mk' levelThreeInTwo g)) ∧
      complexCharacter n=levelTwoComplexCharacter g := by
  let r := sourceRationalSection q
  let s := sourceRationalSection (q*QuotientGroup.mk' levelThreeInTwo g)
  let n2 : levelTwo := rationalLift r*g*(rationalLift s)⁻¹
  have hn2 : n2∈levelThreeInTwo := by
    apply (QuotientGroup.eq_one_iff (N:=levelThreeInTwo) n2).mp
    change QuotientGroup.mk' levelThreeInTwo (rationalLift r*g*(rationalLift s)⁻¹)=1
    rw [map_mul,map_mul,map_inv]
    change rationalQuotient r * QuotientGroup.mk' levelThreeInTwo g *
      (rationalQuotient s)⁻¹=1
    rw [sourceRationalSection_spec,sourceRationalSection_spec,mul_inv_cancel]
  let n : levelThree := ⟨(n2:SL(2,ActualEisensteinCubic.O)),hn2⟩
  refine ⟨n,?_,?_⟩
  · change rationalLift r*g=(rationalLift r*g*(rationalLift s)⁻¹)*rationalLift s
    group
  · rw [←levelTwoComplexCharacter_restrict n]
    change levelTwoComplexCharacter (rationalLift r*g*(rationalLift s)⁻¹)=_
    rw [map_mul,map_mul,←map_inv rationalLift]
    change levelTwoComplexCharacter (rationalLift r)*levelTwoComplexCharacter g*
      levelTwoComplexCharacter (rationalLift s⁻¹)=_
    rw [levelTwoComplexCharacter_rationalLift,levelTwoComplexCharacter_rationalLift,one_mul,mul_one]
end CubicKubota

namespace CubicEisenstein
open CubicKubota

theorem kernelSourceProjection_covariance (F : KernelQuotientL2)
    (hF : ∀n : levelThree,kernelSourcePullback (sourceLevelInclusion n) F=
      complexCharacter n • F) (g : levelTwo) :
    kernelSourcePullback g (kernelSourceProjection F)=
      levelTwoComplexCharacter g • kernelSourceProjection F := by
  rw [kernelSourceProjection_apply,map_smul,map_sum]
  simp_rw [kernelSourcePullback_comp]
  have he : ∀q : levelTwo ⧸ levelThreeInTwo,
      kernelSourcePullback (rationalLift (sourceRationalSection q)*g) F=
      levelTwoComplexCharacter g •
        kernelSourcePullback (rationalLift (sourceRationalSection
          (q*QuotientGroup.mk' levelThreeInTwo g))) F := by
    intro q
    obtain ⟨n,hn,hc⟩ := sourceSection_factor q g
    rw [hn,←kernelSourcePullback_comp,hF,map_smul,hc]
  simp_rw [he]
  rw [←Finset.smul_sum]
  rw [Function.Bijective.sum_comp
    (Group.mulRight_bijective (QuotientGroup.mk' levelThreeInTwo g))
    (fun q => kernelSourcePullback (rationalLift (sourceRationalSection q)) F)]
  rw [smul_comm]

lemma kernelSourceProjection_ae_eq (F : KernelQuotientL2) :
    kernelSourceProjection F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun x => (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
        F (kernelSourceAction (rationalLift (sourceRationalSection q)) x) := by
  rw [kernelSourceProjection_apply]
  have hsum := (Lp.coeFn_finsetSum Finset.univ
    (fun q : levelTwo ⧸ levelThreeInTwo =>
      kernelSourcePullback (rationalLift (sourceRationalSection q)) F)).trans
    (eventuallyEq_sum (fun q _ =>
      kernelSourcePullback_ae_eq (rationalLift (sourceRationalSection q)) F))
  filter_upwards [(Lp.coeFn_smul (24:ℂ)⁻¹ _).trans (hsum.const_smul (24:ℂ)⁻¹)] with x hx
  simpa only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul] using hx

lemma kernelSourceProjection_representative (F : KernelQuotientL2)
    (f : SourceKernelQuotient→ℂ)
    (hf : F=ᵐ[integralQuotientVolume globalKubotaKernel] f) :
    kernelSourceProjection F=ᵐ[integralQuotientVolume globalKubotaKernel]
      fun x => (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
        f (kernelSourceAction (rationalLift (sourceRationalSection q)) x) := by
  apply (kernelSourceProjection_ae_eq F).trans
  have hh : (∑q : levelTwo ⧸ levelThreeInTwo, fun x =>
      F (kernelSourceAction (rationalLift (sourceRationalSection q)) x))
      =ᵐ[integralQuotientVolume globalKubotaKernel]
      (∑q : levelTwo ⧸ levelThreeInTwo, fun x =>
      f (kernelSourceAction (rationalLift (sourceRationalSection q)) x)) :=
    eventuallyEq_sum (fun q _ =>
      (kernelSourceAction_measurePreserving (rationalLift (sourceRationalSection q))).quasiMeasurePreserving.ae_eq_comp hf)
  filter_upwards [hh.const_smul (24:ℂ)⁻¹] with x hx
  simpa only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul] using hx

lemma kernelSourceProjection_hyperbolic_average (f : SourceKernelQuotient→ℂ) (w : HyperbolicSpace) :
    (24:ℂ)⁻¹ * ∑q : levelTwo ⧸ levelThreeInTwo,
      f (kernelSourceAction (rationalLift (sourceRationalSection q))
        (integralOrbitProjection globalKubotaKernel w)) =
    sourceProjection (f ∘ integralOrbitProjection globalKubotaKernel) w := rfl

end CubicEisenstein
end

open scoped Classical

namespace CubicEisenstein
open CubicKubota

lemma kernelSourceAction_level (n : levelThree) :
    kernelSourceAction (sourceLevelInclusion n)=kernelLevelAction n := rfl

lemma kernelSourcePullback_level (n : levelThree) :
    kernelSourcePullback (sourceLevelInclusion n)=kernelLevelPullback n := rfl

theorem kernelSourceProjection_covariance_of_level (F : KernelQuotientL2)
    (hF : ∀n : levelThree,kernelLevelPullback n F=complexCharacter n • F) (g : levelTwo) :
    kernelSourcePullback g (kernelSourceProjection F)=
      levelTwoComplexCharacter g • kernelSourceProjection F := by
  apply kernelSourceProjection_covariance F
  intro n
  rw [kernelSourcePullback_level]
  exact hF n

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
open EisensteinSchwartzPoisson ActualEisensteinCubic ConcreteTraceCRT Module

def periodVector : (Fin 2 → ℝ) ≃L[ℝ] ℂ := periodBasis.equivFunL.symm

lemma periodVector_apply (x : Fin 2 → ℝ) :
    periodVector x = 3 * ((x 0 : ℂ) + (x 1 : ℂ) * omega3) := by
  change periodBasis.equivFun.symm x = _
  rw [Basis.equivFun_symm_apply, Fin.sum_univ_two, periodBasis_zero, periodBasis_one]
  simp only [Complex.real_smul]
  ring

def periodTorus (z : ℂ) : UnitAddTorus (Fin 2) :=
  fun i => (periodBasis.equivFunL z i : UnitAddCircle)

lemma periodTorus_periodVector (x : Fin 2 → ℝ) :
    periodTorus (periodVector x) = fun i => (x i : UnitAddCircle) := by
  change (fun i => ((periodBasis.equivFunL (periodBasis.equivFunL.symm x)) i : UnitAddCircle)) = _
  rw [periodBasis.equivFunL.apply_symm_apply]

def periodFrequencyEquiv : (Fin 2 → ℤ) ≃ ActualEisensteinCubic.O :=
  (finTwoArrowEquiv ℤ).trans dualFrequencyEquiv

lemma periodFrequencyEquiv_apply (n : Fin 2 → ℤ) :
    periodFrequencyEquiv n = dualFrequencyEquiv (n 0, n 1) := rfl

lemma periodVector_character (n : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    ShortDraftTrace.breveE (cuspFrequency (periodFrequencyEquiv n) * periodVector x) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((n 0 : ℂ) * (x 0 : ℂ) + (n 1 : ℂ) * (x 1 : ℂ))) := by
  have hlam : eisLam ≠ 0 := by
    exact eisLam_ne_zero
  have harg : cuspFrequency (periodFrequencyEquiv n) * periodVector x =
      (eisEmbedding (dualFrequencyEquiv (n 0,n 1)) *
        ((x 0 : ℂ) + (x 1 : ℂ) * omega3)) / eisLam := by
    rw [cuspFrequency, periodVector_apply, periodFrequencyEquiv_apply]
    field_simp
  rw [harg, ←paperE, paperE_eq_exp, dualFrequencyEquiv_coordinates]
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hw : omega3.re = -(1/2:ℝ) := by norm_num [omega3]
  congr 1
  simp only [complexPoint, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, hw, omega3_im]
  push_cast
  field_simp
  ring

lemma periodTorus_mFourier (n : Fin 2 → ℤ) (z : ℂ) :
    UnitAddTorus.mFourier n (periodTorus z) =
      ShortDraftTrace.breveE (cuspFrequency (periodFrequencyEquiv n) * z) := by
  obtain ⟨x, rfl⟩ := periodVector.surjective z
  rw [periodTorus_periodVector, periodVector_character]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [←Complex.exp_add]
  congr 1
  ring

lemma periodFrequencyEquiv_neg (n : Fin 2 → ℤ) :
    periodFrequencyEquiv (-n) = -periodFrequencyEquiv n := by
  apply eisEmbedding_injective
  change eisEmbedding (ActualEisensteinCoordinates.eval (-n 0 + -n 1) (-n 0)) =
    eisEmbedding (-ActualEisensteinCoordinates.eval (n 0 + n 1) (n 0))
  rw [map_neg, eisEmbedding_eval, eisEmbedding_eval]
  push_cast
  ring

lemma cuspFrequency_neg (h : ActualEisensteinCubic.O) : cuspFrequency (-h) = -cuspFrequency h := by
  simp only [cuspFrequency, map_neg, neg_div]

lemma periodVector_eq_lattice (x : Fin 2 → ℝ) :
    periodVector x = eisensteinLatticeMap 3 (by norm_num) (Complex.measurableEquivPi.symm x) := by
  rw [periodVector_apply]
  simp [eisensteinLatticeMap, Complex.measurableEquivPi_symm_apply, mul_comm]

lemma periodVector_map_volume :
    Measure.map periodVector volume = ENNReal.ofReal (2/(9*Real.sqrt 3)) • volume := by
  have heq : (periodVector : (Fin 2 → ℝ) → ℂ) =
      eisensteinLatticeMap 3 (by norm_num) ∘ Complex.measurableEquivPi.symm :=
    funext periodVector_eq_lattice
  rw [heq, ←Measure.map_map (eisensteinLatticeMap 3 (by norm_num)).continuous.measurable
    Complex.measurableEquivPi.symm.measurable, Complex.volume_preserving_equiv_pi.symm.map_eq]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (eisensteinLatticeMap 3 (by norm_num)).toLinearEquiv.isUnit_det'.ne_zero
  change Measure.map (eisensteinLatticeMap 3 (by norm_num)) volume =
    ENNReal.ofReal (inverseJacobian (eisensteinLatticeMap 3 (by norm_num))) • volume at hmap
  rw [hmap, eisenstein_inverseJacobian]
  norm_num [mul_comm]

def periodCube : Set (Fin 2 → ℝ) := {x | ∀i, x i ∈ Set.Ico 0 1}

lemma periodVector_preimage_domain : periodVector ⁻¹' periodDomain = periodCube := by
  ext x
  change (∀i, periodBasis.repr (periodBasis.equivFun.symm x) i ∈ Set.Ico 0 1) ↔ _
  simp only [←Basis.equivFun_apply, periodBasis.equivFun.apply_symm_apply]
  rfl

lemma periodDomain_integral_coordinates (f : ℂ → ℂ) :
    (2/(9*Real.sqrt 3):ℝ) • (∫z in periodDomain, f z) =
      ∫x in periodCube, f (periodVector x) := by
  have h := periodVector.toHomeomorph.toMeasurableEquiv.measurableEmbedding.setIntegral_map
    f periodDomain («μ» := (volume : Measure (Fin 2 → ℝ)))
  change (∫z in periodDomain, f z ∂Measure.map periodVector volume) =
    ∫x in periodVector ⁻¹' periodDomain, f (periodVector x) at h
  rw [periodVector_map_volume, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), periodVector_preimage_domain] at h
  exact h

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma periodCube_ae_Ioc : periodCube =ᵐ[volume]
    {x : Fin 2 → ℝ | ∀i, x i ∈ Set.Ioc 0 1} := by
  rw [volume_pi]
  have h := Measure.ae_eq_set_pi («μ» := fun _ : Fin 2 => (volume : Measure ℝ))
    (I := Set.univ) (s := fun _ => Set.Ico (0:ℝ) 1) (t := fun _ => Set.Ioc (0:ℝ) 1)
    (fun _ _ => Ico_ae_eq_Ioc)
  simpa only [Set.pi, Set.mem_univ, forall_true_left, periodCube] using h

lemma periodTorus_integral (f : UnitAddTorus (Fin 2) → ℂ) :
    (∫t, f t) = (2/(9*Real.sqrt 3):ℝ) • (∫z in periodDomain, f (periodTorus z)) := by
  rw [periodDomain_integral_coordinates, UnitAddTorus.integral_preimage f (fun _ => 0)]
  simp only [zero_add, periodTorus_periodVector]
  exact setIntegral_congr_set periodCube_ae_Ioc.symm

lemma periodTorus_fourierCoeff (f : UnitAddTorus (Fin 2) → ℂ) (n : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff f n = (2/(9*Real.sqrt 3):ℝ) •
      (∫z in periodDomain, f (periodTorus z) *
        ShortDraftTrace.breveE (-cuspFrequency (periodFrequencyEquiv n)*z)) := by
  rw [UnitAddTorus.mFourierCoeff, periodTorus_integral]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [periodTorus_mFourier, periodFrequencyEquiv_neg, cuspFrequency_neg]
    exact mul_comm _ _)

lemma periodTorus_L2_ext (F G : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2))))
    (h : ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain, F (periodTorus z)*ShortDraftTrace.breveE (-cuspFrequency h*z)) =
      ∫z in periodDomain, G (periodTorus z)*ShortDraftTrace.breveE (-cuspFrequency h*z)) : F=G := by
  apply UnitAddTorus.mFourierBasis.repr.injective
  ext n
  rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierBasis_repr,
    periodTorus_fourierCoeff, periodTorus_fourierCoeff, h]

end CubicEisenstein

end

end OAI
