import OAI.NumberTheory.DirichletL.GaussSum.BranchScaling
import OAI.NumberTheory.DirichletL.CubicSieve.RadialWindows

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
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)

def initialRayMass : ℝ := ∑ ray : SecondRayIndex,‖secondRayCoefficient ray‖

lemma initialRayMass_nonneg : 0 ≤ initialRayMass := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem initial_complementary_harmonic (F : Finset ι) (U : ℝ) :
    (∑ R ∈ boundedPrimeSupports p F U,1/primeProductNorm p R) ≤
      128*Real.exp 1*(normLogBin U+1 : ℝ) := by
  let f : Finset ι → Ideal O := fun R => ∏ i ∈ R,Ideal.span {p i}
  have hf : Function.Injective f := FirstCauchyArithmetic.family_product_injective _ hinj
  let T := (boundedPrimeSupports p F U).image f
  have hT : ∀ I ∈ T,I ≠ (0 : Ideal O) := by
    intro I hI
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hI
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))
  have hU : ∀ I ∈ T,(Ideal.absNorm I : ℝ) ≤ U := by
    intro I hI
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hI
    rw [←primeProductNorm_eq_ideal_norm p R]
    exact (Finset.mem_filter.mp hR).2
  have hb := descent_ideal_inverse_sum T U hT hU
  rw [Finset.sum_image (fun R _ S _ h => hf h)] at hb
  simpa only [f,←primeProductNorm_eq_ideal_norm p] using hb

include hinj in

theorem initial_harmonic_aggregation (F : Finset ι) (U K D : ℝ) (hD : 0 ≤ D)
    (a : SecondRayIndex → Finset ι → SecondLogIndex → ℝ)
    (ha : ∀ ray, ∀ R ∈ boundedPrimeSupports p F U, ∀ j ∈ secondLogBinBox U K,
      a ray R j ≤ D/primeProductNorm p R*‖secondRayCoefficient ray‖) :
    (∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F U,
      ∑ j ∈ secondLogBinBox U K,a ray R j) ≤
    D*initialRayMass*((secondLogBinBox U K).card : ℝ)*
      (128*Real.exp 1*(normLogBin U+1 : ℝ)) := by
  let B := secondLogBinBox U K
  let C := 128*Real.exp 1*(normLogBin U+1 : ℝ)
  have hinner (ray : SecondRayIndex) :
      (∑ R ∈ boundedPrimeSupports p F U,∑ j ∈ B,a ray R j) ≤
      (D*‖secondRayCoefficient ray‖*(B.card : ℝ))*C := by
    calc
      _ ≤ ∑ R ∈ boundedPrimeSupports p F U,∑ _j ∈ B,
          D/primeProductNorm p R*‖secondRayCoefficient ray‖ := by
        apply Finset.sum_le_sum
        intro R hR
        exact Finset.sum_le_sum (fun j hj => ha ray R hR j hj)
      _ = (D*‖secondRayCoefficient ray‖*(B.card : ℝ))*
          ∑ R ∈ boundedPrimeSupports p F U,1/primeProductNorm p R := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R hR
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (initial_complementary_harmonic p hinj F U)
        (by positivity)
  calc
    _ ≤ ∑ ray : SecondRayIndex,(D*‖secondRayCoefficient ray‖*(B.card : ℝ))*C :=
      Finset.sum_le_sum (fun ray _ => hinner ray)
    _ = _ := by
      unfold initialRayMass
      simp only [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hray
      ring

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcretePrimeRowBridge (idealGenerator)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def sourceGlobalBlock (b:CubeCoordinates ι) (C D:Finset ι) : GlobalCubeBlock ι :=
  ⟨b.swap,C,D⟩

lemma cube_swap_support (b:CubeCoordinates ι) : b.swap.support=b.support := by
  simp only [CubeCoordinates.swap,CubeCoordinates.support,Finset.union_comm]

omit [DecidableEq ι] in
lemma cube_swap_sum (b:CubeCoordinates ι) :
    (fun i=>b.swap.leftExponent i+b.swap.rightExponent i)=
      (fun i=>b.leftExponent i+b.rightExponent i) := by
  funext i
  exact Nat.add_comm _ _

lemma orientedCubeFirstBlock_single_source
    (pool:Finset ι) (b:CubeCoordinates ι) (C D:Finset ι) (I:Ideal O) (h:O)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) :
    orientedCubeFirstBlock p hp hcop hg pool (sourceGlobalBlock b C D) {(I,h)} (fun _=>1)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell =
    (primeProductNorm p D:ℂ)⁻¹ *
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (originalLabelColumn p hg b.support b.leftBit b.rightBit true
          (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p
            (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)) S)))
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) C) (idealGenerator I))
        (originalLabelColumn p hg b.support b.leftBit b.rightBit false
          (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p
            (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) S)))
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) C) (idealGenerator I))
        W V₁ V₂ (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
          (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  have hl : b.swap.leftBit=b.rightBit := rfl
  have hr : b.swap.rightBit=b.leftBit := rfl
  have hst : b.swap.sideDivisor true=b.rightDivisor := rfl
  have hsf : b.swap.sideDivisor false=b.leftDivisor := rfl
  simp only [orientedCubeFirstBlock,sourceGlobalBlock,globalCubePool,globalCubeColumnScale,
    globalFirstBlockColumnScale,GlobalCubeBlock.withCommon,cube_swap_support,cube_swap_sum,
    hl,hr,hst,hsf,Finset.sum_singleton,one_mul]

lemma canonical_log_kernel
    (pool:Finset ι) (b:CubeCoordinates ι) (hb:b.Admissible) (C:Finset ι)
    (hCB:Disjoint C b.support) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f d h:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell) :
    actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun U=>g₁ (columnLog p ell U)))
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun U=>g₂ (columnLog p ell U)))
      W (fun _=>1) (fun _=>1) 1 1 K d h =
    actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (originalLabelColumn p hg b.support b.leftBit b.rightBit true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p
          (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)) S))) (∏i∈C,p i) f)
      (originalLabelColumn p hg b.support b.leftBit b.rightBit false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p
          (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) S))) (∏i∈C,p i) f)
      W (fun _=>1) (fun _=>1) (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
        (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) K d h := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  have hdis (S:Finset ι) (hS:S∈(pool\(b.support∪C)).powerset) :
      Disjoint S C ∧ Disjoint S b.support := by
    constructor <;> apply Finset.disjoint_left.mpr
    · intro i hi hx
      exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hi)).2 (Finset.mem_union_right _ hx)
    · intro i hi hx
      exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hi)).2 (Finset.mem_union_left _ hx)
  have h₁:=canonicalCubeResidual_log p hp hg b hb C N hCB (hdis N hN).1 (hdis N hN).2 true Ψ₁ m₁ f g₁ ell hell
  have h₂:=canonicalCubeResidual_log p hp hg b hb C P hCB (hdis P hP).1 (hdis P hP).2 false Ψ₂ m₂ f g₂ ell hell
  simp only [CubeCoordinates.sideDivisor,Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true] at h₁ h₂
  simp only [threeGaussRowFactor,h₁,h₂]

def commonProductUnit (C:Finset ι) : Oˣ :=
  Classical.choose (exists_label_unit (∏i∈C,p i) (∏i∈C,Ideal.span {p i})
    (FiniteGaussPhase.span_finset_prod C p))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma commonProductUnit_spec (C:Finset ι) :
    (∏i∈C,p i)=(commonProductUnit p C:O)*primeSubsetGenerator (fun i=>Ideal.span {p i}) C :=
  Classical.choose_spec (exists_label_unit (∏i∈C,p i) (∏i∈C,Ideal.span {p i})
    (FiniteGaussPhase.span_finset_prod C p))

def commonCubePhase (b:CubeCoordinates ι) (C:Finset ι) : ℂ :=
  blockRow p hg (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
    (fun i=>(conductorExponent (parity (b.leftExponent i+b.rightExponent i)) (b.leftBit i) (b.rightBit i)).val)
    ((commonProductUnit p C:O)^2)

lemma commonCubePhase_norm (b:CubeCoordinates ι) (C:Finset ι) :
    ‖commonCubePhase p hg b C‖=1 :=
  commonUnitPhase_norm p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit (commonProductUnit p C)

theorem canonicalSource_mode_attachment
    (pool:Finset ι) (b:CubeCoordinates ι) (hb:b.Admissible) (C D:Finset ι)
    (hCB:Disjoint C b.support) (I:Ideal O) (h:O)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    ((UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ))*
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ (idealGenerator I) (fun U=>g₁ (columnLog p ell U)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ (idealGenerator I) (fun U=>g₂ (columnLog p ell U)))
        W (fun _=>1) (fun _=>1) 1 1 K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h =
    (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*commonCubePhase p hg b C*
      orientedCubeFirstBlock p hp hcop hg pool (sourceGlobalBlock b C D)
        {(I,(commonProductUnit p C:O)^2*h)} (fun _=>1) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  have hFB:Disjoint (pool\(b.support∪C)) b.support :=
    Finset.disjoint_left.mpr (fun i hi hiB=>(Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB))
  rw [canonical_log_kernel p hp hcop hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ (idealGenerator I) _ h g₁ g₂ W K ell hell]
  rw [actualFirstKernel_insert_windows p hp hcop hg _ _ _ _ _ Ψ₁ Ψ₂ m₁ m₂ _ _
    g₁ g₂ W V₁ V₂ _ _ K _ h hV₁ hV₂]
  rw [commonProductUnit_spec p C]
  rw [actualFirstKernel_common_unit p hp hcop hg _ _ hFB _ _ _ _ _ W V₁ V₂ _ _ K
    (commonProductUnit p C) _ (idealGenerator I) _ h]
  rw [orientedCubeFirstBlock_single_source]
  unfold commonCubePhase
  ring

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcretePrimeRowBridge (idealGenerator)
open ConcreteTraceCRT (eisEmbedding)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

lemma orientedCubeFirstBlock_eq_sum_single (pool:Finset ι) (b:GlobalCubeBlock ι)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) :
    orientedCubeFirstBlock p hp hcop hg pool b s a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell=
      ∑x∈s,a x*orientedCubeFirstBlock p hp hcop hg pool b {x} (fun _=>1)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  unfold orientedCubeFirstBlock
  simp only [Finset.sum_singleton,one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def rawCanonicalBlock (pool:Finset ι) (b:GlobalCubeBlock ι)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (K ell:ℝ) : ℂ :=
  let q:=b.cube.swap
  ∑x∈s,a x*((UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)/
    (primeProductNorm p b.firstDivisor:ℂ))*
    actualFirstKernel p hp hcop hg (pool\(q.support∪b.common)) q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit
      (canonicalCubeResidual p hg q b.common true Ψ₁ m₁ (idealGenerator x.1)
        (fun U=>g₁ (columnLog p ell U)))
      (canonicalCubeResidual p hg q b.common false Ψ₂ m₂ (idealGenerator x.1)
        (fun U=>g₂ (columnLog p ell U)))
      W (fun _=>1) (fun _=>1) 1 1 K
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) b.firstDivisor) x.2

def sourceFrequencyEquiv (C:Finset ι) : (Ideal O×O)≃(Ideal O×O) :=
  Equiv.prodCongr (Equiv.refl _) (unitSquareRowEquiv (commonProductUnit p C))

def sourceRotatedCoefficient (b:GlobalCubeBlock ι) (a:Ideal O×O→ℂ) (x:Ideal O×O) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)*
    commonCubePhase p hg b.cube.swap b.common*a ((sourceFrequencyEquiv p b.common).symm x)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceFrequencyEquiv_label (C:Finset ι) (x:Ideal O×O) :
    (sourceFrequencyEquiv p C x).1=x.1 := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceFrequencyEquiv_row_norm (C:Finset ι) (x:Ideal O×O) :
    ‖eisEmbedding (sourceFrequencyEquiv p C x).2‖=‖eisEmbedding x.2‖ := by
  have hr : (sourceFrequencyEquiv p C x).2=(commonProductUnit p C:O)^2*x.2 := rfl
  rw [hr,map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,one_mul]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceFrequencyEquiv_row_ne_zero (C:Finset ι) (x:Ideal O×O) (hx:x.2≠0) :
    (sourceFrequencyEquiv p C x).2≠0 := by
  change (commonProductUnit p C:O)^2*x.2≠0
  exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hx

lemma sourceRotatedCoefficient_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (b:GlobalCubeBlock ι) (a:Ideal O×O→ℂ) (x:Ideal O×O) :
    ‖sourceRotatedCoefficient p hg b a x‖=‖a ((sourceFrequencyEquiv p b.common).symm x)‖ := by
  have hprime (i:ι):Prime (Ideal.span {p i}):=
    Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have hμ : ‖(UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)‖=1 := by
    have hh:=congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj b.firstDivisor)
    simp only [norm_mul,norm_one] at hh
    change ‖FirstCauchyArithmetic.supportMobius (fun i=>Ideal.span {p i}) b.firstDivisor‖=1
    nlinarith [norm_nonneg (FirstCauchyArithmetic.supportMobius (fun i=>Ideal.span {p i}) b.firstDivisor)]
  simp only [sourceRotatedCoefficient,norm_mul,hμ,commonCubePhase_norm,one_mul]

theorem rawCanonicalBlock_eq_oriented
    (pool:Finset ι) (b:GlobalCubeBlock ι) (hb:GlobalCubeAdmissible b)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    rawCanonicalBlock p hp hcop hg pool b s a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell =
    orientedCubeFirstBlock p hp hcop hg pool b (s.image (sourceFrequencyEquiv p b.common))
      (sourceRotatedCoefficient p hg b a) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  have hq:b.cube.swap.Admissible := by
    constructor
    · change b.cube.rightDivisor⊆b.cube.swap.support
      rw [cube_swap_support]
      exact hb.1.2
    · change b.cube.leftDivisor⊆b.cube.swap.support
      rw [cube_swap_support]
      exact hb.1.1
  have hc:Disjoint b.common b.cube.swap.support := by
    rw [cube_swap_support]
    exact hb.2.1
  have hback:sourceGlobalBlock b.cube.swap b.common b.firstDivisor=b := by
    cases b
    simp only [sourceGlobalBlock,CubeCoordinates.swap_swap]
  rw [orientedCubeFirstBlock_eq_sum_single,Finset.sum_image]
  · unfold rawCanonicalBlock
    dsimp only
    apply Finset.sum_congr rfl
    intro x hx
    have hmode:=canonicalSource_mode_attachment p hp hcop hg pool b.cube.swap hq b.common b.firstDivisor hc
      x.1 x.2 Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell hell hV₁ hV₂
    rw [hback] at hmode
    have hidx : (x.1,(commonProductUnit p b.common:O)^2*x.2)=sourceFrequencyEquiv p b.common x := rfl
    rw [hidx] at hmode
    simp only [sourceRotatedCoefficient,Equiv.symm_apply_apply]
    calc
      _ = a x*((UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)/
          (primeProductNorm p b.firstDivisor:ℂ)*
          actualFirstKernel p hp hcop hg (pool\(b.cube.swap.support∪b.common)) b.cube.swap.support
            (fun i=>b.cube.swap.leftExponent i+b.cube.swap.rightExponent i) b.cube.swap.leftBit b.cube.swap.rightBit
            (canonicalCubeResidual p hg b.cube.swap b.common true Ψ₁ m₁ (idealGenerator x.1) (fun U=>g₁ (columnLog p ell U)))
            (canonicalCubeResidual p hg b.cube.swap b.common false Ψ₂ m₂ (idealGenerator x.1) (fun U=>g₂ (columnLog p ell U)))
            W (fun _=>1) (fun _=>1) 1 1 K (primeSubsetGenerator (fun i=>Ideal.span {p i}) b.firstDivisor) x.2) := by ring
      _ = _ := by rw [hmode];ring
  · exact fun x hx y hy hxy=>(sourceFrequencyEquiv p b.common).injective hxy

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem rawCanonicalTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (hWin₁ : ∀ t,g₁ t≠0 → V₁ t=1) (hWin₂ : ∀ t,g₂ t≠0 → V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H U : ℝ),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,htransfer⟩ :=
    orientedTwoPassage_quantitative W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂ hg₁ hg₂ hV₁ hV₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  let s' := fun b:GlobalCubeBlock ι=>(s b).image (sourceFrequencyEquiv p b.common)
  let a' := fun b:GlobalCubeBlock ι=>sourceRotatedCoefficient p hg b (a b)
  have heq : (∑b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell)=
      ∑b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s' b) (a' b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
    apply Finset.sum_congr rfl
    intro b hb
    exact rawCanonicalBlock_eq_oriented p hp hcop hg pool b (hadm b hb) (s b) (a b)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell hell hWin₁ hWin₂
  rw [heq]
  apply htransfer p hp hinj hcop hg hc hpr pool blocks s' a' w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    dsimp only [a']
    rw [sourceRotatedCoefficient_norm p hg hinj,Equiv.symm_apply_apply]
    exact ha b hb y hy
  · exact hadm
  · exact hb₁
  · exact hb₂
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_label]
    exact hsf b hb y hy
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact sourceFrequencyEquiv_row_ne_zero p b.common y (hs0 b hb y hy)
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_label]
    exact hf b hb y hy
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_row_norm]
    exact hh b hb y hy

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

theorem padded_orientedCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (Ksrc K ell B F Ymax : ℝ),
      0<Ksrc → 0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      (Ksrc/K)*C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_full_uniform_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ Ksrc K ell B F Ymax hKsrc hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
  by_cases hempty : blocks=∅
  · subst blocks
    simp only [Finset.sum_empty,mul_zero,norm_zero,Real.sqrt_zero,le_refl]
  have hne : blocks.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b*globalCubeCoefficient p K ell B F true b
  have hv (b) (hb : b∈blocks) : 0≤v b := mul_nonneg (hw b hb)
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hE₁ (b) : 0≤E₁ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hE₂ (b) : 0≤E₂ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hden : 0<ell*B^2*F := by positivity
  have hYmax0 : 0≤Ymax := by
    obtain ⟨b,hb⟩ := hne
    exact (globalPooledRowScale_pos K ell B F hK hell hB hF _).le.trans (hYmax b hb)
  have hpref : 0≤(Ksrc/K)*C*Ymax^deltaLoss := mul_nonneg (mul_nonneg (div_nonneg hKsrc.le hK.le) hC) (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      ((Ksrc/K)*C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hD := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hswapD := FirstPassCubeLabels.dilationLabel_swap p b.cube.support
      (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ Ksrc hKsrc (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) (primeSubsetGenerator_ne_zero _ _)
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hsf b hb) (hs0 b hb) (by simpa only [hswapD] using hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    rw [firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit true,
      firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit false,
      FirstPassCubeLabels.cubeActiveSupport_swap b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit] at hh
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hscl' : (ell*B^2*F)⁻¹*((Ksrc/primeProductNorm p b.firstDivisor)/
        ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
          (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) ≤
        (Ksrc/K)*globalCubeCoefficient p K ell B F true b := by
      have hKratio : Ksrc=(Ksrc/K)*K := by field_simp
      calc
        _ = (Ksrc/K)*((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)) := by
          conv_lhs => rw [hKratio]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscl (div_nonneg hKsrc.le hK.le)
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [orientedCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hD.le,←mul_assoc]
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((Ksrc/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ ((Ksrc/K)*globalCubeCoefficient p K ell B F true b)*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl'
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (mul_nonneg (div_nonneg hKsrc.le hK.le) (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _))
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,((Ksrc/K)*C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = ((Ksrc/K)*C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = ((Ksrc/K)*C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ ((Ksrc/K)*C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end SecondPassArithmetic

end

end OAI
