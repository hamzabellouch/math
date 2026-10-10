import OAI.NumberTheory.DirichletL.Eisenstein.FundamentalDomain

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

namespace CompletedGauss
open ActualEisensteinCubic

theorem largeCubeCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (H₀ : ℝ) (B : Ideal O),B≠⊥ →
      ‖largeCubeCoefficient H₀ B‖ ≤ C*(Ideal.absNorm B : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  exact ⟨C,hC,fun H₀ B hB => (largeCubeCoefficient_norm_le H₀ B).trans (hbound B hB)⟩

end CompletedGauss

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def globalRowScaleFloor (K ell B F M : ℝ) : ℝ :=
  ell^2*B^2*F^2/(K*(ell*Real.exp M)^2)

theorem globalRowScaleFloor_pos (K ell B F M : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) : 0 < globalRowScaleFloor K ell B F M := by
  unfold globalRowScaleFloor
  positivity

theorem globalNormCaps_antitone_row (ell B Y₀ Y₁ M H : ℝ) (hY₀ : 0 < Y₀)
    (hY : Y₀ ≤ Y₁) (hH : 0 ≤ H) :
    ∀ i,globalNormCaps ell B Y₁ M H i ≤ globalNormCaps ell B Y₀ M H i := by
  have hc : ⌈H*(ell*Real.exp M)^2/Y₁⌉₊ ≤ ⌈H*(ell*Real.exp M)^2/Y₀⌉₊ :=
    Nat.ceil_mono (div_le_div_of_nonneg_left (by positivity) hY₀ hY)
  have hc' : (⌈H*(ell*Real.exp M)^2/Y₁⌉₊ : ℝ) ≤ ⌈H*(ell*Real.exp M)^2/Y₀⌉₊ := by exact_mod_cast hc
  intro i
  fin_cases i <;> simp [globalNormCaps]
  gcongr

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalRowScaleFloor_le_pooled (K ell B F M : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (side : Bool) (x : GlobalSecondData ι)
    (hx : GlobalSecondAdmissible x) (hk : x.source.frequency ≠ 0)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    globalRowScaleFloor K ell B F M ≤ globalPooledRowScale K ell B F (globalScaleIndex p side x) := by
  let j := globalScaleIndex p side x
  have hC : globalLogRep j 1 ≤ ell*Real.exp M :=
    (globalScaleIndex_bounds p hp side x hk 1).1.trans (globalSupported_small_norms p hp ell M hell side x hx hs).2.1
  have hJ := globalPooled_J_bound p hp B hB side x hk hb₁ hb₂
  have hcpos := globalLogRep_pos j 1
  have hjpos := globalLogRep_pos j 4
  have hd := globalLogRep_ge_one j 5
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  unfold globalRowScaleFloor globalPooledRowScale
  calc
    ell^2*B^2*F^2/(K*(ell*Real.exp M)^2) = ell^2*B^4*F^2/(K*(ell*Real.exp M)^2*B^2) := by field_simp
    _ ≤ Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4) := by
      apply div_le_div₀ (by positivity)
      · calc
          ell^2*B^4*F^2 = 1*ell^2*B^4*F^2*1 := by ring
          _ ≤ _ := by gcongr
      · positivity
      · gcongr

include hp in

theorem globalScaleIndex_mem_uniform_box (K ell B F M H : ℝ)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F) (hH : 0 ≤ H)
    (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk0 : x.source.frequency ≠ 0)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      (globalPooledRowScale K ell B F (globalScaleIndex p side x)) M H x.source.sourceCommon x.source.divisor) :
    globalScaleIndex p side x ∈
      globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) := by
  have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalScaleIndex p side x)
  have hfloor := globalRowScaleFloor_pos K ell B F M hK hell hB hF
  have hlower := globalRowScaleFloor_le_pooled p hp K ell B F M hK hell hB hF side x hx hk0 hs hb₁ hb₂
  have hcaps := globalScaleVector_le_caps p hp ell B _ M H hell hB.le hY hH side x hx hs hb₁ hb₂ hk
  apply globalScaleIndex_mem_box p hp side x hk0
  intro i
  exact (hcaps i).trans (globalNormCaps_antitone_row ell B _ _ M H hfloor hlower hH i)

end

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def weightedGlobalArithmeticBinSource (γ : GlobalSecondData ι → ℂ) (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (ell Y : ℝ) : ℂ :=
  globalSecondRawSource p hp hcop hg (globalArithmeticBin p s side q j)
    (fun x => γ x*globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x)
    F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m A₁ A₂ W V
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j)

theorem weightedGlobalArithmeticBinSource_squarefree (γ : GlobalSecondData ι → ℂ) (s : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hs : ∀ x∈s,GlobalSecondAdmissible x)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (ell Y : ℝ) :
    weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j F Ψ m ray A₁ A₂ W V ell Y =
    globalSecondRawSource p hp hcop hg (globalSquarefreeBin p s side q j)
      (fun x => γ x*globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x)
      F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m A₁ A₂ W V
      (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
      (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  unfold weightedGlobalArithmeticBinSource globalSecondRawSource globalSquarefreeBin
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hsf : Squarefree (newLabel (globalSecondTuple p x))
  · rw [ite_eq_left hsf]
  · rw [ite_eq_right hsf]
    have hz : globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x=0 := by
      by_contra hn
      exact hsf (globalSecondOuterWeight_squarefree p hp hcop hg Ψ m ray ell Y side x
        (hs x (Finset.mem_filter.mp hx).1) hn)
    simp only [hz,mul_zero,zero_mul]

end

theorem full_uniform_weightedGlobalArithmeticBin_transfer
    (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2), ∀ (θ₁ θ₂ : ℝ), ∀ (s : Finset (GlobalSecondData ι)) (side : Bool)
      (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (ell Y : ℝ)
      (γ : GlobalSecondData ι → ℂ) (Γ : ℝ),
      0 < ell → 0 < Y → q.1 ≠ ⊥ → 0 ≤ Γ → (∀ x∈s,‖γ x‖ ≤ Γ) → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      ‖weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j F Ψ m ray (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V ell Y‖ ≤
      (Γ*C)*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*globalPooledOuterBound ray ell Y j*
        (globalPooledLabelScale j*Ideal.absNorm q.1)^ε/(1+globalBinRadial ell Y j)^A *
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := full_uniform_globalSecondRawSource_twisted_transfer ε hε A₁ A₂ W V M hM hV A J
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound V hVc hVs
  refine ⟨Cₐ*Cₛ*Cw,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc
  have htrans := htrans p hp hcop hg hinj
  intro θ₁ θ₂ s side q j F Ψ m ray ell Y γ Γ hell hY hq hΓ hγ hΨ hs hk
  rw [weightedGlobalArithmeticBinSource_squarefree p hp hcop hg γ s side q j hs]
  let t := globalSquarefreeBin p s side q j
  let T := globalArithmeticTargets p s side q j
  have ht (x : GlobalSecondData ι) (hx : x∈t) : x∈s ∧ globalSecondFixedTriple p x=q ∧ globalScaleIndex p side x=j :=
    Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hbound := globalArithmeticTargets_bounds p hp s side q j hk
  have hB : 0 ≤ globalPooledOuterBound ray ell Y j := by
    have h0 := (globalLogRep_pos j 0).le
    have h1 := (globalLogRep_pos j 1).le
    have h2 := (globalLogRep_pos j 2).le
    have h3 := (globalLogRep_pos j 3).le
    unfold globalPooledOuterBound
    positivity
  have hw : ∀ x∈t,‖γ x*globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x‖*
      ‖JointLogSeparation.outerWindow V (globalBinZ p ell side j x) (globalBinUd p j x)
        (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)‖ ≤ Γ*globalPooledOuterBound ray ell Y j*Cw := by
    intro x hx
    have hh := globalSecondOuterWeight_bin_bound p hp hcop hg hinj hc Ψ hΨ m ray ell Y hell hY.le side x (hk x (ht x hx).1)
    rw [(ht x hx).2.2] at hh
    rw [norm_mul]
    exact mul_le_mul (mul_le_mul (hγ x (ht x hx).1) hh (norm_nonneg _) hΓ)
      (hwglobal _ _ _ _ _) (norm_nonneg _) (mul_nonneg hΓ hB)
  have hh := htrans (globalBinRadial ell Y j) (globalBinRadial_pos ell Y hell hY j) θ₁ θ₂ t T q
    (fun x => γ x*globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x) (Γ*globalPooledOuterBound ray ell Y j*Cw)
    (globalPooledLabelScale j) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) hq (mul_nonneg (mul_nonneg hΓ hB) hCw)
    (zero_le_one.trans (globalPooledLabelScale_ge_one j))
    (fun x hx => hs x (ht x hx).1) (fun x hx => (ht x hx).2.1)
    (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    (fun a ha => (hbound a ha).1) (fun a ha => (hbound a ha).2.1) hw
  convert hh using 1 ; ring

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open SecondPassIntegration (densityChildEnergy)

theorem weightedGlobalPositiveBin_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (θ₁ θ₂ K ell B F : ℝ) (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (γ : GlobalSecondData ι → ℂ) (Γ : ℝ),
      0 < K → 0 < ell → 0 < B → 0 < F → 0 ≤ Γ → (∀ x∈s,‖γ x‖ ≤ Γ) → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      globalBinFirstCoefficient K ell B F j *
      ‖∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ ≤
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight (Γ*C) ε θ₁ θ₂ K ell B F A J j ray q *
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
          (globalPooledColumnScale ell j*globalPooledLabelScale j)) := by
  obtain ⟨C,hC,htrans⟩ := full_uniform_weightedGlobalArithmeticBin_transfer ε hε A₁ A₂ W V M hM hV hVc hVs A J
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg hinj hc θ₁ θ₂ K ell B F s side j pool Ψ m γ Γ hK hell hB hF hΓ hγ hΨ hs hk
  have hy := globalPooledRowScale_pos K ell B F hK hell hB hF j
  have hfirst := globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j
  have hmass : globalPooledColumnScale ell j*globalPooledLabelScale j ≠ 0 :=
    (mul_pos (globalPooledColumnScale_pos ell hell j) (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))).ne'
  calc
    _ ≤ globalBinFirstCoefficient K ell B F j *
        ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        ‖weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ := by
      apply mul_le_mul_of_nonneg_left _ hfirst
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro ray hray
      exact norm_sum_le _ _
    _ = ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalBinFirstCoefficient K ell B F j *
        ‖weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂)
          W V ell (globalPooledRowScale K ell B F j)‖ := by simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ray hray
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨x,hx,hqx⟩ := Finset.mem_image.mp hq
      have hq0 : q.1 ≠ ⊥ := by
        rw [← hqx]
        exact (globalSecondFixedTriple_nonzero p hp x).1
      have ht := htrans p hp hcop hg hinj hc θ₁ θ₂ s side q j pool Ψ m ray ell
        (globalPooledRowScale K ell B F j) γ Γ hell hy hq0 hΓ hγ hΨ hs hk
      have ht' := mul_le_mul_of_nonneg_left ht hfirst
      apply ht'.trans_eq
      have hc0 := (globalPooledColumnScale_pos ell hell j).ne'
      have hl0 := (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)).ne'
      unfold globalDescentWeight
      field_simp

end SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem fixedSecondTest_subunit (V : ℝ → ℂ) (X A : ℝ) (hX : 0 < X)
    (hV : ∀ s,V s ≠ 0 → |s| ≤ A) (hsmall : X*Real.exp A < 1)
    (a b : ℝ) (negative : Bool) (S : Finset ι) : fixedSecondTest p V X a b negative S=0 := by
  have hz : V (columnLog p X S)=0 := by
    by_contra hn
    have hh := columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hV _ hn))
    have h1 := primeProductNorm_ge_one p hp S
    linarith
  cases negative <;> simp [fixedSecondTest,JointLogSeparation.fixedColumnTest,hz]

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem childEnergy_subunit (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X A : ℝ) (hX : 0 < X)
    (hV : ∀ s,V s ≠ 0 → |s| ≤ A) (hsmall : X*Real.exp A < 1)
    (a b : ℝ) (negative rowNegative : Bool) :
    childEnergy p hp hcop hg pool Ψ m T V X negative rowNegative a b=0 := by
  have hrow (f y : O) : fixedChildRow p hp hcop hg pool Ψ m (fixedSecondTest p V X a b negative) f y=0 := by
    unfold fixedChildRow
    apply Finset.sum_eq_zero
    intro S hS
    simp only [secondChildColumn,fixedSecondTest_subunit p hp V X A hX hV hsmall a b negative S,mul_zero]
  simp [childEnergy,idealChildRow,hrow]

theorem densityChildEnergy_subunit (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ A : ℝ) (J : ℕ) (hX : 0 < X₁)
    (hV : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hsmall : X₁*Real.exp A < 1) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J=0 := by
  unfold densityChildEnergy childGeometricMean
  simp only [childEnergy_subunit p hp hcop hg pool Ψ₁ m T V₁ X₁ A hX hV hsmall,
    Real.sqrt_zero,zero_mul,mul_zero,integral_zero]

theorem childDensity_elementary_all_scales
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      (6*128^4*(Real.exp A*M)^2*(∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3)*K*X := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · exact childDensity_elementary_supported p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂ m T V₁ V₂
      X F K A M J hX hF hK hA hM hscale hV₁ hV₂ hVs₁ hVs₂ hT
  · rw [densityChildEnergy_subunit p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X A (2*J) hX hVs₁ (lt_of_not_ge hscale),zero_div]
    have hI : 0 ≤ ∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t :=
      integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
    positivity

end SecondPassIntegration
end

namespace SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open SecondPassIntegration (densityChildEnergy)

def globalTerminalConstant (A M : ℝ) : ℝ :=
  6*128^4*(Real.exp A*M)^2*(∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3

def globalRayTripleConstant : ℝ := 128^3*(Real.exp 1)^18*(512*32^2)

theorem globalTerminalConstant_nonneg (A M : ℝ) : 0 ≤ globalTerminalConstant A M := by
  have hI : 0 ≤ ∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  unfold globalTerminalConstant
  positivity

theorem radial_decay_step (R : ℝ) (hR : 0 ≤ R) (N : ℕ) :
    R/(1+R)^(N+1) ≤ 1/(1+R)^N := by
  have h1 : 0 < 1+R := by linarith
  have hr : R/(1+R) ≤ 1 := (div_le_iff₀ h1).mpr (by linarith)
  calc
    R/(1+R)^(N+1) = (R/(1+R))/(1+R)^N := by rw [pow_succ];field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hr (pow_nonneg h1.le _)

theorem globalPooledRow_radial_bound (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 1 ≤ B) (hF : 1 ≤ F) (j : GlobalLogIndex) (hJ : globalLogRep j 4 ≤ B^2) :
    globalLogRep j 8*Real.exp 1 ≤ globalBinRadial ell (globalPooledRowScale K ell B F j) j*K := by
  have hB0 := zero_lt_one.trans_le hB
  have hF0 := zero_lt_one.trans_le hF
  have hD := globalPooledDelta_pos B F hB0 hF0 j
  have hD1 : 1 ≤ globalPooledDelta B F j :=
    (one_le_mul_of_one_le_of_one_le hB hF).trans (globalPooledDelta_ge B F hB0.le hF0.le j)
  have hN := globalPooledNaturalRow_pos K B F hK hB0 hF0 j
  have hR := globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell
    (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
  have he : globalLogRep j 8*Real.exp 1 =
      globalBinRadial ell (globalPooledRowScale K ell B F j) j*globalPooledNaturalRow K B F j := by
    rw [globalBinRadial,globalPooled_radial_ratio K ell B F hK hell hB0 hF0]
    field_simp
  calc
    _ = _ := he
    _ ≤ globalBinRadial ell (globalPooledRowScale K ell B F j) j*(K/(globalPooledDelta B F j)^2) :=
      mul_le_mul_of_nonneg_left (globalPooledNaturalRow_bound K B F hK hB0 hF0 j hJ) hR.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_self hK.le (one_le_pow₀ hD1)) hR.le

theorem globalRadialBin_terminal_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (V₁ V₂ : ℝ → ℂ) (C ε θ₁ θ₂ K ell B F A₀ M : ℝ) (N J : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hK : 0 < K) (hell : 0 < ell) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hA₀ : 0 ≤ A₀) (hM : 0 ≤ M)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ M) (hV₂ : ∀ t,‖V₂ t‖ ≤ M)
    (hVs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A₀) (hVs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A₀)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hJ : globalLogRep j 4 ≤ B^2) :
    (∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))) ≤
    (C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε *
      (globalTerminalConstant A₀ M*globalRayTripleConstant)*K*((ell*B^3)*F)) /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N := by
  let X := globalPooledColumnScale ell j
  let lengthScale := globalPooledLabelScale j
  let R := globalBinRadial ell (globalPooledRowScale K ell B F j) j
  let K' := globalLogRep j 8*Real.exp 1
  let Ct := globalTerminalConstant A₀ M
  let Q := C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε *
      (Ct*globalRayTripleConstant)*K*((ell*B^3)*F)
  have hB0 := zero_lt_one.trans_le hB
  have hF0 := zero_lt_one.trans_le hF
  have hX := globalPooledColumnScale_pos ell hell j
  have hL := globalPooledLabelScale_ge_one j
  have hR : 0 < R := globalBinRadial_pos ell _ hell (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
  have hK' : 1 ≤ K' := one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 8) (Real.one_le_exp (by norm_num))
  have hCt : 0 ≤ Ct := globalTerminalConstant_nonneg A₀ M
  have hrow : K' ≤ R*K := globalPooledRow_radial_bound K ell B F hK hell hB hF j hJ
  have hQ : 0 ≤ Q := by
    have hn : 0 ≤ globalBinLossScale B j := by
      have hh := (globalLogRep_pos j 4).le
      unfold globalBinLossScale;positivity
    unfold Q globalRayTripleConstant
    positivity
  have hterm (ray : SecondRayIndex) (q : Ideal O × Ideal O × Ideal O) :
      densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂ X X (2*J)/(X*lengthScale) ≤ Ct*K'*(X*lengthScale) := by
    have h := SecondPassIntegration.childDensity_elementary_all_scales p hp hcop hg hc hinj pool
      (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (fun a => (secondRayMinus_norm_le Ψ ray a).trans (hΨ a))
      (fun a => (secondRayPlus_norm_le Ψ ray a).trans (hΨ a))
      (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂ X lengthScale K' A₀ M J
      hX hL hK' hA₀ hM hV₁ hV₂ hVs₁ hVs₂ (globalArithmeticTargets_bounds p hp s side q j hk)
    apply h.trans
    apply mul_le_mul_of_nonneg_left
    · exact le_mul_of_one_le_right hX.le hL
    · exact mul_nonneg hCt (zero_le_one.trans hK')
  have hmass := globalDescentWeight_mass p hp C ε θ₁ θ₂ K ell B F (N+1) (2*J)
    hC hε hK hell hB0 hF0 side s j hk hb₁ hb₂
  calc
    _ ≤ ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q*(Ct*K'*(X*lengthScale)) := by
      apply Finset.sum_le_sum
      intro ray hray
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hterm ray q)
        (globalDescentWeight_nonneg C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q hC hK hell hB0 hF0)
    _ = Ct*K'*(∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q*(X*lengthScale)) := by
      simp only [Finset.mul_sum]
      congr 1
      funext ray
      congr 1
      funext q
      ring
    _ ≤ Ct*(R*K)*((C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε /
        (1+R)^(N+1))*globalRayTripleConstant*((ell*B^3)*F)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hrow hCt
      · exact hmass
      · apply Finset.sum_nonneg
        intro ray hray
        apply Finset.sum_nonneg
        intro q hq
        exact mul_nonneg (globalDescentWeight_nonneg C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q hC hK hell hB0 hF0)
          (mul_nonneg hX.le (zero_le_one.trans hL))
      · exact mul_nonneg hCt (mul_nonneg hR.le hK.le)
    _ = Q*(R/(1+R)^(N+1)) := by dsimp only [Q];ring
    _ ≤ Q*(1/(1+R)^N) := mul_le_mul_of_nonneg_left (radial_decay_step R hR.le N) hQ
    _ = _ := by dsimp only [Q,R,Ct];ring

theorem globalRadialBin_terminal_bound_all_bins {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (V₁ V₂ : ℝ → ℂ) (C ε θ₁ θ₂ K ell B F A₀ M : ℝ) (N J : ℕ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hK : 0 < K) (hell : 0 < ell) (hB : 1 ≤ B) (hF : 1 ≤ F)
    (hA₀ : 0 ≤ A₀) (hM : 0 ≤ M)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ M) (hV₂ : ∀ t,‖V₂ t‖ ≤ M)
    (hVs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A₀) (hVs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A₀)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hb₁ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ∀ x∈s,‖ConcreteTraceCRT.eisEmbedding (FirstPassCubeLabels.primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    :
    (∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F (N+1) (2*J) j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))) ≤
    (C*(1+‖θ₁‖)^(2*J+2)*(1+‖θ₂‖)^(2*J+2)*(globalBinLossScale B j)^ε *
      (globalTerminalConstant A₀ M*globalRayTripleConstant)*K*((ell*B^3)*F)) /
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N := by
  by_cases hs : (globalLogSector p s side j).Nonempty
  · obtain ⟨x,hx⟩ := hs
    obtain ⟨hxs,hj⟩ := Finset.mem_filter.mp hx
    have hJ := globalPooled_J_bound p hp B (zero_lt_one.trans_le hB) side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
    rw [hj] at hJ
    exact globalRadialBin_terminal_bound p hp hcop hg hc hinj pool Ψ hΨ m V₁ V₂ C ε θ₁ θ₂ K ell B F A₀ M N J
      hC hε hK hell hB hF hA₀ hM hV₁ hV₂ hVs₁ hVs₂ s side j hk hb₁ hb₂ hJ
  · have he : globalBinTriples p s side j=∅ := by
      simp only [globalBinTriples,Finset.not_nonempty_iff_eq_empty.mp hs,Finset.image_empty]
    rw [he]
    simp only [Finset.sum_empty,Finset.sum_const_zero]
    have hB0 := zero_lt_one.trans_le hB
    have hF0 := zero_lt_one.trans_le hF
    have hR := globalBinRadial_pos ell _ hell (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
    have hct := globalTerminalConstant_nonneg A₀ M
    have hl := zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)
    have h4 := globalLogRep_pos j 4
    have hh : 0 ≤ globalBinLossScale B j := by unfold globalBinLossScale;positivity
    unfold globalRayTripleConstant
    positivity

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum CompletedGauss
open QuadraticSquarefreeKernel

def liftingPrimeElement : O := ActualEisensteinCoordinates.eval 1 3
def liftingPrime : Ideal O := Ideal.span {liftingPrimeElement}

theorem liftingPrimeElement_norm : ShortDraftLatticeCount.qNat liftingPrimeElement=7 := by
  unfold ShortDraftLatticeCount.qNat liftingPrimeElement
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

theorem liftingPrime_norm : Ideal.absNorm liftingPrime=7 := by
  rw [liftingPrime,←qNat_eq_absNorm_span,liftingPrimeElement_norm]

theorem liftingPrime_prime : Prime liftingPrime := by
  apply Ideal.prime_of_isPrime
  · intro h
    have hh := Ideal.absNorm_eq_zero_iff.mpr h
    rw [liftingPrime_norm] at hh
    norm_num at hh
  · exact Ideal.isPrime_of_irreducible_absNorm (by
      rw [liftingPrime_norm,Nat.irreducible_iff_nat_prime]
      exact (by decide : Nat.Prime 7))

theorem liftingPrime_supported : Supported liftingPrime := by
  apply (supported_span_iff liftingPrimeElement).mpr
  have hlam : ShortDraftLatticeCount.qNat lambda=3 := by
    have he : lambda=ActualEisensteinCoordinates.eval (-1) 1 := theta_counter_lambda_eq
    rw [he]
    unfold ShortDraftLatticeCount.qNat
    rw [ShortDraftLatticeCount.coords_eval]
    norm_num [ShortDraftLatticeCount.q]
  have htwo : ShortDraftLatticeCount.qNat (2:O)=4 := by
    have he : (2:O)=ActualEisensteinCoordinates.eval 2 0 := by simp [ActualEisensteinCoordinates.eval]
    rw [he]
    unfold ShortDraftLatticeCount.qNat
    rw [ShortDraftLatticeCount.coords_eval]
    norm_num [ShortDraftLatticeCount.q]
  constructor
  · rintro ⟨z,hz⟩
    have h := congrArg ShortDraftLatticeCount.qNat hz
    rw [liftingPrimeElement_norm,ShortDraftLatticeCount.qNat_mul,hlam] at h
    omega
  · rintro ⟨z,hz⟩
    have h := congrArg ShortDraftLatticeCount.qNat hz
    rw [liftingPrimeElement_norm,ShortDraftLatticeCount.qNat_mul,htwo] at h
    omega

theorem liftingPrime_admissible : Admissible liftingPrime :=
  ⟨liftingPrime_prime.ne_zero,liftingPrime_prime.squarefree,liftingPrime_supported.2⟩

theorem supported_pow {I : Ideal O} (hI : Supported I) (k : ℕ) : Supported (I^k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    change P∈UniqueFactorizationMonoid.normalizedFactors (1:Ideal O) at hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact (Multiset.notMem_zero P hP).elim
  | succ k hk =>
    rw [pow_succ]
    exact (supported_mul_iff _ _).mpr ⟨hk,hI⟩

theorem exists_lifting_exponent (M : ℝ) (I : Ideal O) (hI : I≠0)
    (hIM : (Ideal.absNorm I:ℝ)≤M) :
    ∃k : ℕ, M<(49:ℝ)^k*(Ideal.absNorm I:ℝ) ∧
      (49:ℝ)^k*(Ideal.absNorm I:ℝ)≤49*M := by
  have hN : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ hN).mpr (by simpa using hIM))
    (by norm_num : (1:ℝ)<49)
  refine ⟨k+1,?_,?_⟩
  · exact (div_lt_iff₀ hN).mp hhi
  · have h := (le_div_iff₀ hN).mp hlo
    rw [pow_succ]
    nlinarith

def liftingExponent (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) : ℕ :=
  (exists_lifting_exponent M I hI hIM).choose

def liftedRow (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) : Ideal O :=
  (liftingPrime^liftingExponent M I hI hIM)^2*I

theorem liftedRow_norm (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) :
    (Ideal.absNorm (liftedRow M I hI hIM):ℝ)=(49:ℝ)^liftingExponent M I hI hIM*(Ideal.absNorm I:ℝ) := by
  simp only [liftedRow,map_mul,map_pow,liftingPrime_norm,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [←pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem liftedRow_bounds (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) :
    M<(Ideal.absNorm (liftedRow M I hI hIM):ℝ) ∧
      (Ideal.absNorm (liftedRow M I hI hIM):ℝ)≤49*M := by
  rw [liftedRow_norm]
  exact (exists_lifting_exponent M I hI hIM).choose_spec

theorem liftedRow_squarefreePart (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) : squarefreePart (liftedRow M I hI.1 hIM)=I :=
  (squarePart_mul_squarefree (pow_ne_zero _ liftingPrime_prime.ne_zero) hI.2.1).2

theorem liftedRow_supported (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) : Supported (liftedRow M I hI.1 hIM) := by
  exact (supported_mul_iff _ _).mpr
    ⟨supported_pow (supported_pow liftingPrime_supported _) _,admissible_supported hI⟩

theorem liftedRow_character (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) (J : Ideal O) (hJ : Admissible J)
    (hPJ : IsCoprime liftingPrime J) :
    quadraticRow J (primaryGenerator (liftedRow M I hI.1 hIM)) =
      quadraticRow J (primaryGenerator I) := by
  rw [liftedRow,canonical_quadraticRow_primary_squarefree J hJ,
    idealZeroMask_primary_eq_indicator J _ hJ.1 (supported_pow liftingPrime_supported _),
    ite_eq_left hPJ.pow_left,one_mul]

theorem liftedRow_injective (M : ℝ) :
    Function.Injective (fun I : idealRange M =>
      liftedRow M I.val (mem_idealRange.mp I.property).1.1 (mem_idealRange.mp I.property).2) := by
  intro I J h
  apply Subtype.ext
  have he := congrArg squarefreePart h
  simpa only [liftedRow_squarefreePart M I.val (mem_idealRange.mp I.property).1,
    liftedRow_squarefreePart M J.val (mem_idealRange.mp J.property).1] using he

end CanonicalQuadraticSieve

end

end OAI
