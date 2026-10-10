import OAI.NumberTheory.DirichletL.Eisenstein.DirichletForm

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

theorem poolProduct_admissible (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (S : Finset (primePool F)) : Admissible (∏ i ∈ S,i.val) := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏ i ∈ S,i.val) ≠ (0 : Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  refine ⟨hn, ?_, ?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))).isRelPrime
    · intro i hi
      exact (hp i).squarefree
  · intro P hP
    obtain ⟨hprime, hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
    obtain ⟨i, hi, hPi⟩ := (hprime.dvd_finsetProd_iff (fun i : primePool F => i.val)).mp hdiv
    have he : P=i.val := (prime_dvd_prime_iff_eq hprime (hp i)).mp hPi
    rw [he]
    exact ⟨poolGood F hF i, poolOdd F hF i⟩

theorem poolPrimary_norm (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (S : Finset (primePool F)) :
    primeProductNorm (poolPrimary F) S = (Ideal.absNorm (∏ i ∈ S,i.val) : ℝ) := by
  rw [primeProductNorm, eisEmbedding_norm_sq_eq_absNorm_span, FiniteGaussPhase.span_finset_prod]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact poolPrimary_span F hF i

theorem selectedIdealTest_full_range (W : ℝ → ℂ) (b Z X : ℝ) (hZ : 0 < Z)
    (hs : ∀ t, W t ≠ 0 → t ≤ b) (hX : b*Z ≤ X)
    (S : Finset (primePool (idealRange X))) :
    selectedIdealTest (idealRange X) (fun n => W (n/Z)) S =
      W (primeProductNorm (poolPrimary (idealRange X)) S/Z) := by
  have hF : ∀ I ∈ idealRange X, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  rw [poolPrimary_norm (idealRange X) hF S]
  unfold selectedIdealTest
  by_cases hw : W ((Ideal.absNorm (∏ i ∈ S,i.val) : ℝ)/Z)=0
  · simp only [hw, ite_self]
  · rw [ite_eq_left]
    apply mem_idealRange.mpr
    refine ⟨poolProduct_admissible (idealRange X) hF S, ?_⟩
    exact ((div_le_iff₀ hZ).mp (hs _ hw)).trans hX

theorem idealRowSum_initial_energy {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W : ℝ → ℂ) (a b Z X : ℝ) (ha : 0 < a) (hZ : 0 < Z)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hX : b*Z ≤ X) (z : O) :
    let F := idealRange X
    let hF := fun I (hI : I ∈ F) => (mem_idealRange.mp hI).1
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    ‖idealRowSum F (fun I hI => (hF I hI).1)
      (fun I hI P hP => ((hF I hI).2.2 P hP).1) χ (fun n => W (n/Z)) z‖^2/Z =
    ‖mobiusRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ (normCharacter χ) 1
      (normalizedColumn (poolPrimary F)
        (fun T => initialLogProfile W a b ha hs hW (columnLog (poolPrimary F) Z T))) z‖^2 := by
  dsimp only
  let F := idealRange X
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  rw [idealRowSum_eq_mobiusRow F hF]
  have ht : selectedIdealTest F (fun n => W (n/Z)) =
      fun T => W (primeProductNorm (poolPrimary F) T/Z) := by
    funext T
    exact selectedIdealTest_full_range W b Z X hZ (fun t ht => (hs ht).2) hX T
  rw [ht]
  exact (mobiusRow_initial_energy (poolPrimary F) (poolPrimary_good F hF)
    (poolPrimary_ne_zero F hF) Finset.univ (normCharacter χ) 1 z Z hZ W a b ha hs hW).symm

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem inputConjugateRow_zero_of_mass_zero (F : Finset ι) (Ψ : O →* ℂ)
    (m c d : O) (H : Finset ι → ℂ)
    (hm : (∑S∈F.powerset,‖secondInputCoefficient p hg Ψ m c d H S‖^2)=0) (z : O) :
    inputConjugateRow p hg F Ψ m c d H z=0 := by
  unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  apply Finset.sum_eq_zero
  intro S hS
  have hle : ‖secondInputCoefficient p hg Ψ m c d H S‖^2≤0 := by
    rw [←hm]
    exact Finset.single_le_sum (f := fun A => ‖secondInputCoefficient p hg Ψ m c d H A‖^2) (fun A _ => sq_nonneg _) hS
  have hz : secondInputCoefficient p hg Ψ m c d H S=0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (secondInputCoefficient p hg Ψ m c d H S)]
  simp only [hz,mul_zero,zero_mul]

include hp in
theorem globalFirstCoreRow_zero_off_support (pool : Finset ι) (b : GlobalFirstData ι)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (ell M U : ℝ) (hell : 0<ell)
    (hM : ∀t,g t≠0 → |t|≤M) (hU : ell*Real.exp M≤U)
    (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ) (z : O)
    (hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)) :
    globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z=0 := by
  have hX : 0<globalFirstBlockColumnScale p ell side b :=
    div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
  have hm := globalFirstColumnMass_zero_off_support p hp hg pool b (firstCoreTwist side χ Ψ r) m
    (firstCoreModeProfile g V side t) ell M U hell
    (fun u hu => hM u (firstCoreModeProfile_support g V side t u hu).1) hU side hoff
  have hz := inputConjugateRow_zero_of_mass_zero p hg (globalFirstRawPool pool b)
    (firstCoreTwist side χ Ψ r) (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    (globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b) hm (if side then -z else z)
  unfold globalFirstCoreRow
  rw [firstCoreInputRow_eq_mode_row p hp hg _ _ _ _ _ _ side χ Ψ m g V _ hX]
  change _*inputConjugateRow p hg (globalFirstRawPool pool b) (firstCoreTwist side χ Ψ r)
    (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    (globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b) (if side then -z else z)=0
  rw [hz,mul_zero]

include hp in

theorem globalFirstFiniteEnergy_eq_supported (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ))
    (ell M U : ℝ) (hell : 0<ell) (hM : ∀t,g t≠0 → |t|≤M) (hU : ell*Real.exp M≤U)
    (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex)
    (T : GlobalFirstData ι → Finset O) (t : ℝ) :
    globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side χ r T t=
      globalFirstFiniteEnergy p hg pool
        (s.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U))
        w Ψ m g V ell side χ r T t := by
  unfold globalFirstFiniteEnergy
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro b hb hn
  have hoff : ¬(primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U) := by
    intro hh; exact hn (Finset.mem_filter.mpr ⟨hb,hh⟩)
  have hz (z : O) := globalFirstCoreRow_zero_off_support p hp hg pool b Ψ m g V ell M U hell hM hU side χ r t z hoff
  simp only [hz,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,mul_zero]

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

def globalFirstTailFactor (K ell B F U H : ℝ) (N : ℕ) : ℝ :=
  (1+U)^4*(1+(1+U)^3*(K*U^2/(ell^2*B^2*F^2)))^2/(1+H)^N

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstPooledRow_lower_from_common (b : GlobalFirstData ι)
    (K ell B F U : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hU : 0<U)
    (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) (side : Bool) :
    ell^2*B^2*F^2/(K*U^2)≤globalFirstPooledRow p K ell B F side b := by
  let x := b.append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p side x
  have hC : globalLogRep j 1≤U := (globalScaleIndex_bounds p hp side x one_ne_zero 1).1.trans hc
  have hJ := globalPooled_J_bound p hp B hB side x one_ne_zero hb1 hb2
  have hcp := globalLogRep_pos j 1
  have hjp := globalLogRep_pos j 4
  have hd := globalLogRep_ge_one j 5
  have he : 1≤Real.exp 1 := Real.one_le_exp (by norm_num)
  change _≤Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
  calc
    _ = ell^2*B^4*F^2/(K*U^2*B^2) := by field_simp
    _ ≤ _ := by
      apply div_le_div₀ (by positivity)
      · calc
          ell^2*B^4*F^2 = 1*ell^2*B^4*F^2*1 := by ring
          _ ≤ _ := by gcongr
      · positivity
      · gcongr

include hp in
theorem globalFirstTailFactor_bound (b : GlobalFirstData ι)
    (K ell B F M U H : ℝ) (N : ℕ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hU : 1≤U) (hH : 0≤H)
    (hellU : ell*Real.exp M≤U) (hc : primeProductNorm p b.common≤U)
    (hb1 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb2 : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) (side : Bool) :
    let lengthScale := 1+globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon*Real.exp M
    let Y := globalFirstPooledRow p K ell B F side b
    lengthScale^4*(1+lengthScale^3/Y)^2/(1+H)^N≤globalFirstTailFactor K ell B F U H N := by
  dsimp only
  let X := globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon
  let Y := globalFirstPooledRow p K ell B F side b
  have ha := primeProductNorm_ge_one p hp (b.cube.sideDivisor side)
  have hc1 := primeProductNorm_ge_one p hp b.common
  have ht := primeProductNorm_ge_one p hp b.firstCommon
  have hX : 0<X := by
    dsimp [X,globalFirstBlockColumnScale]
    positivity
  have hXle : X≤ell := by
    dsimp [X,globalFirstBlockColumnScale]
    apply (div_le_self (by positivity) ht).trans
    exact div_le_self hell.le (one_le_mul_of_one_le_of_one_le ha hc1)
  have hL : 1+X*Real.exp M≤1+U := add_le_add le_rfl ((mul_le_mul_of_nonneg_right hXle (Real.exp_pos _).le).trans hellU)
  have hY : 0<Y := globalPooledRowScale_pos K ell B F hK hell hB hF _
  have hlower := globalFirstPooledRow_lower_from_common p hp b K ell B F U hK hell hB hF (by linarith) hc hb1 hb2 side
  have hinv : 1/Y≤K*U^2/(ell^2*B^2*F^2) := by
    have h := one_div_le_one_div_of_le (by positivity : 0<ell^2*B^2*F^2/(K*U^2)) hlower
    simpa only [one_div_div] using h
  have hratio : (1+X*Real.exp M)^3/Y≤(1+U)^3*(K*U^2/(ell^2*B^2*F^2)) := by
    calc
      _ = (1+X*Real.exp M)^3*(1/Y) := by ring
      _ ≤ _ := by gcongr
  change (1+X*Real.exp M)^4*(1+(1+X*Real.exp M)^3/Y)^2/(1+H)^N≤_
  unfold globalFirstTailFactor
  gcongr

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

theorem globalFirstWeightedVolume_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Γ K ell B F U : ℝ) (side : Bool),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 1≤U →
      (∀b∈s,0≤w b ∧ w b≤Γ) → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,primeProductNorm p b.common≤U) → (∀b∈s,primeProductNorm p b.firstCommon≤U) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∑b∈s,w b*globalFirstCoefficient p K ell B F side b*
        globalFirstPooledRow p K ell B F side b*(primeProductNorm p b.firstCommon)⁻¹)≤
          C*Γ*(ell*B^3*F)*(B*U)^ε := by
  obtain ⟨Cd,hCd,hcount⟩ := globalFirstData_harmonic_sum (ε/3) (by positivity)
  obtain ⟨Cp,hCp,hpowers⟩ := globalDiagonalPowers ε hε
  refine ⟨Cd*(Real.exp 1)^3*Cp,by positivity,?_⟩
  intro ι _ p hp _ hinj s w Γ K ell B F U side hΓ hK hell hB hF hU hw hs hC ht hb1 hb2
  have hB0 : 0<B := by linarith
  let θ := fun b : GlobalFirstData ι =>
    (1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
      (1/‖eisEmbedding (∏i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)
  have hsum := hcount p hp hinj s B U hB hU hs hC ht hb1 hb2
  change (∑b∈s,θ b)≤_ at hsum
  have hterm (b : GlobalFirstData ι) (hb : b∈s) :
      w b*globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤(Γ*(Real.exp 1)^3*ell*B^2*F)*θ b := by
    have htpos := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
    have hc : 0≤globalFirstCoefficient p K ell B F side b :=
      globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
    have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
    have hsc := globalFirst_diagonal_scalar p hp K ell B F hK hell hB0 hF side b
    have hsc' : globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹≤((Real.exp 1)^3*ell*B^2*F)*θ b := by
      convert hsc using 1 ; dsimp [θ] ; ring
    calc
      _ = w b*(globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹) := by ring
      _ ≤ Γ*(globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
        (primeProductNorm p b.firstCommon)⁻¹) := mul_le_mul_of_nonneg_right (hw b hb).2 (by positivity)
      _ ≤ Γ*(((Real.exp 1)^3*ell*B^2*F)*θ b) := mul_le_mul_of_nonneg_left hsc' hΓ
      _ = _ := by ring
  calc
    _ ≤ (Γ*(Real.exp 1)^3*ell*B^2*F)*(∑b∈s,θ b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ (Γ*(Real.exp 1)^3*ell*B^2*F)*
        (Cd*B^(1+ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Cd*(Real.exp 1)^3)*Γ*(ell*B^3*F)*
        (B^(ε/3)*(U*B^2)^(ε/3)*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2) := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      ring
    _ ≤ (Cd*(Real.exp 1)^3)*Γ*(ell*B^3*F)*(Cp*(B*U)^ε) :=
      mul_le_mul_of_nonneg_left (hpowers B U hB hU) (by positivity)
    _ = _ := by ring

theorem globalFirstTailCost_parent_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
      (Γ K ell B F M U H : ℝ) (N : ℕ) (side : Bool),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 1≤U → 0≤H → ell*Real.exp M≤U →
      (∀b∈s,0≤w b ∧ w b≤Γ) → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,primeProductNorm p b.common≤U) → (∀b∈s,primeProductNorm p b.firstCommon≤U) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      globalFirstTailCost p s (fun b => ((w b*globalFirstCoefficient p K ell B F side b : ℝ) : ℂ))
        K ell B F M H N side≤C*Γ*(ell*B^3*F)*(B*U)^ε*globalFirstTailFactor K ell B F U H N := by
  obtain ⟨C,hC,hvolume⟩ := globalFirstWeightedVolume_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj s w Γ K ell B F M U H N side hΓ hK hell hB hF hU hH hellU hw hs hCnorm ht hb1 hb2
  have hB0 : 0<B := by linarith
  have hfactor : 0≤globalFirstTailFactor K ell B F U H N := by unfold globalFirstTailFactor; positivity
  have hv := hvolume p hp hinj s w Γ K ell B F U side hΓ hK hell hB hF hU hw hs hCnorm ht hb1 hb2
  apply le_trans _ (mul_le_mul_of_nonneg_right hv hfactor)
  unfold globalFirstTailCost
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b hb
  dsimp only
  have hc : 0≤globalFirstCoefficient p K ell B F side b :=
    globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB0 hF _
  have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB0 hF _
  have hT := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon
  have hw0 := (hw b hb).1
  rw [Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hw0 hc)]
  have h := globalFirstTailFactor_bound p hp b K ell B F M U H N hK hell hB0 hF hU hH hellU (hCnorm b hb) (hb1 b hb) (hb2 b hb) side
  dsimp only at h
  have h' := mul_le_mul_of_nonneg_left h
    (show 0≤w b*globalFirstCoefficient p K ell B F side b*globalFirstPooledRow p K ell B F side b*
      (primeProductNorm p b.firstCommon)⁻¹ by positivity)
  convert h' using 1 ; ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem globalFirstCoreRows_quantitative_transfer
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cd Ct : ℝ),0≤C ∧ 0<Cd ∧ 0<Ct ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℝ) (Γ K ell B F H U : ℝ)
      (Ψ : O →* ℂ) (m : O) (χ : RayCharacter) (r : FirstCoreIndex)
      (T : GlobalFirstData ι → Finset O),
      0≤Γ → (∀ b∈s,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M≤U →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side b) →
      (∀ b∈s,∀ z∈T b,z≠0) →
      let activeFamily := s.filter (fun b => FirstPassCubeLabels.primeProductNorm p b.common≤U ∧
        FirstPassCubeLabels.primeProductNorm p b.firstCommon≤U)
      let source := globalFirstSupportedPool p pool activeFamily
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
      let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
      let Ψmode := firstCoreTwist side χ Ψ r
      (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
        globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t) ≤
      (∫ t : ℝ,firstLogDensity 0 t)*
        (Cd*Γ*(ell*B^3*F)*(B*U)^ε +
          globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε 0 0 K ell B F M H A J side +
          Ct*Γ*(ell*B^3*F)*(B*U)^ε*globalFirstTailFactor K ell B F U H N) := by
  have hbase : ∀t,firstCoreBaseProfile g V side t≠0 → |t|≤M := by
    intro t ht
    apply hgM t
    intro hz
    apply ht
    simp only [firstCoreBaseProfile_apply,hz,zero_mul]
  obtain ⟨windows,C,Ct0,hC,hCt0,hwc,hws,hwb,hrows⟩ :=
    globalFirstCoreRows_integrated_transfer ε hε g V M hM hgM side A J N
  obtain ⟨Cd,hCd,hdiag⟩ := globalFirstDiagonalCost_parent_bound ε hε
    (firstCoreBaseProfile g V side) rowMajorant M hbase
  obtain ⟨Ct1,hCt1,htail⟩ := globalFirstTailCost_parent_bound ε hε
  refine ⟨windows,C,Cd,Ct0*Ct1,hC,hCd,mul_pos hCt0 hCt1,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ K ell B F H U Ψ m χ r T
    hΓ hw hK hell hB hF hH hU hellU hs hΨ hb1 hb2 hT hT0
  dsimp only
  have hB0 : 0<B := by linarith
  let activeFamily := s.filter (fun b => FirstPassCubeLabels.primeProductNorm p b.common≤U ∧
    FirstPassCubeLabels.primeProductNorm p b.firstCommon≤U)
  let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
  let Ψmode := firstCoreTwist side χ Ψ r
  have hsub (b : GlobalFirstData ι) (hb : b∈activeFamily) : b∈s := (Finset.mem_filter.mp hb).1
  have hΓw := fun b hb => hw b (hsub b hb)
  have hsa := fun b hb => hs b (hsub b hb)
  have hba1 := fun b hb => hb1 b (hsub b hb)
  have hba2 := fun b hb => hb2 b (hsub b hb)
  have hΨmode : ∀a,‖Ψmode a‖≤1 := fun a => (firstCoreTwist_norm_le side χ Ψ r a).trans (hΨ a)
  have hr := hrows p hp hcop hg hinj hc hpr pool activeFamily w Γ K ell B F H Ψ m χ r T
    hΓ hΓw hK hell hB0 hF hH hsa hΨ hba1 hba2
    (fun b hb => hT b (hsub b hb)) (fun b hb => hT0 b (hsub b hb))
  dsimp only at hr
  have hd := hdiag p hp hg hinj pool activeFamily w Ψmode m Γ K ell B F U side
    hΓ hK hell hB hF hU hellU hΨmode hΓw hsa hba1 hba2
  have ht := htail p hp hinj activeFamily w Γ K ell B F M U H N side
    hΓ hK hell hB hF hU hH hellU hΓw hsa
    (fun b hb => (Finset.mem_filter.mp hb).2.1) (fun b hb => (Finset.mem_filter.mp hb).2.2) hba1 hba2
  have heq :
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t)=
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*globalFirstFiniteEnergy p hg pool activeFamily weight Ψ m g V ell side χ r T t) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [globalFirstFiniteEnergy_eq_supported p hp hg pool s weight Ψ m g V ell M U hell hgM hellU side χ r T t]
  rw [heq]
  apply hr.trans
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t))
  have ht' := mul_le_mul_of_nonneg_left ht hCt0.le
  have h := add_le_add (add_le_add hd (le_refl
    (globalChildBudget p hp hcop hg pool
      (globalFirstSupportedPool p pool activeFamily
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side)
      Ψmode m windows (Γ*C) ε 0 0 K ell B F M H A J side))) ht'
  convert h using 1 ; dsimp [weight,Ψmode] ; ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def globalFirstRayChildBudget (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C Γ ε K ell B F M H U : ℝ) (A J : ℕ) (side : Bool) : ℝ :=
  let family := (globalFirstFamilySet pool blocks).filter
    (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)
  let source := globalFirstSupportedPool p pool family
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,
    (∫t : ℝ,firstLogDensity 0 t)*globalChildBudget p hp hcop hg pool source
      (firstCoreTwist side (if side then a.1 else a.2) Ψ r) m windows (Γ*firstCoreUniformWeight r*C)
      ε 0 0 K ell B F M H A J side

def globalFirstQuantitativeBudget (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C Cd Ct Γ ε K ell B F M H U : ℝ) (A J N : ℕ) (side : Bool) : ℝ :=
  (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*(ell*B^3*F)*(B*U)^ε*
      (Cd+Ct*globalFirstTailFactor K ell B F U H N) +
    globalFirstRayChildBudget p hp hcop hg pool blocks Ψ m windows C Γ ε K ell B F M H U A J side

end

private lemma two_finite_error_sum {α β : Type*} [Fintype α] [Fintype β]
    (a : α → ℝ) (b : β → ℝ) (E : ℝ) (c : α → β → ℝ) :
    (∑x,a x*∑y,(b y*E+c x y))=(∑x,a x)*(∑y,b y)*E+∑x,a x*∑y,c x y := by
  simp only [Finset.sum_add_distrib,Finset.sum_mul,mul_add]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_mul]
  ring

theorem globalCubeInputFamilyEnergy_quantitative
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀t,g t≠0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cd Ct : ℝ),0≤C ∧ 0<Cd ∧ 0<Ct ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0 → |t|≤M+6+1) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2) (_hpr : ∀i,lambda^2∣p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (w : GlobalCubeBlock ι → ℝ) (Γ K ell B F H U : ℝ)
      (Ψ : O →* ℂ) (m : O) (T : GlobalCubeBlock ι → Finset O),
      0≤Γ → (∀b∈blocks,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M≤U →
      (∀b∈blocks,GlobalCubeAdmissible b) → (∀a,‖Ψ a‖≤1) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀b∈blocks,∀z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side (b.withCommon ∅)) →
      (∀b∈blocks,∀z∈T b,z≠0) →
      (∑b∈blocks,w b*globalCubeCoefficient p K ell B F side b*
        globalCubeInputFamilyEnergy p hg pool b Ψ m g V ell side (2*(J+2)) (T b))≤
      globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ m windows C Cd Ct Γ ε K ell B F M H U A J N side := by
  obtain ⟨windows,C,Cd,Ct,hC,hCd,hCt,hwc,hws,hwb,hrow⟩ :=
    globalFirstCoreRows_quantitative_transfer ε hε g V M hM hgM side A J N
  refine ⟨windows,C,Cd,Ct,hC,hCd,hCt,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ m T
    hΓ hw hK hell hB hF hH hU hellU hs hΨ hb1 hb2 hT hT0
  have hB0 : 0<B := by linarith
  let family := globalFirstFamilySet pool blocks
  let activeFamily := family.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)
  let source := globalFirstSupportedPool p pool activeFamily
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  let child := fun (a : RayCharacter×RayCharacter) (r : FirstCoreIndex) =>
    (∫t : ℝ,firstLogDensity 0 t)*globalChildBudget p hp hcop hg pool source
      (firstCoreTwist side (if side then a.1 else a.2) Ψ r) m windows (Γ*firstCoreUniformWeight r*C)
      ε 0 0 K ell B F M H A J side
  let E0 := (∫t : ℝ,firstLogDensity 0 t)*Γ*(ell*B^3*F)*(B*U)^ε*(Cd+Ct*globalFirstTailFactor K ell B F U H N)
  have hI : 0≤∫t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hf0 : 0≤globalFirstTailFactor K ell B F U H N := by unfold globalFirstTailFactor; positivity
  have hE0 : 0≤E0 := by dsimp [E0]; positivity
  have hrow' (a : RayCharacter×RayCharacter) (r : FirstCoreIndex) :
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*
        globalFirstFiniteEnergy p hg pool family
          (fun d => globalFirstFamilyWeight p hg w Ψ m side r d*globalFirstCoefficient p K ell B F side d)
          Ψ m g V ell side (if side then a.1 else a.2) r (fun d => T d.block) t)≤
      firstCoreUniformWeight r*E0+child a r := by
    have hΓr : 0≤Γ*firstCoreUniformWeight r := by unfold firstCoreUniformWeight; positivity
    have h := hrow p hp hcop hg hinj hc hpr pool family
      (globalFirstFamilyWeight p hg w Ψ m side r) (Γ*firstCoreUniformWeight r) K ell B F H U Ψ m
      (if side then a.1 else a.2) r (fun d => T d.block) hΓr
      (fun d hd => globalFirstFamilyWeight_bounds p hg blocks w Γ hw Ψ hΨ m side r pool d hd)
      hK hell hB hF hH hU hellU
      (fun d hd => hs d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1) hΨ
      (fun d hd => hb1 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1)
      (fun d hd => hb2 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1)
      (by intro d hd z hz; rw [globalFirstPooledRow_block]; exact hT d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1 z hz)
      (fun d hd => hT0 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1)
    dsimp only at h
    convert h using 1 ; dsimp [E0,child,source,activeFamily] ; ring
  rw [globalCubeInputFamilyEnergy_eq_integrated_rows]
  have hm : (∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)*(∑r : FirstCoreIndex,firstCoreUniformWeight r)≤512*(512*32) := by
    have ha : (∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)≤512 := by
      simpa only [Fintype.sum_prod_type] using RayFourExpansion.crossCoeff_sum_norm_le
    exact mul_le_mul ha firstCoreUniformWeight_mass
      (Finset.sum_nonneg (fun r _ => by unfold firstCoreUniformWeight; positivity)) (by norm_num)
  calc
    _ ≤ ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,(firstCoreUniformWeight r*E0+child a r) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun r _ => hrow' a r)) (norm_nonneg _))
    _ = ((∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)*(∑r : FirstCoreIndex,firstCoreUniformWeight r))*E0+
        ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,child a r :=
      two_finite_error_sum _ _ _ _
    _ ≤ (512*(512*32))*E0+∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,child a r :=
      add_le_add (mul_le_mul_of_nonneg_right hm hE0) le_rfl
    _ = _ := by
      unfold globalFirstQuantitativeBudget globalFirstRayChildBudget
      dsimp [E0,child,source,activeFamily,family]
      ring

end SecondPassArithmetic

end

end OAI
