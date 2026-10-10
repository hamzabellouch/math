import OAI.NumberTheory.DirichletL.Eisenstein.FixedFrequencyExpansion

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
open scoped BigOperators Classical

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedThetaTwist_mul (φ χ:Eis→*ℂ) (n:Eis) :
    fixedThetaTwist (φ*χ) n=fixedThetaTwist φ n*χ n := by
  by_cases hn:lambda^2∣n-1
  · rw [fixedThetaTwist_primary _ n hn,fixedThetaTwist_primary _ n hn,MonoidHom.mul_apply]
    ring
  · rw [fixedThetaTwist_not_primary _ n hn,fixedThetaTwist_not_primary _ n hn,zero_mul]

def fixedThetaRowCoeff (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (h:Eis⧸Ideal.span {c}) : ℂ :=
  finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient φ c) h

lemma fixedThetaRowCoeff_norm (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (h:Eis⧸Ideal.span {c}) :
    ‖fixedThetaRowCoeff c hc φ h‖≤1 :=
  finiteAdditiveFourierCoeff_norm _ _ (fixedThetaQuotient_norm_le_one φ hφ c) h

theorem fixedThetaTwist_fixed_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Q:Ideal Eis) (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (φ χ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (n:Eis) :
    fixedThetaTwist (φ*χ) n=
      ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n*χ n := by
  rw [←Finset.sum_mul,fixedThetaTwist_mul]
  congr 1
  have h:=finiteAdditiveFourier_inversion (quotientTrace c hc)
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) (fixedThetaQuotient φ c)
    (Ideal.Quotient.mk _ n)
  rw [fixedThetaQuotient_mk φ Q hφ c hcQ n] at h
  exact h.symm

theorem fixedThetaTwist_free_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Q:Ideal Eis) (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (I:Ideal Eis) (hI:CanonicalQuadraticSieve.Supported I)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (n:Eis) :
    fixedThetaTwist (φ*freePrimeRow I hI Q) n=
      (∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n)*
      ActualEisensteinCubic.principalSexticRow (fun P:FreePrimeIndex I Q=>P.val.val)
        (freePrimeIndex_pairwise_coprime I Q)
        (fun P=>(supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1)
        (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val.val%6)
        (ActualEisensteinCubic.finitePrimeModulus (fun P:FreePrimeIndex I Q=>P.val.val))
        (ActualEisensteinCubic.span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [fixedThetaTwist_fixed_fourier c hc Q hcQ φ _ hφ n,←Finset.sum_mul,
    freePrimeRow_eq_principalSexticRow I hI Q n]

theorem actual_fixedTheta_fourier (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:CanonicalQuadraticSieve.Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (∀h:Eis⧸Ideal.span {c},‖fixedThetaRowCoeff c hc φ h‖≤1) ∧
      (∀n,fixedThetaTwist (rowTwist Ψ m f z) n=
        ∑h:Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc φ h*fixedRowFourierPhase c hc h n*
          freePrimeRow I hI (Q*Ideal.span {(72:Eis)}) n) := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hrow⟩:=exists_actual_coprime_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,hcop,fixedThetaRowCoeff_norm c hc φ hφn,?_⟩
  have he:fixedThetaTwist (rowTwist Ψ m f z)=
      fixedThetaTwist (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})):=
    fixedThetaTwist_congr_primary _ _ hrow
  intro n
  rw [he]
  exact fixedThetaTwist_fixed_fourier c hc _ hcQ φ _ hφ n

end CubicEisenstein

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
open UniqueFactorizationMonoid LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

lemma admissiblePrimeGood (K:Ideal Eis) (hK:Admissible K) (P:PrimeIndex K) : lambda∉P.val :=
  (hK.2.2 P.val (Multiset.mem_toFinset.mp P.property)).1

theorem quadraticRow_eq_primeIndex (K:Ideal Eis) (hK:Admissible K) (x:Eis) :
    quadraticRow K x=finiteSexticRow (fun P:PrimeIndex K=>P.val)
      (admissiblePrimeGood K hK) (fun _=>3) x := by
  have hs:∀I∈({K}:Finset (Ideal Eis)),Admissible I:=by
    intro I hI
    simpa only [Finset.mem_singleton.mp hI] using hK
  have heq:primePool ({K}:Finset (Ideal Eis))=primeSupport K:=by
    simp [primePool,primeSupport]
  let e:primePool ({K}:Finset (Ideal Eis))≃PrimeIndex K:={
    toFun:=fun P=>⟨P.val,heq ▸ P.property⟩
    invFun:=fun P=>⟨P.val,heq.symm ▸ P.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
  rw [quadraticRow_eq_pool {K} hs K (Finset.mem_singleton_self K) x,
    idealSupport_singleton_univ]
  simp only [QuadraticInitialBound.quadraticRow,finiteSquarefreeRow,Finset.prod_pow,
    finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]
  congr 1
  exact Fintype.prod_equiv e _ _ (fun P=>rfl)

theorem completedLocalExponent_residual (I F Q:Ideal Eis) (hFQ:F∣Q)
    (P:PrimeIndex (rowResidualPart I Q)) : completedLocalExponent I F P.val=1 := by
  have h:=rowResidualPart_prime_exponent I Q P.val (Multiset.mem_toFinset.mp P.property)
  have hnot:¬P.val∣F:=fun hd=>h.2.2 (hd.trans hFQ)
  simp only [completedLocalExponent,h.2.1,ite_eq_right hnot,mul_zero,add_zero,Nat.reduceMod]

theorem residual_bracket_eq_quadraticRow (I F Q:Ideal Eis) (hFQ:F∣Q)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (x:Eis) :
    (∏P:PrimeIndex (rowResidualPart I Q),
      bracket (actualSextic P.val
        (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) P))
        (completedLocalExponent I F P.val) (Ideal.Quotient.mk P.val x))=
      quadraticRow (rowResidualPart I Q) x := by
  simp_rw [completedLocalExponent_residual I F Q hFQ,bracket_one_eq_quadratic]
  rw [quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad)]
  simp only [finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ)≠0)]

def residualQuadraticPhase (K:Ideal Eis) (u:Eisˣ) (m:ℕ) (D E:Ideal Eis) : ℂ :=
  quadraticRow K ((u.val*lambda^m)*primaryGenerator (D*E))

lemma residualQuadraticPhase_norm_le_one (K:Ideal Eis) (u:Eisˣ) (m:ℕ) (D E:Ideal Eis) :
    ‖residualQuadraticPhase K u m D E‖≤1 := quadraticRow_norm_le_one _ _

theorem residual_bracket_extracted_columns (I F Q:Ideal Eis) (hFQ:F∣Q)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (u:Eisˣ) (m:ℕ) (D E n b:Ideal Eis) :
    (∏P:PrimeIndex (rowResidualPart I Q),
      bracket (actualSextic P.val
        (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) P))
        (completedLocalExponent I F P.val)
        (Ideal.Quotient.mk P.val
          ((u.val*lambda^m)*primaryGenerator (D*n)*(primaryGenerator (E*b))^3)))=
      residualQuadraticPhase (rowResidualPart I Q) u m D E *
        quadraticRow (rowResidualPart I Q) (primaryGenerator (n*b)) := by
  simp_rw [completedLocalExponent_residual I F Q hFQ]
  rw [residual_bracket_product]
  rw [←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad),
    ←quadraticRow_eq_primeIndex _ (rowResidualPart_admissible I Q hbad)]
  simp only [primaryGenerator_mul,residualQuadraticPhase,
    canonical_quadraticRow_argument_mul _ (rowResidualPart_admissible I Q hbad)]
  ring

end

section
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def actualResidualModelRow (K:ℝ) (I Q:Ideal Eis) (hI:I≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (hIK:(Ideal.absNorm I:ℝ)≤K) :
    idealRange (completedResidualScale K I Q) := by
  refine ⟨rowResidualPart I Q,mem_idealRange.mpr ⟨rowResidualPart_admissible I Q hbad,?_⟩⟩
  rw [rowResidualPart_norm I Q hI,completedResidualScale]
  exact div_le_div_of_nonneg_right hIK (by positivity)

lemma actualResidualModelRow_val (K:ℝ) (I Q:Ideal Eis) (hI:I≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (hIK:(Ideal.absNorm I:ℝ)≤K) :
    (actualResidualModelRow K I Q hI hbad hIK).val=rowResidualPart I Q := rfl

lemma actualResidualModelRow_shell (K:ℝ) (I Q:Ideal Eis) (hI:I≠0)
    (hbad:∀P∈fixedBadPrimes,P∣Q) (hIK:(Ideal.absNorm I:ℝ)≤K)
    (hlo:K/2≤(Ideal.absNorm I:ℝ)) :
    completedResidualScale K I Q/2≤(Ideal.absNorm (actualResidualModelRow K I Q hI hbad hIK).val:ℝ) := by
  change completedResidualScale K I Q/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ)
  rw [rowResidualPart_norm I Q hI,completedResidualScale]
  have h:=div_le_div_of_nonneg_right hlo
    (show 0≤(Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ) by positivity)
  convert h using 1 ; ring

theorem completedBranchScale_raw_argument {ι:Type*} [Fintype ι]
    (K X c r:ℝ) (I F Q:Ideal Eis) (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (e:ι→Fin 3) (k n b:Ideal Eis) (hK:0<completedResidualScale K I Q)
    (hc:0<c) (hk:k≠0) :
    ((completedBranchScale K (X/c) I F Q P e)⁻¹*
      (completedResidualScale K I Q/(Ideal.absNorm k:ℝ))^2)*r^3*
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3=
    X*r^3*
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1*n):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2*b):ℝ)^3/
      (c*(Ideal.absNorm k:ℝ)^2*(Ideal.absNorm (∏i,P i):ℝ)^2) := by
  have hkN:(Ideal.absNorm k:ℝ)≠0:=by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hk)
  have hpN:(Ideal.absNorm (∏i,P i):ℝ)≠0:=by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _=>NeZero.ne (P i))))
  simp only [completedBranchScale,inv_div,map_mul,Nat.cast_mul]
  field_simp [hK.ne',hc.ne',hkN,hpN]

end

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def residualModelRowPhase {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (u:Eisˣ) (D E:Ideal Eis) (m:ℕ) (k:idealRange K) : ℂ :=
  rowPhase m k*residualQuadraticPhase k.val u m D E

lemma residualModelRowPhase_norm_le_one {K:ℝ} (rowPhase:ℕ→idealRange K→ℂ)
    (hphase:∀m k,‖rowPhase m k‖≤1) (u:Eisˣ) (D E:Ideal Eis) (m:ℕ) (k:idealRange K) :
    ‖residualModelRowPhase rowPhase u D E m k‖≤1 := by
  rw [residualModelRowPhase,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (hphase m k)).trans (residualQuadraticPhase_norm_le_one k.val u m D E)

theorem residual_coefficient_eq_canonical {ι:Type*} [Fintype ι]
    (I F Q:Ideal Eis) (hFQ:F∣Q) (hbad:∀P∈fixedBadPrimes,P∣Q)
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (u:Eisˣ)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (rowPhase:ℕ→ℂ) (m:ℕ) (n b:Ideal Eis) :
    let D:=reflectionExtractedDivisor P j e 1
    let E:=reflectionExtractedDivisor P j e 2
    (rowPhase m*(∏p:PrimeIndex (rowResidualPart I Q),
        bracket (actualSextic p.val (admissiblePrimeGood _ (rowResidualPart_admissible I Q hbad) p))
          (completedLocalExponent I F p.val)
          (Ideal.Quotient.mk p.val ((u.val*lambda^m)*primaryGenerator (D*n)*(primaryGenerator (E*b))^3))) *
      η m (D*n) (E*b)*reflectedBranch P hg j e (primaryGenerator (D*n)) (primaryGenerator (E*b)))/
        ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*b):ℝ):ℝ):ℂ)=
      4*canonicalRawBranchCoefficient P hg j e ρ q
        (fun l a c=>η l (D*a) (E*c))
        (fun l=>rowPhase l*residualQuadraticPhase (rowResidualPart I Q) u l D E)
        (rowResidualPart I Q) m n b := by
  dsimp only
  rw [residual_bracket_extracted_columns I F Q hFQ hbad]
  unfold canonicalRawBranchCoefficient reflectedDyadicCoefficient
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  norm_num
  ring

end CompletedGauss

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def pool (I Q Q0:Ideal Eis) : Finset (Ideal Eis) :=
  (completedReflectionPool I Q).filter (fun P=>¬Q0≤P)

lemma pool_subset (I Q Q0:Ideal Eis) : pool I Q Q0⊆completedReflectionPool I Q :=
  Finset.filter_subset _ _
lemma pool_maximal (I Q Q0:Ideal Eis) (P:pool I Q Q0) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_good (I Q Q0:Ideal Eis) (P:pool I Q Q0) : lambda∉P.val :=
  completedReflectionPool_good I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_odd (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ringChar (Eis⧸P.val)≠2 :=
  completedReflectionPool_odd I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_divides (I Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (P:pool I Q Q0) : P.val∣I*Q :=
  completedReflectionPool_divides I Q hI hQ ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_nonresidual (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ¬P.val∣rowResidualPart I Q :=
  completedReflectionPool_nonresidual I Q ⟨P.val,pool_subset I Q Q0 P.property⟩
lemma pool_free (I Q Q0:Ideal Eis) (P:pool I Q Q0) : ¬Q0≤P.val :=
  (Finset.mem_filter.mp P.property).2

lemma pool_eq_on_fiber (I J Q Q0:Ideal Eis) (hI:I≠0) (hJ:J≠0) (hQ:Q≠0)
    (hA:rowPowerfulPart I=rowPowerfulPart J) (hT:rowMaskPart I Q=rowMaskPart J Q) :
    pool I Q Q0=pool J Q Q0 := by
  unfold pool
  rw [completedReflectionPool_eq_on_fiber I J Q hI hJ hQ hA hT]

end

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def reflectionChoiceValue (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6)
    (P:Ideal Eis) : Fin 6 :=
  if h:P∈pool I Q Q0 then e ⟨P,h⟩ else 0

def reflectionActivePool (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6) : Finset (Ideal Eis) :=
  (pool I Q Q0).filter (fun P=>reflectionSixActive (reflectionChoiceValue I Q Q0 e P))

lemma reflectionActivePool_subset (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6) :
    reflectionActivePool I Q Q0 e⊆pool I Q Q0 := Finset.filter_subset _ _

lemma mem_reflectionActivePool (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6)
    (P:pool I Q Q0) :
    P.val∈reflectionActivePool I Q Q0 e ↔ reflectionSixActive (e P) := by
  rw [reflectionActivePool, Finset.mem_filter]
  simp only [P.property, true_and]
  rw [reflectionChoiceValue, dite_eq_left P.property]

lemma reflectionActivePool_encode (I Q Q0:Ideal Eis)
    (A:Finset (pool I Q Q0)) (e:A→Fin 3) :
    reflectionActivePool I Q Q0 (encodeReflectionSix ⟨A,e⟩)=A.image Subtype.val := by
  ext P
  constructor
  · intro hP
    let p:pool I Q Q0:=⟨P,reflectionActivePool_subset I Q Q0 _ hP⟩
    have hp:p∈A:=(reflectionSixActive_encode ⟨A,e⟩ p).mp
      ((mem_reflectionActivePool I Q Q0 _ p).mp hP)
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  · intro hP
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hP
    exact (mem_reflectionActivePool I Q Q0 _ p).mpr ((reflectionSixActive_encode ⟨A,e⟩ p).mpr hp)

def reflectionActiveLabel (I Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6)
    (P:reflectionActivePool I Q Q0 e) : Fin 3 :=
  reflectionSixLabel (e ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩)

def sixReflectedBranch (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6)
    (amplitude:ℕ→Ideal Eis→Ideal Eis→ℂ) (hamp:∀m n b,‖amplitude m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q where
  levelScale:=levelScale
  levelScale_pos:=hlevel
  levelScale_le:=hbound
  primes:=reflectionActivePool I Q Q0 e
  maximal:=fun P=>pool_maximal I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  good:=fun P=>pool_good I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  coprime:=by
    intro P R hPR
    let : P.val.IsMaximal:=pool_maximal I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
    let : R.val.IsMaximal:=pool_maximal I Q Q0 ⟨R.val,reflectionActivePool_subset I Q Q0 e R.property⟩
    exact Ideal.isCoprime_of_isMaximal (Subtype.val_injective.ne hPR)
  divides:=fun P=>pool_divides I Q Q0 hI hQ ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  nonresidual:=fun P=>pool_nonresidual I Q Q0 ⟨P.val,reflectionActivePool_subset I Q Q0 e P.property⟩
  label:=reflectionActiveLabel I Q Q0 e
  nColumns:=fun i=>dualIdealDyad i.2.2
  bColumns:=fun i=>dualIdealDyad i.2.1
  nBounds:=fun i n hn=>dualIdealDyad_bounds i.2.2 n hn
  bBounds:=fun i b hb=>dualIdealDyad_bounds i.2.1 b hb
  amplitude:=fun i=>amplitude i.1
  amplitude_bound:=fun i n _ b _=>hamp i.1 n b
  rowPhase:=fun i=>rowPhase i.1
  rowPhase_bound:=fun i k=>hrow i.1 k

end

section
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspBranch (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    ReflectedBranchData levelBound K I F Q :=
  (sixReflectedBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e
    (fixedCuspArrayWithPhase cusp u phaseArray)
    (fixedCuspArrayWithPhase_norm_le_one cusp u phaseArray hphase) rowPhase hrow).withExtractedFixedCuspArrayWithPhase cusp u phaseArray hphase rowPhase hrow

lemma sixPhaseFixedCuspBranch_primes (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    (sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow).primes=reflectionActivePool I Q Q0 e := rfl

lemma sixPhaseFixedCuspBranch_amplitude (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1)
    (i:ℕ×ℕ×ℕ) (n b:Ideal Eis) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    let D:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 1
    let E:=reflectionExtractedDivisor (fun p:d.primes=>p.val)
      (fun p=>completedLocalExponent I F p.val) d.label 2
    d.amplitude i n b=phaseArray i.1 (D*n) (E*b)*fixedConjugateCuspArray cusp u i.1 (D*n) (E*b) := rfl

lemma sixPhaseFixedCuspBranch_scale (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K X levelBound levelScale:ℝ) (hlevel:0<levelScale) (hbound:levelScale≤levelBound)
    (e:pool I Q Q0→Fin 6) (cusp:Fin 3) (u:Eisˣ)
    (phaseArray:ℕ→Ideal Eis→Ideal Eis→ℂ) (hphase:∀m n b,‖phaseArray m n b‖≤1)
    (rowPhase:ℕ→idealRange (completedResidualScale K I Q)→ℂ) (hrow:∀m k,‖rowPhase m k‖≤1) :
    let d:=sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound levelScale hlevel hbound e cusp u
      phaseArray hphase rowPhase hrow
    completedBranchScale K (X/d.levelScale) I F Q (fun P:d.primes=>P.val) d.label=
      completedBranchScale K (X/levelScale) I F Q
        (fun P:reflectionActivePool I Q Q0 e=>P.val) (reflectionActiveLabel I Q Q0 e) := rfl

end
section

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance poolMaximal (I Q Q0:Ideal Eis) (P:pool I Q Q0) : P.val.IsMaximal :=
  pool_maximal I Q Q0 P
noncomputable local instance poolField (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Field (Eis⧸P.val) :=
  Ideal.Quotient.field P.val
noncomputable local instance poolFintype (I Q Q0:Ideal Eis) (P:pool I Q Q0) : Fintype (Eis⧸P.val) :=
  Fintype.ofFinite _

def reflectionInactiveStratumWeight (I F Q Q0:Ideal Eis) (A:Finset (pool I Q Q0)) : ℂ :=
  ∏P∈(Finset.univ:Finset (pool I Q Q0))\A,
    zeroFourierCoefficient (actualSextic P.val (pool_good I Q Q0 P))
      (completedLocalExponent I F P.val)

lemma reflectionInactiveStratumWeight_norm_le_one (I F Q Q0:Ideal Eis)
    (A:Finset (pool I Q Q0)) : ‖reflectionInactiveStratumWeight I F Q Q0 A‖≤1 := by
  rw [reflectionInactiveStratumWeight,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
  intro P _
  by_cases hj:completedLocalExponent I F P.val=0
  · rw [hj]
    exact zeroFourierCoefficient_zero_norm_le_one _
  · have he:=canonical_zeroFourierCoefficient P.val (pool_good I Q Q0 P)
      (pool_odd I Q Q0 P) (completedLocalExponent I F P.val)
      (Nat.mod_lt _ (by decide : 0<6))
    have hz:zeroFourierCoefficient (actualSextic P.val (pool_good I Q Q0 P))
        (completedLocalExponent I F P.val)=0 := by
      simpa only [actualSextic,ite_eq_right hj] using he
    rw [hz]
    simp

def reflectionSixInactiveWeight (I F Q Q0:Ideal Eis) (e:pool I Q Q0→Fin 6) : ℂ :=
  if reflectionSixValid e then reflectionInactiveStratumWeight I F Q Q0 (reflectionSixSupport e) else 0

lemma reflectionSixInactiveWeight_norm_le_one (I F Q Q0:Ideal Eis)
    (e:pool I Q Q0→Fin 6) : ‖reflectionSixInactiveWeight I F Q Q0 e‖≤1 := by
  unfold reflectionSixInactiveWeight
  split_ifs
  · exact reflectionInactiveStratumWeight_norm_le_one I F Q Q0 _
  · simp

lemma sum_reflectionSixInactiveWeight_unpad (I F Q Q0:Ideal Eis)
    (G:(pool I Q Q0→Fin 6)→ℂ) :
    (∑e:pool I Q Q0→Fin 6,reflectionSixInactiveWeight I F Q Q0 e*G e)=
      ∑A:Finset (pool I Q Q0),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_active_exceptional_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [ite_eq_left he,encode_decodeReflectionSix e he]
    simp only [reflectionSixInactiveWeight,ite_eq_left he,decodeReflectionSix]
  · simp only [ite_eq_right he,reflectionSixInactiveWeight,zero_mul]

abbrev SixReflectionIndex (rays:ℕ) (I Q Q0:Ideal Eis) :=
  Fin rays×(pool I Q Q0→Fin 6)

end

open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O

def sixPhaseFixedCuspFiber (rays:ℕ) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q Q0→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q Q0→Fin 3) (unit:SixReflectionIndex rays I Q Q0→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q Q0→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1) : ReflectedFiberData rays levelBound K I F Q where
  pool:=pool I Q Q0
  maximal:=pool_maximal I Q Q0
  divides:=pool_divides I Q Q0 hI hQ
  branch:=fun x=>sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound (levelScale x) (hlevel x) (hlevelBound x)
    x.2 (cusp x) (unit x) (phaseArray x) (hphase x) (rowPhase x) (hrow x)
  weight:=fun x=>rayWeight x*reflectionSixInactiveWeight I F Q Q0 x.2
  weight_bound:=by
    intro x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hray x)).trans (reflectionSixInactiveWeight_norm_le_one I F Q Q0 x.2)

theorem sixPhaseFixedCuspFiber_value (rays:ℕ) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K levelBound:ℝ) (levelScale:SixReflectionIndex rays I Q Q0→ℝ)
    (hlevel:∀x,0<levelScale x) (hlevelBound:∀x,levelScale x≤levelBound)
    (cusp:SixReflectionIndex rays I Q Q0→Fin 3) (unit:SixReflectionIndex rays I Q Q0→Eisˣ)
    (phaseArray:SixReflectionIndex rays I Q Q0→ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hphase:∀x m n b,‖phaseArray x m n b‖≤1)
    (rayWeight:SixReflectionIndex rays I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:SixReflectionIndex rays I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=sixPhaseFixedCuspFiber rays I F Q Q0 hI hQ K levelBound levelScale hlevel hlevelBound
      cusp unit phaseArray hphase rayWeight hray rowPhase hrow
    d.value W X ρ q k=
      ∑t:Fin rays,∑A:Finset (pool I Q Q0),∑e:A→Fin 3,
        reflectionInactiveStratumWeight I F Q Q0 A*rayWeight (t,encodeReflectionSix ⟨A,e⟩)*
          (d.branch (t,encodeReflectionSix ⟨A,e⟩)).value W X ρ q k := by
  dsimp only
  rw [ReflectedFiberData.value,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  calc
    _=∑e:pool I Q Q0→Fin 6,reflectionSixInactiveWeight I F Q Q0 e*
      (rayWeight (t,e)*(sixPhaseFixedCuspBranch I F Q Q0 hI hQ K levelBound (levelScale (t,e))
        (hlevel (t,e)) (hlevelBound (t,e)) e (cusp (t,e)) (unit (t,e))
        (phaseArray (t,e)) (hphase (t,e)) (rowPhase (t,e)) (hrow (t,e))).value W X ρ q k) := by
          apply Finset.sum_congr rfl
          intro e _
          dsimp only [sixPhaseFixedCuspFiber]
          ring
    _=_ := by
      rw [sum_reflectionSixInactiveWeight_unpad]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro e _
      dsimp only [sixPhaseFixedCuspFiber]
      exact (mul_assoc _ _ _).symm

end CompletedGauss.FreeReflection

end

end OAI
