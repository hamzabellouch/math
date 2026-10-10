import OAI.NumberTheory.DirichletL.MeanSquare.SourceRemainders

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

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FiniteGaussPhase (canonicalProductGauss_cross_factors)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma threeGaussRowFactor_empty
    (B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O)
    (hB : cubeActiveSupport B v ε₁ ε₂=∅) :
    threeGaussRowFactor p hp hcop hg ∅ ∅ B v ε₁ ε₂ C₁ C₂ d h=
      star (C₁ ∅)*C₂ ∅ := by
  let : IsEmpty {i:ι // i∈(((∅:Finset ι)∪∅)∪cubeActiveSupport B v ε₁ ε₂)} :=
    ⟨fun x=>by simpa [hB] using x.property⟩
  simp [MixedCrossSeparation.columnCoefficient,FiniteGaussPhase.canonicalProductCoefficient,
    threeGaussRowFactor,canonicalProductGauss_cross_factors,FiniteGaussPhase.angularFactor,
    blockRow,finiteSexticRow]

end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma canonicalCubeResidual_empty (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) :
    canonicalCubeResidual p hg b C negative Ψ m f H ∅=
      H ((if negative then b.rightDivisor else b.leftDivisor)∪C) := by
  simp [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,
    finiteSquarefreeRow,rowCoprimeMask]

def canonicalCubeDualZero (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) 0

theorem canonicalCubeDualZero_eq_density
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K=
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
          (star (H₁ (b.rightDivisor∪C))*H₂ (b.leftDivisor∪C))*
          (K:ℂ)*paperRadialFourier W 0*
          ∏i∈C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit,
            (1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i}))
      else 0 := by
  unfold canonicalCubeDualZero
  simp_rw [actualFirstKernel_zero]
  split_ifs with hB
  · simp only [threeGaussRowFactor_empty p hp hcop hg _ _ _ _ _ _ _ _ hB,
      canonicalCubeResidual_empty,Bool.false_eq_true,ite_true,ite_false,one_mul]
    rw [←Finset.sum_mul]
    have hprime (i : ι) : Prime (Ideal.span {p i}) :=
      Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
    have hd (D : Finset ι) : (primeProductNorm p D:ℂ)=
        (Ideal.absNorm (∏i∈D,Ideal.span {p i}):ℂ) := by
      rw [primeProductNorm_eq_ideal_norm,Complex.ofReal_natCast]
    simp_rw [hd]
    rw [primeSubset_moebius_norm_sum _ hprime hinj]
    ring
  · simp only [mul_zero,Finset.sum_const_zero]

theorem canonicalCubeDualZero_norm_le
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        ‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖*|K| *‖paperRadialFourier W 0‖ else 0 := by
  rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj]
  split_ifs with hB
  · let M := C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
    have hprod : (∏i∈M,(1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i})))=
        ((∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i}))):ℝ) := by
      simp only [Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one,
        Complex.ofReal_div,Complex.ofReal_natCast]
    rw [show (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)=M from rfl,hprod]
    simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).1]
    calc
      _ ≤ 1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖*
          ∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i})) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (abs_nonneg _)) (norm_nonneg _))
          (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).1
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_of_le_one_right
          (show 0≤(1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖) by positivity)
          (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).2
  · simp

end

open ActualEisensteinCubic
open FirstPassCubeLabels

theorem boundedPrimeSupports_card_positive {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (X : ℝ) (hX : 0<X) :
    ((boundedPrimeSupports p F X).card:ℝ)≤128*X := by
  by_cases hx : 1≤X
  · exact boundedPrimeSupports_card p hinj F X hx
  · have he : boundedPrimeSupports p F X=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      exact hx ((primeProductNorm_ge_one p hp S).trans (Finset.mem_filter.mp hS).2)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end SecondPassArithmetic

namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open SecondPassArithmetic (boundedPrimeSupports boundedPrimeSupports_card_positive
  columnLog_norm_upper firstFrequencyDisk primeProductNorm_ge_one)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem actualFirstKernel_complement_eq_pairs
    (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) (T : Finset O) :
    (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val)=
      ∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
        ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val
        else 0 := by
  have hs (N Q : Finset ι) : Summable (fun h:{h:O // h∉T}=>if Disjoint N Q then
      canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0) := by
    by_cases hNQ : Disjoint N Q
    · simp only [hNQ,ite_true]
      exact (canonicalPairMode_summable p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd).subtype _
    · simp only [hNQ,ite_false]
      exact summable_zero
  change (∑'h:{h:O // h∉T},∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
    canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0)=_
  rw [Summable.tsum_finsetSum (fun N hN=>summable_sum (fun Q hQ=>hs N Q))]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Summable.tsum_finsetSum (fun Q hQ=>hs N Q)]
  apply Finset.sum_congr rfl
  intro Q hQ
  split_ifs <;> simp

end

theorem full_uniform_actualFirstKernel_disk_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),Disjoint F B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0≤G₁ → 0≤G₂ → 0<X₁ → 0<X₂ → 0<K → 0≤P →
      (∀N∈F.powerset,‖C₁ N‖≤G₁) → (∀N∈F.powerset,‖C₂ N‖≤G₂) →
      (∀N∈F.powerset,C₁ N≠0 → columnLog p X₁ N≤M₁) →
      (∀N∈F.powerset,C₂ N≠0 → columnLog p X₂ N≤M₂) →
      ∀(d : O),d≠0 →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_disk_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hFB C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂ hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hS₁ hS₂ d hd
  dsimp only
  let U₁:=X₁*Real.exp M₁
  let U₂:=X₂*Real.exp M₂
  let S:=cubeActiveSupport B v ε₁ ε₂
  let T:=firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
  let slow:=K/(‖eisEmbedding d‖^2*primeProductNorm p S*U₁*U₂)
  let tail:ℝ:=(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)
  let Q:ℝ:=G₁*G₂*K*tail
  have hU₁:0<U₁:=mul_pos hX₁ (Real.exp_pos _)
  have hU₂:0<U₂:=mul_pos hX₂ (Real.exp_pos _)
  have hNd:0<‖eisEmbedding d‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hslow:0<slow:=div_pos hK (mul_pos (mul_pos (mul_pos hNd (primeProductNorm_pos p hp S)) hU₁) hU₂)
  have hH:0≤P/Real.exp (M₁+M₂):=div_nonneg hP (Real.exp_pos _).le
  have htail:0≤tail:=by dsimp [tail]; positivity
  have hQ:0≤Q:=mul_nonneg (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le) htail
  let rem (N R:Finset ι):ℂ:=if Disjoint N R then
    ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val else 0
  have hnzero (N R:Finset ι) (hn:C₁ N=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hn]
  have hrzero (N R:Finset ι) (hr:C₂ R=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hr]
  have heq : (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val)=
      ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,rem N R := by
    rw [actualFirstKernel_complement_eq_pairs p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K hK d hd T]
    change (∑N∈F.powerset,∑R∈F.powerset,rem N R)=_
    calc
      _ = ∑N∈boundedPrimeSupports p F U₁,∑R∈F.powerset,rem N R := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro N hN hn
        have hz:C₁ N=0:=by
          by_contra h
          exact hn (Finset.mem_filter.mpr ⟨hN,columnLog_norm_upper p hp X₁ M₁ hX₁ N (hS₁ N hN h)⟩)
        simp only [hnzero N _ hz,Finset.sum_const_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro N hN
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro R hR hr
        have hz:C₂ R=0:=by
          by_contra h
          exact hr (Finset.mem_filter.mpr ⟨hR,columnLog_norm_upper p hp X₂ M₂ hX₂ R (hS₂ R hR h)⟩)
        exact hrzero N R hz
  have hrem (N:Finset ι) (hN:N∈boundedPrimeSupports p F U₁) (R:Finset ι) (hR:R∈boundedPrimeSupports p F U₂):‖rem N R‖≤Q:=by
    have hNF: N∈F.powerset:=(Finset.mem_filter.mp hN).1
    have hRF: R∈F.powerset:=(Finset.mem_filter.mp hR).1
    by_cases hn:C₁ N=0
    · rw [hnzero N R hn,norm_zero]; exact hQ
    by_cases hr:C₂ R=0
    · rw [hrzero N R hr,norm_zero]; exact hQ
    by_cases hNR:Disjoint N R
    · have hNB:=hFB.mono_left (Finset.mem_powerset.mp hNF)
      have hRB:=hFB.mono_left (Finset.mem_powerset.mp hRF)
      have hNS:Disjoint N S:=hNB.mono_right (Finset.filter_subset _ _)
      have hRS:Disjoint R S:=hRB.mono_right (Finset.filter_subset _ _)
      have hnorm:primeProductNorm p ((N∪R)∪S)=primeProductNorm p N*primeProductNorm p R*primeProductNorm p S:=by
        rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hNS,hRS⟩),primeProductNorm_union p _ _ hNR]
      have hprod:=mul_le_mul (Finset.mem_filter.mp hN).2 (Finset.mem_filter.mp hR).2
        (primeProductNorm_pos p hp R).le hU₁.le
      have hscale:slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S)):=by
        apply div_le_div_of_nonneg_left hK.le (mul_pos hNd (primeProductNorm_pos p hp _))
        rw [hnorm]
        calc
          _ ≤ ‖eisEmbedding d‖^2*(U₁*U₂*primeProductNorm p S):=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
          _ = _ := by ring
      have hnroot:1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖:=by
        have hx:=primeProductNorm_ge_one p hp ((N∪R)∪S)
        change 1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖^2 at hx
        nlinarith [norm_nonneg (eisEmbedding (∏i∈(N∪R)∪S,p i))]
      have hpre:(K/‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖)*(‖C₁ N‖*‖C₂ R‖)≤G₁*G₂*K:=by
        calc
          _ ≤ K*(G₁*G₂):=mul_le_mul (div_le_self hK.le hnroot)
            (mul_le_mul (hC₁ N hNF) (hC₂ R hRF) (norm_nonneg _) hG₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
          _ = _ := by ring
      have hfrac:(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S))))^2*(1+P/Real.exp (M₁+M₂))^A)≤tail:=by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (sq_pos_of_pos (lt_min (by norm_num) hslow)) (pow_pos (by linarith) _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_min zero_le_one hslow.le)
          (min_le_min_left 1 hscale) 2) (pow_nonneg (by linarith) _)
      have hpair:=hb p hp hcop hg hc N R B v ε₁ ε₂ hNR hNB hRB C₁ C₂ W (fun _=>1) (fun _=>1)
        X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP (hS₁ N hNF hn) (hS₂ R hRF hr) d hd
      simp only [norm_one,one_mul] at hpair
      dsimp only [rem]
      rw [ite_eq_left hNR]
      exact hpair.trans (mul_le_mul hpre hfrac (by positivity) (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le))
    · simp only [rem,ite_eq_right hNR,norm_zero];exact hQ
  rw [heq]
  calc
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,‖rem N R‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun N hN=>norm_sum_le _ _))
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,Q:=
      Finset.sum_le_sum (fun N hN=>Finset.sum_le_sum (fun R hR=>hrem N hN R hR))
    _ = ((boundedPrimeSupports p F U₁).card:ℝ)*((boundedPrimeSupports p F U₂).card:ℝ)*Q:=by simp;ring
    _ ≤ (128*U₁)*(128*U₂)*Q:=mul_le_mul_of_nonneg_right
      (mul_le_mul (boundedPrimeSupports_card_positive p hp hinj F U₁ hU₁)
        (boundedPrimeSupports_card_positive p hp hinj F U₂ hU₂) (Nat.cast_nonneg _) (by positivity)) hQ
    _ = _ := by dsimp [Q,tail,slow,U₁,U₂,S];ring

end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))
  (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)

include hinj

theorem canonicalCubeDualZero_support
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (ell K M : ℝ) (hell : 0<ell) (hgM : ∀t,g₁ t≠0→t≤M)
    (hC : ¬primeProductNorm p C≤ell*Real.exp M) :
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K=0 := by
  have hz : g₁ (columnLog p ell (b.rightDivisor∪C))=0 := by
    by_contra h
    exact hC ((primeProductNorm_mono p hp (Finset.subset_union_right)).trans
      (columnLog_norm_upper p hp ell M hell _ (hgM _ h)))
  rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj]
  split_ifs <;> simp [hz]

include hc

theorem canonicalCubeDualZero_fixed_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (G₁ G₂ ell K : ℝ) (hG₁ : 0≤G₁) (_hG₂ : 0≤G₂)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) :
    ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        G₁*G₂*|K| *‖paperRadialFourier W 0‖ else 0 := by
  apply (canonicalCubeDualZero_norm_le p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hg₁ _) (hg₂ _) (norm_nonneg _) hG₁) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

theorem canonicalCubeZero_common_sum_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (labels : Finset (Ideal O))
    (a : Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (Γ G₁ G₂ ell K M : ℝ) (hΓ : 0≤Γ) (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hell : 0<ell)
    (ha : ∀C∈(pool\b.support).powerset,∀I∈labels,‖a C I‖≤Γ)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) (hgM : ∀t,g₁ t≠0→t≤M) :
    ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (128*(ell*Real.exp M))*(labels.card:ℝ)*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) else 0 := by
  let z (C:Finset ι) (I:Ideal O):ℂ:=canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
    (ConcretePrimeRowBridge.idealGenerator I)
    (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K
  let Q:ℝ:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hL:0<ell*Real.exp M:=mul_pos hell (Real.exp_pos _)
  have heq : (∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I)=
      ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,a C I*z C I := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro C hC hnot
    have hbnd : ¬primeProductNorm p C≤ell*Real.exp M:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
    apply Finset.sum_eq_zero
    intro I hI
    rw [show z C I=0 from canonicalCubeDualZero_support p hp hcop hg hinj pool b C Ψ₁ Ψ₂ m₁ m₂ _ g₁ g₂ W ell K M hell hgM hbnd,mul_zero]
  change ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I‖≤_
  rw [heq]
  by_cases hb : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  · rw [ite_eq_left hb]
    have hpnt (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M)) (I:Ideal O) (hI:I∈labels):‖a C I*z C I‖≤Q:=by
      rw [norm_mul]
      have hz:=canonicalCubeDualZero_fixed_bound p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I) g₁ g₂ W G₁ G₂ ell K hG₁ hG₂ hg₁ hg₂
      rw [ite_eq_left hb] at hz
      exact mul_le_mul (ha C (Finset.mem_filter.mp hC).1 I hI) hz (norm_nonneg _) hΓ
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,‖a C I*z C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,Q:=
        Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun I hI=>hpnt C hC I hI))
      _ = ((boundedPrimeSupports p (pool\b.support) (ell*Real.exp M)).card:ℝ)*(labels.card:ℝ)*Q:=by simp;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj _ _ hL) (Nat.cast_nonneg _)) hQ
  · rw [ite_eq_right hb]
    have hz (C:Finset ι) (I:Ideal O):z C I=0:=by
      dsimp [z]
      rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj,ite_eq_right hb]
    simp only [hz,mul_zero,Finset.sum_const_zero,norm_zero,le_refl]

end

theorem full_uniform_canonicalFirstZero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ ell K M B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<ell → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) → (∀t,g₁ t≠0→t≤M) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      C*B^(1+ε)*(ell*Real.exp M)*F*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) := by
  obtain ⟨C,hC,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨C*128*128,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Γ G₁ G₂ ell K M B F hΓ hG₁ hG₂ hell hB hF hΨ₁ hΨ₂ hadm hb1 hb2 hI0 hIF ha hg₁ hg₂ hgM
  let Q:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  let good:=fun b:CubeCoordinates ι=>cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:((bs.filter good).card:ℝ)≤C*B^(1+ε):=by
    have h:=hcount p hp hinj (bs.filter good) B 1 hB (by norm_num)
      (fun b hb=>hadm b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb1 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb2 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>by
        have he : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ := (Finset.mem_filter.mp hb).2
        rw [he]
        simp)
    simpa only [mul_one] using h
  calc
    _ ≤ ∑b∈bs,‖∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,if good b then (128*(ell*Real.exp M))*(labels.card:ℝ)*Q else 0:=by
      apply Finset.sum_le_sum
      intro b hb
      exact canonicalCubeZero_common_sum_bound p hp hcop hg hinj hc pool b labels (a b) Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ g₁ g₂ W Γ G₁ G₂ ell K M hΓ hG₁ hG₂ hell (ha b hb) hg₁ hg₂ hgM
    _ = ((bs.filter good).card:ℝ)*((128*(ell*Real.exp M))*(labels.card:ℝ)*Q):=by
      rw [←Finset.sum_filter];simp
    _ ≤ (C*B^(1+ε))*((128*(ell*Real.exp M))*(128*F)*Q):=by
      apply mul_le_mul hbcount _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlabel (by positivity)) hQ
    _ = _ := by dsimp [Q];ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma originalLabelColumn_core_norm_le
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀u,‖Ψ u‖≤1) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖originalLabelColumn p hg B ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H) c f S‖≤‖H S‖ := by
  have hm (z:O):‖rowCoprimeMask (fun i=>Ideal.span {p i}) S z‖≤1:=by
    unfold rowCoprimeMask;split_ifs <;> simp
  have hrow (z:O):‖finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z‖^4≤1:=by
    simpa using pow_le_pow_left₀ (norm_nonneg _)
      (finiteSquarefreeRow_norm_le_one (fun i=>Ideal.span {p i}) hg S z) 4
  simp only [originalLabelColumn,multiplicativeCoreColumn,norm_mul,norm_pow]
  calc
    _ ≤ 1*‖H S‖*1*1*1 := by
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul
            (mul_le_mul_of_nonneg_right
              ((mul_le_mul (hΨ _) (hm m) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) (norm_nonneg _))
            (hm _) (norm_nonneg _) (by positivity))
          (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity))
        (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma originalLabelColumn_core_test_ne_zero
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι)
    (h : originalLabelColumn p hg B ε₁ ε₂ negative
      (multiplicativeCoreColumn p Ψ m H) c f S≠0) : H S≠0 := by
  intro hz
  apply h
  simp only [originalLabelColumn,multiplicativeCoreColumn,hz,mul_zero,zero_mul]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem canonicalFirstFrequencyRadius_eq_global
    (b : CubeCoordinates ι) (hb : b.Admissible) (C D : Finset ι)
    (Ksrc K ell : ℝ) (hKsrc : 0<Ksrc) (hK : 0<K) :
    canonicalFirstFrequencyRadius p b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit (primeSubsetGenerator (fun i=>Ideal.span {p i}) D)
      (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
      (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) Ksrc (Ksrc/K)=
    globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D) := by
  have hl:b.swap.leftBit=b.rightBit:=rfl
  have hr:b.swap.rightBit=b.leftBit:=rfl
  simp only [canonicalFirstFrequencyRadius,globalFirstFrequencyScale,sourceGlobalBlock,
    cube_swap_support,cube_swap_sum,hl,hr,
    cubeActiveSupport_swap,primeSubsetGenerator_norm_eq_productNorm,
    CubeCoordinates.aLabel_left p b hb,CubeCoordinates.aLabel_right p b hb]
  change (Ksrc/K)*(primeProductNorm p D*primeProductNorm p
    (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*
    (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))*
    (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)))/Ksrc = _
  have hC:primeProductNorm p C≠0:=(primeProductNorm_pos p hp C).ne'
  have hL:primeProductNorm p b.leftDivisor≠0:=(primeProductNorm_pos p hp _).ne'
  have hR:primeProductNorm p b.rightDivisor≠0:=(primeProductNorm_pos p hp _).ne'
  simp only [primeProductNorm]
  simp only [primeProductNorm] at hC hL hR
  field_simp

end

theorem full_uniform_canonicalSource_kernel_tail (A : ℕ) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι),b.Admissible → ∀ C D:Finset ι,Disjoint C b.support →
      ∀(Ψ₁ Ψ₂:O→*ℂ),(∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      ∀(m₁ m₂ f:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (G₁ G₂ M₁ M₂ Ksrc K ell:ℝ),
      0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
      let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
      let U₁:=X₁*Real.exp M₁
      let U₂:=X₂*Real.exp M₂
      let slow:=Ksrc/(primeProductNorm p D*primeProductNorm p
        (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*U₁*U₂)
      let T:=firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun S=>g₁ (columnLog p ell S)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun S=>g₂ (columnLog p ell S)))
        W (fun _=>1) (fun _=>1) 1 1 Ksrc
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*Ksrc)*
        ((Ctail*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+(Ksrc/K)/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,Ctail,hCtail,hbound⟩:=full_uniform_actualFirstKernel_disk_remainder A
  refine ⟨s,Ctail,hCtail,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool b hb C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂
  dsimp only
  let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
  let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
  have hX₁:0<X₁:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hX₂:0<X₂:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hFB:Disjoint (pool\(b.support∪C)) b.support:=Finset.disjoint_left.mpr (fun i hi hb=>
    (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hb))
  let C₁:=originalLabelColumn p hg b.support b.leftBit b.rightBit true
    (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) (∏i∈C,p i) f
  let C₂:=originalLabelColumn p hg b.support b.leftBit b.rightBit false
    (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) (∏i∈C,p i) f
  have hcoef₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₁ N‖≤G₁:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit true Ψ₁ hΨ₁ m₁ _ f _ N).trans (hg₁ _)
  have hcoef₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₂ N‖≤G₂:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit false Ψ₂ hΨ₂ m₂ _ f _ N).trans (hg₂ _)
  have hs₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₁ N≠0):columnLog p X₁ N≤M₁:=
    hM₁ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit true Ψ₁ m₁ _ f _ N hn)
  have hs₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₂ N≠0):columnLog p X₂ N≤M₂:=
    hM₂ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit false Ψ₂ m₂ _ f _ N hn)
  have h:=hbound p hp hinj hcop hg hc (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit hFB C₁ C₂ W
    G₁ G₂ X₁ X₂ Ksrc (Ksrc/K) M₁ M₂ hG₁ hG₂ hX₁ hX₂ hKsrc (div_pos hKsrc hK).le
    hcoef₁ hcoef₂ hs₁ hs₂ (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) (primeSubsetGenerator_ne_zero _ _)
  rw [canonicalFirstFrequencyRadius_eq_global p hp b hb C D Ksrc K ell hKsrc hK] at h
  simp only [primeSubsetGenerator_norm_eq_productNorm] at h
  have heq := fun h:O=>canonical_log_kernel p hp hcop hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ f
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h g₁ g₂ W Ksrc ell hell
  simp_rw [heq]
  exact h

end SecondPassArithmetic

end

end OAI
