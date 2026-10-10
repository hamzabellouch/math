import OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer

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

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FourierBridge (logPhase)

def initialOuterWeight {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (q : Frequency) (x : SecondExpansionData ι) : ℂ :=
  w x * outerWindow V (z x) (ud x) (ue x) (uv x) (kap x) *
    logPhase (q.1 + q.2.1) (z x) * logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)

lemma initialOuterWeight_continuous {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (x : SecondExpansionData ι) :
    Continuous (fun q => initialOuterWeight V w z ud ue uv kap q x) := by
  have h₁ : Continuous (fun q : Frequency => logPhase (q.1 + q.2.1) (z x)) :=
    (FourierBridge.logPhase_continuous_left (z x)).comp
    (continuous_fst.add continuous_snd.fst)
  have h₂ : Continuous (fun q : Frequency => logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)) :=
    (FourierBridge.logPhase_continuous_left (kap x - ud x - 2 * ue x - 2 * uv x)).comp
    continuous_snd.snd
  unfold initialOuterWeight
  fun_prop

lemma initialOuterWeight_norm {ι : Type*} (V : Fin 7 → ℝ → ℂ) (w : SecondExpansionData ι → ℂ)
    (z ud ue uv kap : SecondExpansionData ι → ℝ) (q : Frequency) (x : SecondExpansionData ι) :
    ‖initialOuterWeight V w z ud ue uv kap q x‖ =
      ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ := by
  simp only [initialOuterWeight, norm_mul, FourierBridge.logPhase_norm, mul_one]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def initialSourceSum (s : Finset (SecondExpansionData ι)) (w : SecondExpansionData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : SecondExpansionData ι → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2
    (sourceObservation p x).1 (-(sourceObservation p x).1) A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem initialSource_eq_integrated
    (s : Finset (SecondExpansionData ι)) (w : SecondExpansionData ι → ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W b : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : SecondExpansionData ι → ℝ) (X₁ X₂ R : ℝ)
    (hsep : ∀ x ∈ s,
      postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
        A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R =
      separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
        A₁ A₂ b V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂) :
    initialSourceSum p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
      integratedSourceMode p hp hcop hg (𝓕 A₁) (𝓕 A₂) b s
        (initialOuterWeight V w z ud ue uv kap) F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ := by
  let Q : SecondExpansionData ι → Frequency → ℂ := fun x q =>
    initialOuterWeight V w z ud ue uv kap q x *
      star (fixedChildRow p hp hcop hg F Ψ₁ m
        (fixedSecondTest p (V 5) X₁ q.1 q.2.2 true) (sourceObservation p x).2 (sourceObservation p x).1) *
      fixedChildRow p hp hcop hg F Ψ₂ m
        (fixedSecondTest p (V 6) X₂ q.2.1 q.2.2 false) (sourceObservation p x).2 (-(sourceObservation p x).1)
  let M : SecondExpansionData ι → ℝ := fun x =>
    (‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖) *
      rowMagnitude p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true *
      rowMagnitude p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
  have hc (x : SecondExpansionData ι) : Continuous (Q x) := by
    have hw := initialOuterWeight_continuous V w z ud ue uv kap x
    have h₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hw.mul h₁.star).mul h₂
  have hbound (x : SecondExpansionData ι) (q : Frequency) : ‖Q x q‖ ≤ M x := by
    dsimp only [Q, M]
    rw [norm_mul, norm_mul, norm_star, initialOuterWeight_norm]
    have h₁ := fixedRow_norm_le p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ q.1 q.2.2 true
    have h₂ := fixedRow_norm_le p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ q.2.1 q.2.2 false
    have hn₁ := rowMagnitude_nonneg p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 (V 5) X₁ true
    have hn₂ := rowMagnitude_nonneg p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) (V 6) X₂ false
    gcongr
  calc
    _ = ∑ x ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * Q x (t₁,t₂,t₃) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hsep x hx]
      unfold separatedPostCommon
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      dsimp [tripleCoefficient, Q, initialOuterWeight]
      ring
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * (∑ x ∈ s, Q x (t₁,t₂,t₃)) :=
      finite_triple_bounded_integral s (𝓕 A₁) (𝓕 A₂) b Q (fun x _ => hc x) M (fun x _ => hbound x)
    _ = _ := rfl

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation

theorem initial_source_uniform_transfer (ε : ℝ) (hε : 0<ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7→ℝ→ℂ) (M : Fin 7→ℝ)
    (hM : ∀j,0≤M j) (hV : ∀j x,V j x≠0→|x|≤M j) (N J : ℕ) :
    ∃ Cₐ : ℝ,0<Cₐ ∧ ∃ Cₛ : ℝ,0≤Cₛ ∧ ∀R:ℝ,0<R→∃b:𝓢(ℝ,ℂ),
      (∀t₁ t₂ t₃:ℝ,(1+R)^N*‖(𝓕 A₁) t₁*(𝓕 A₂) t₂*b t₃‖≤
        Cₛ*FirstPassCubeLabels.firstLogDensity J t₁*FirstPassCubeLabels.firstLogDensity J t₂*
          FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (r : O) (s : Finset (SecondExpansionData ι)) (T : Finset (O×O))
        (w : SecondExpansionData ι→ℂ) (A K : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O)
        (z ud ue uv kap : SecondExpansionData ι→ℝ) (X₁ X₂ : ℝ),
        0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
        (∀x∈s,sourceObservation p x∈T) → (∀y∈T,y.1≠0) →
        (∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
        (∀x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖≤A) →
        ‖initialSourceSum p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖≤
          A*Cₐ*K^ε*(∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖*
            sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ,hCₐ,htrans⟩ := integrated_source_transfer ε hε
  obtain ⟨Cₛ,hCₛ,hsep⟩ := full_uniform_postCommonSmoothPair_fixed_tests A₁ A₂ W V M hM hV N J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro R hR
  obtain ⟨b,hpoint,hid⟩ := hsep R hR
  refine ⟨b,hpoint,?_⟩
  intro ι _ p hp _ hcop hg hinj r s T w A K F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hA hK hs hmap hT hnorm hw
  have hsource := initialSource_eq_integrated p hp hcop hg s w F Ψ₁ Ψ₂ m A₁ A₂ W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid p hp hcop hg F Ψ₁ Ψ₂ m
      (sourceObservation p x).2 (sourceObservation p x).1 (-(sourceObservation p x).1)
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans p hp hcop hg hinj r s T (initialOuterWeight V w z ud ue uv kap) A K
    F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b hA hK hs hmap hT hnorm
  · intro q x hx
    rw [initialOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact initialOuterWeight_continuous V w z ud ue uv kap x

end

section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def initialLogIndex (x : SecondExpansionData ι) : SecondLogIndex :=
  (normLogBin (primeProductNorm p x.divisor),normLogBin (primeProductNorm p x.overlap),
    normLogBin (elementNorm (sourceObservation p x).1))

def initialLogColumn (Z B : ℝ) (j : SecondLogIndex) : ℝ :=
  Z/(secondLogE j*secondLogV j*B)

def initialLogLabel (j : SecondLogIndex) : ℝ := secondLogE j*secondLogV j*Real.exp 2

omit [DecidableEq ι] in
lemma sourceRow_nonzero (x : SecondExpansionData ι) (hk : x.frequency≠0) :
    (sourceObservation p x).1≠0 := mul_ne_zero (primeSubsetGenerator_ne_zero _ _) hk

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceLabel_span (x : SecondExpansionData ι) :
    Ideal.span {(sourceObservation p x).2}=
      (∏i∈x.divisor,Ideal.span {p i})*(∏i∈x.overlap,Ideal.span {p i}) := by
  simp only [sourceObservation,←Ideal.span_singleton_mul_span_singleton,
    primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,FiniteGaussPhase.span_finset_prod]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceLabel_norm (x : SecondExpansionData ι) :
    elementNorm (sourceObservation p x).2=primeProductNorm p x.divisor*primeProductNorm p x.overlap := by
  simp only [elementNorm,sourceObservation,map_mul,norm_mul,mul_pow,
    primeSubsetGenerator_norm_eq_productNorm,primeProductNorm]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceQuotient_nonzero (x : SecondExpansionData ι) (hE : x.divisor⊆x.sourceCommon) :
    secondExpansionQuotient p x≠0 := by
  rw [secondExpansionQuotient_of_subset p x hE]
  intro he
  have hh := secondMaskQuotient_spec p x.divisor x.sourceCommon hE
  rw [he,mul_zero] at hh
  exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hh

include hp in

theorem initial_log_coordinates (Z : ℝ) (hZ : 0<Z) (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hk : x.frequency≠0) :
    let j := initialLogIndex p x
    let B := elementNorm (secondExpansionQuotient p x)
    let X₀ := initialLogColumn Z B j
    |Real.log (primeProductNorm p x.overlap*X₀/residualScale p Z x)|≤2 ∧
    |Real.log (primeProductNorm p x.divisor/secondLogE j)|≤2 ∧
    |Real.log (primeProductNorm p x.overlap/secondLogV j)|≤2 ∧
    |Real.log (elementNorm (sourceObservation p x).1/secondLogK j)|≤2 := by
  dsimp only
  have he := normLogBin_error (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)
  have hv := normLogBin_error (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)
  have hn : 1≤elementNorm (sourceObservation p x).1 := element_norm_ge_one _ (sourceRow_nonzero p x hk)
  have hrow := normLogBin_error (elementNorm (sourceObservation p x).1) hn
  have hE0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor).ne'
  have hV0 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.overlap).ne'
  have hB0 := (SecondPassIntegration.elementNorm_pos _ (sourceQuotient_nonzero p hp x hE)).ne'
  have hE1 := (normLogScale_pos (normLogBin (primeProductNorm p x.divisor))).ne'
  have hV1 := (normLogScale_pos (normLogBin (primeProductNorm p x.overlap))).ne'
  have hratio : primeProductNorm p x.overlap*initialLogColumn Z
      (elementNorm (secondExpansionQuotient p x)) (initialLogIndex p x)/residualScale p Z x=
      (primeProductNorm p x.divisor/normLogScale (normLogBin (primeProductNorm p x.divisor)))*
      (primeProductNorm p x.overlap/normLogScale (normLogBin (primeProductNorm p x.overlap))) := by
    simp only [initialLogColumn,residualScale,initialLogIndex,secondLogE,secondLogV,
      elementNorm,primeSubsetGenerator_norm_eq_productNorm]
    have hZ0 := hZ.ne'
    dsimp [elementNorm] at hB0
    have hBn : ‖eisEmbedding (secondExpansionQuotient p x)‖≠0 := by
      intro hz
      apply hB0
      rw [hz]
      norm_num
    field_simp [hBn]

  refine ⟨?_,?_,?_,?_⟩
  · rw [hratio,Real.log_mul (div_ne_zero hE0 hE1) (div_ne_zero hV0 hV1),
      abs_of_nonneg (add_nonneg he.1 hv.1)]
    linarith [he.2,hv.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg he.1]
    linarith [he.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg hv.1]
    linarith [hv.2]
  · change |Real.log (_/normLogScale (normLogBin _))|≤2
    rw [abs_of_nonneg hrow.1]
    linarith [hrow.2]

include hp in

omit [DecidableEq ι] in
theorem initial_log_target_bounds (x : SecondExpansionData ι) (hk : x.frequency≠0) :
    elementNorm (sourceObservation p x).2 ≤ initialLogLabel (initialLogIndex p x) ∧
    elementNorm (sourceObservation p x).1≤secondLogK (initialLogIndex p x)*Real.exp 1 := by
  have he := (normLogBin_scale_bounds _ (primeProductNorm_ge_one p hp x.divisor)).2
  have hv := (normLogBin_scale_bounds _ (primeProductNorm_ge_one p hp x.overlap)).2
  have hk' := (normLogBin_scale_bounds _ (element_norm_ge_one _ (sourceRow_nonzero p x hk))).2
  refine ⟨?_,hk'⟩
  rw [sourceLabel_norm]
  have hh := mul_le_mul he hv (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (mul_nonneg (normLogScale_pos _).le (Real.exp_pos _).le)
  simpa only [initialLogLabel,initialLogIndex,secondLogE,secondLogV,
    show (2:ℝ)=1+1 by norm_num,Real.exp_add,mul_assoc,mul_left_comm,mul_comm] using hh

theorem initial_log_mass (Z B : ℝ) (hB : B≠0) (j : SecondLogIndex) :
    initialLogColumn Z B j*initialLogLabel j=Z/B*Real.exp 2 := by
  have he := (normLogScale_pos j.1).ne'
  have hv := (normLogScale_pos j.2.1).ne'
  unfold initialLogColumn initialLogLabel secondLogE secondLogV
  field_simp

theorem initial_log_radial (Z H B : ℝ) (hZ : Z≠0) (hB : B≠0) (j : SecondLogIndex) :
    H*secondLogK j/(secondLogE j^2*secondLogV j^2*initialLogColumn Z B j^2)=
      H*secondLogK j*B^2/Z^2 := by
  have he := (normLogScale_pos j.1).ne'
  have hv := (normLogScale_pos j.2.1).ne'
  unfold initialLogColumn secondLogE secondLogV
  field_simp

end

open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))

include hcop in
theorem sourceLabel_squarefree (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hV : Disjoint x.sourceCommon x.overlap) :
    Squarefree (Ideal.span {(sourceObservation p x).2}) := by
  have hd : Disjoint x.divisor x.overlap := hV.mono_left hE
  rw [sourceLabel_span,←Finset.prod_union hd]
  exact primeSpanProduct_squarefree p hcop _

include hcop in
theorem sourceMask_coprime (x : SecondExpansionData ι)
    (hE : x.divisor⊆x.sourceCommon) (hV : Disjoint x.sourceCommon x.overlap) :
    IsCoprime (Ideal.span {secondExpansionQuotient p x})
      (Ideal.span {(sourceObservation p x).2}) := by
  rw [secondExpansionQuotient_of_subset p x hE,secondMaskQuotient_span,sourceLabel_span]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.mul_right
  · apply IsCoprime.prod_right
    intro j hj
    exact hcop (fun he => (Finset.mem_sdiff.mp hi).2 (he.symm ▸ hj))
  · apply IsCoprime.prod_right
    intro j hj
    exact hcop (fun he => Finset.disjoint_left.mp hV (Finset.mem_sdiff.mp hi).1 (he.symm ▸ hj))

include hp in
theorem initialLogIndex_mem_box (Z M K : ℝ) (x : SecondExpansionData ι)
    (hs : SecondSourceSupport p Z M x) (hE : x.divisor⊆x.sourceCommon)
    (hk : x.frequency≠0) (hK : elementNorm (sourceObservation p x).1≤K) :
    initialLogIndex p x∈secondLogBinBox (Z*Real.exp M) K := by
  obtain ⟨hG,hE',hV⟩ := secondSourceSupport_bounds p hp Z M x hs hE
  simp only [initialLogIndex,secondLogBinBox,Finset.mem_product,Finset.mem_range,Nat.lt_succ_iff]
  exact ⟨normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hE',
    normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hV,
    normLogBin_mono (SecondPassIntegration.elementNorm_pos _ (sourceRow_nonzero p x hk)) hK⟩

end

theorem initial_log_box_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ U V K : ℝ,1≤U → 0<V → 0<K → V≤U → K≤U →
      ((secondLogBinBox V K).card:ℝ)≤C*U^ε := by
  obtain ⟨C,hC,hpow⟩ := globalLogFactor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro U V K hU hV hK hVU hKU
  have hv := normLogBin_le_log_upper V U hV hVU hU
  have hk := normLogBin_le_log_upper K U hK hKU hU
  have hlog := Real.log_nonneg hU
  let B := 1+Real.log 27+22*Real.log U
  have h27 : 0≤Real.log 27 := Real.log_nonneg (by norm_num)
  have hB : 1≤B := by dsimp [B]; linarith
  have hvB : (normLogBin V:ℝ)+1≤B := by dsimp [B]; linarith
  have hkB : (normLogBin K:ℝ)+1≤B := by dsimp [B]; linarith
  have hh : ((secondLogBinBox V K).card:ℝ)≤B^3 := by
    rw [secondLogBinBox_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ B^2*B := mul_le_mul (pow_le_pow_left₀ (by positivity) hvB 2) hkB
        (by positivity) (sq_nonneg B)
      _ = B^3 := by ring
  exact hh.trans ((pow_le_pow_right₀ hB (by decide : 3≤10)).trans (hpow U hU))

end InitialMeanSquare

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (bit conductorExponent dilationExponent retained parity evenDouble
  primeProduct primeProductNorm aLabel dilationLabel jLabel j2Label squarefreeLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

theorem local_first_conductor_balance (parityBit e₁ e₂ : Bool) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      2*bit (!parityBit && e₁ && e₂)=bit e₁+bit e₂+bit parityBit := by
  cases parityBit <;> cases e₁ <;> cases e₂ <;> decide

theorem local_first_conductor_bound (parityBit e₁ e₂ : Bool) (n : ℕ) (hn : 0<n) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2*n := by
  have h : (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2 := by
    cases parityBit <;> cases e₁ <;> cases e₂ <;> decide
  omega

variable {ι : Type*} [DecidableEq ι] (p : ι → O)

omit [DecidableEq ι] in
theorem firstActiveProduct_as_primeProduct (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)=
      primeProduct p S (fun i => if conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 then 0 else 1) := by
  unfold cubeActiveSupport primeProduct
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 <;> simp [h]

omit [DecidableEq ι] in
theorem first_conductor_product_balance (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)*dilationLabel p S v ε₁ ε₂*j2Label p S v ε₁ ε₂^2 =
      aLabel p S ε₁*aLabel p S ε₂*squarefreeLabel p S v := by
  rw [firstActiveProduct_as_primeProduct]
  simp only [dilationLabel,j2Label,aLabel,squarefreeLabel,primeProduct,← Finset.prod_pow,
    ← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  simpa only [evenDouble,mul_comm] using local_first_conductor_balance (parity (v i)) (ε₁ i) (ε₂ i)

variable [∀ i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_conductor_product_dvd (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) :
    (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)*
      dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂*jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣
      aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2 := by
  rw [firstActiveProduct_as_primeProduct,← primeProduct_add]
  simp only [dilationLabel,jLabel,aLabel,primeProduct,← Finset.prod_pow,← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  simpa only [mul_comm] using local_first_conductor_bound (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i) (v₁ i+v₂ i) (hv i hi)

variable (hp : ∀ i,p i≠0)
include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_conductor_norm_bound (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) (B : ℝ) (hB : 0≤B)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤B) :
    ‖eisEmbedding (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2*
      ‖eisEmbedding (dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2*
      ‖eisEmbedding (jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤
    ‖eisEmbedding (aLabel p S ε₁)‖^2*‖eisEmbedding (aLabel p S ε₂)‖^2*B^4 := by
  have hn : aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2≠0 := by
    apply mul_ne_zero (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
    exact pow_ne_zero _ (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
  have h := element_norm_le_of_dvd hn (first_conductor_product_dvd p S v₁ v₂ ε₁ ε₂ hv)
  simp only [map_mul,map_pow,norm_mul,norm_pow,mul_pow] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hm := mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hs := pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hm 2
  convert hs using 1 <;> ring

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel jLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

lemma first_row_numeric_bound (an en jn a1 a2 cn dn hn fn ell K B F : ℝ)
    (ha : 0≤an) (he : 0≤en) (hj : 0<jn) (h1 : 0<a1) (h2 : 0<a2) (hc : 0<cn)
    (hd : 0≤dn) (_hh : 0≤hn) (hf : 0≤fn) (hell : 0<ell) (hK : 0<K) (_hB : 0<B) (hF : 0<F)
    (hcon : an*en*jn≤a1*a2*B^4) (hfreq : hn≤ell^2*an*dn/(K*a1*a2*cn^2)) (hlabel : fn≤F) :
    hn*fn^2*en≤ell^2*B^4*F^2*dn/(K*cn^2*jn) := by
  have hratio : an*en/(a1*a2)≤B^4/jn := by
    apply (div_le_div_iff₀ (mul_pos h1 h2) hj).mpr
    nlinarith [hcon]
  calc
    hn*fn^2*en ≤ (ell^2*an*dn/(K*a1*a2*cn^2))*F^2*en := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul hfreq (pow_le_pow_left₀ hf hlabel 2) (sq_nonneg _) (by positivity)
    _ = (ell^2*dn*F^2/(K*cn^2))*(an*en/(a1*a2)) := by
      field_simp

    _ ≤ (ell^2*dn*F^2/(K*cn^2))*(B^4/jn) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstRowScale_le_pooled (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (b : GlobalCubeBlock ι) :
    globalFirstRowScale p K ell B F ((b.withCommon ∅).append ⟨∅,∅,∅,1⟩) ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).2
  have hc := (hbds 1).1
  have hJ := (hbds 4).1
  change primeProductNorm p b.firstDivisor≤globalLogRep j 5*Real.exp 1 at hd
  change globalLogRep j 1≤primeProductNorm p b.common at hc
  change globalLogRep j 4≤globalCubeJNorm p x at hJ
  change ell^2*B^4*F^2*primeProductNorm p b.firstDivisor/
      (K*(primeProductNorm p b.common)^2*globalCubeJNorm p x) ≤
    Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
  have hdpos := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor).le
  have h5 := (globalLogRep_pos j 5).le
  apply div_le_div₀ (by positivity)
  · calc
      _ ≤ ell^2*B^4*F^2*(globalLogRep j 5*Real.exp 1) := by gcongr
      _ = _ := by ring
  · exact mul_pos (mul_pos hK (sq_pos_of_pos (globalLogRep_pos j 1))) (globalLogRep_pos j 4)
  · exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (globalLogRep_pos j 1).le hc 2) hK.le)
      hJ (globalLogRep_pos j 4).le (by positivity)

include hp in

theorem first_row_enlargement (b : GlobalCubeBlock ι) (x : Ideal O × O)
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : (Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ‖eisEmbedding x.2‖^2 ≤
      ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
      primeProductNorm p b.firstDivisor/
      (K*‖eisEmbedding (aLabel p b.cube.support b.cube.leftBit)‖^2*
        ‖eisEmbedding (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x)‖^2 ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let active := cubeActiveSupport b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let e := dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let j := jLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let a1 := aLabel p b.cube.support b.cube.leftBit
  let a2 := aLabel p b.cube.support b.cube.rightBit
  have hpos (v : ι → ℕ) : 0<‖eisEmbedding (primeProduct p b.cube.support v)‖^2 :=
    zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _))
  have hcon := first_conductor_norm_bound p hp b.cube.support b.cube.leftExponent b.cube.rightExponent
    b.cube.leftBit b.cube.rightBit b.cube.support_pos B hB.le hb₁ hb₂
  have hnum := first_row_numeric_bound (primeProductNorm p active) (‖eisEmbedding e‖^2) (‖eisEmbedding j‖^2)
    (‖eisEmbedding a1‖^2) (‖eisEmbedding a2‖^2) (primeProductNorm p b.common) (primeProductNorm p b.firstDivisor)
    (‖eisEmbedding x.2‖^2) (Ideal.absNorm x.1) ell K B F
    (FirstPassCubeLabels.primeProductNorm_pos p hp active).le (sq_nonneg _) (hpos _) (hpos _) (hpos _)
    (FirstPassCubeLabels.primeProductNorm_pos p hp b.common) (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor).le
    (sq_nonneg _) (Nat.cast_nonneg _) hell hK hB hF hcon hh hf
  have hgen : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator x.1)‖^2=(Ideal.absNorm x.1 : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hrow : ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap e x)‖^2 =
      ‖eisEmbedding x.2‖^2*(Ideal.absNorm x.1 : ℝ)^2*‖eisEmbedding e‖^2 := by
    simp only [DescentWeightedCauchy.firstElementRowMap,map_mul,map_pow,norm_mul,norm_pow,mul_pow]
    rw [show (‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator x.1)‖^2)^2 =
        (Ideal.absNorm x.1 : ℝ)^2 by rw [hgen]]
  rw [hrow]
  exact hnum.trans (globalFirstRowScale_le_pooled p hp K ell B F hK hell hB hF b)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstFrequencyScale (K ell : ℝ) (b : GlobalCubeBlock ι) : ℝ :=
  ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
    primeProductNorm p b.firstDivisor/
    (K*‖eisEmbedding (aLabel p b.cube.support b.cube.leftBit)‖^2*
      ‖eisEmbedding (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)

def globalCubeFirstTargets (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O)) : Finset O :=
  s.image (DescentWeightedCauchy.firstElementRowMap
    (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
      b.cube.leftBit b.cube.rightBit))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeFirstTargets_mem (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (x : Ideal O × O) (hx : x∈s) :
    DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x∈globalCubeFirstTargets p b s :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeFirstTargets_ne_zero (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (hsf : ∀ x∈s,Squarefree x.1) (hs0 : ∀ x∈s,x.2≠0)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) : z≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  apply mul_ne_zero
  · apply mul_ne_zero (hs0 x hx)
    exact pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero _ (by simpa using (hsf x hx).ne_zero))
  · exact primeProduct_ne_zero p hp _ _

include hp in
theorem globalCubeFirstTargets_norm_bound (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : ∀ x∈s,(Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ∀ x∈s,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) :
    (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  rw [← eisEmbedding_norm_sq_eq_absNorm_span]
  exact first_row_enlargement p hp b x K ell B F hK hell hB hF hb₁ hb₂ (hf x hx) (hh x hx)

end SecondPassArithmetic

end

end OAI
