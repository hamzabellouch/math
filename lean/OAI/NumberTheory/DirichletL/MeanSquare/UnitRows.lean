import OAI.NumberTheory.DirichletL.MeanSquare.UniformPolynomialHeight

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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedUnitRows
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open CompletedGauss hiding O
open CanonicalQuadraticSieve hiding O
open CanonicalRowCompletion
local instance : Fintype ActualEisensteinCubic.Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def unitRowFamily (Ψ : ActualEisensteinCubic.O→*ℂ) (mask : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ) {F : ℝ}
    (f : idealRange F) (I : Ideal ActualEisensteinCubic.O) : ActualEisensteinCubic.O→*ℂ :=
  rowTwist Ψ mask (idealGenerator f.val) (u.val*idealGenerator I)

lemma unitRowFamily_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀x,‖Ψ x‖≤1)
    (mask : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ) {F : ℝ} (f : idealRange F) (I : Ideal ActualEisensteinCubic.O) (x : ActualEisensteinCubic.O) :
    ‖unitRowFamily Ψ mask u f I x‖≤1 := rowTwist_norm Ψ hΨ _ _ _ _

lemma rowTwist_normHeight (Ψ : ActualEisensteinCubic.O→*ℂ) (mask f z : ActualEisensteinCubic.O) (θ : ℝ) :
    rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ) mask f z =
      SecondPassArithmetic.normHeightTwist (rowTwist Ψ mask f z) θ := by
  unfold rowTwist
  exact (SecondPassArithmetic.normHeightTwist_mul Ψ _ θ).symm

theorem short_completed_elements_uniform_twist
    (a b : ℝ) (ha : 0<a)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀T : Finset ActualEisensteinCubic.O,(∀z∈T,z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤K) →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),(∀x,‖Ψ x‖≤1) → ∀(mask : ActualEisensteinCubic.O) (lengthScale : ℂ),
      (∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays (T.image (fun z=>Ideal.span {z})) K
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ) (unitRowFamily Ψ mask u f) lengthScale) →
      (∑f : idealRange F,∑z∈T,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) z) W X (Z^(1/1000:ℝ))‖^2)/F≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨n,hn⟩ := CompletedHeight.short_completed_average_uniform_twist
    a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨n,?_⟩
  intro W hsupp hW
  obtain ⟨C,hC,hbound⟩ := hn W hsupp hW
  refine ⟨6*C,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin T hT Ψ hΨ mask lengthScale hmodels
  let rows := T.image (fun z=>Ideal.span {z})
  let R : ℝ := (C*(1+‖θ‖)^n)*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε
  have hrows := image_span_nonzero_norm T K hT
  have hu (u : ActualEisensteinCubic.Oˣ) :
      (∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2)/F≤R := by
    simp_rw [rowTwist_normHeight]
    exact hbound θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows
      (unitRowFamily Ψ mask u) (unitRowFamily_norm Ψ hΨ mask u) lengthScale (hmodels u)
  have hsum :
      (∑f : idealRange F,∑z∈T,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) z) W X (Z^(1/1000:ℝ))‖^2)≤
      ∑u : ActualEisensteinCubic.Oˣ,∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2 := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro f _
    exact sum_nonzero_element_le_units T (fun z hz=>(hT z hz).1) _ (fun z=>sq_nonneg _)
  calc
    _ ≤ (∑u : ActualEisensteinCubic.Oˣ,∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2)/F :=
      div_le_div_of_nonneg_right hsum (by linarith)
    _ = ∑u : ActualEisensteinCubic.Oˣ,(∑f : idealRange F,∑I∈rows,
        ‖shortCompletedSum (rowTwist (SecondPassArithmetic.normHeightTwist Ψ θ)
          mask (idealGenerator f.val) (u.val*idealGenerator I)) W X (Z^(1/1000:ℝ))‖^2)/F :=
      Finset.sum_div _ _ _
    _ ≤ ∑u : ActualEisensteinCubic.Oˣ,R := Finset.sum_le_sum (fun u _=>hu u)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,unit_card,nsmul_eq_mul]; dsimp [R]; ring

end CompletedUnitRows

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open CanonicalCoefficientClass (IsBaseRayTwist)
open RayFourExpansion (RayCharacter)

structure CanonicalStateCondition (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ) : Prop where
  coefficient : IsBaseRayTwist base Ψ
  mask_ne_zero : m≠0
  column_pos : 0<X
  label_ge_one : 1≤F
  row_ge_one : 1≤K
  row_le_global : K≤Z^3
  mass_le : X*F≤canonicalRankMass Z (fixedDepthRank Z K)
  invariant : K*‖eisEmbedding m‖^2≤
    (X*F)*Z^(-canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z K))
  label_bounds : ∀I∈labels,I≠⊥ ∧ Squarefree I ∧ IsCoprime I bad ∧ (Ideal.absNorm I:ℝ)≤F

theorem CanonicalStateCondition.invariant_reserved
    {base : ActualEisensteinCubic.O→*ℂ} {bad : Ideal ActualEisensteinCubic.O} {Z η : ℝ} {Ψ : ActualEisensteinCubic.O→*ℂ} {m : ActualEisensteinCubic.O}
    {labels : Finset (Ideal ActualEisensteinCubic.O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hη : 0≤η) (hbudget : 3000*η≤(1:ℝ)/40) :
    K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((1:ℝ)/40)) :=
  canonicalRankMargin_final_bound Z η _ _ _ hZ hη
    (mul_nonneg h.column_pos.le (zero_le_one.trans h.label_ge_one)) hbudget h.invariant

theorem CanonicalStateCondition.small_or_live
    {base : ActualEisensteinCubic.O→*ℂ} {bad : Ideal ActualEisensteinCubic.O} {Z η : ℝ} {Ψ : ActualEisensteinCubic.O→*ℂ} {m : ActualEisensteinCubic.O}
    {labels : Finset (Ideal ActualEisensteinCubic.O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : Real.exp 9000≤Z) (hZ1 : 1≤Z) (hη : 0≤η)
    (hbudget : 3000*η≤(1:ℝ)/40) :
    K≤F ∨ (1<X ∧ X≤Z^3 ∧ F≤Z^3) := by
  have hi := h.invariant_reserved hZ1 hη hbudget
  have hr : Z^(-((1:ℝ)/40))≤1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num : -((1:ℝ)/40)≤0))
  have hi' : K*‖eisEmbedding m‖^2≤X*F :=
    hi.trans ((mul_le_mul_of_nonneg_left hr
      (mul_nonneg h.column_pos.le (zero_le_one.trans h.label_ge_one))).trans_eq (mul_one _))
  exact canonical_small_or_live Z X F K _ m hZ h.column_pos h.label_ge_one
    (zero_le_one.trans h.row_ge_one) h.mask_ne_zero h.mass_le hi'

variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem canonicalStateCondition_retained
    (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hpbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (a : RayCharacter) (r : FirstCoreIndex) (ray : SecondRayIndex) (B : ℝ)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hB : 0<B) (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale K (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    let labels':=globalCanonicalLabels p source side q j
    let m':=fixedTripleMask m q
    fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧
    CanonicalStateCondition base bad Z η (secondRayMinus (firstCoreTwist side a Ψ r) ray)
      m' labels' X' F' K' ∧
    CanonicalStateCondition base bad Z η (secondRayPlus (firstCoreTwist side a Ψ r) ray)
      m' labels' X' F' K' := by
  obtain ⟨hXc,hFc,hKc,hrank,hKglobal,hmass,hinvariant,hm,hlabels⟩ :=
    canonical_retained_unpadded_closure p hp source side q j hq Z ((1:ℝ)/20) η X B F K m
      hZ hZbig hη hηsmall hstate.column_pos hB hstate.label_ge_one hstate.row_ge_one
      hstate.mask_ne_zero hprogress hstate.row_le_global hstate.mass_le hstate.invariant
      hk hb₁ hb₂ hretained
  have hbad := globalCanonicalLabels_coprime p bad hpbad source side q j
  have hbnd : ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ IsCoprime I bad ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
    intro I hI
    exact ⟨(hlabels I hI).1,(hlabels I hI).2.1,hbad I hI,(hlabels I hI).2.2⟩
  refine ⟨hrank,?_,?_⟩
  · exact ⟨(hstate.coefficient.firstCore side a r).secondMinus ray,
      hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant,hbnd⟩
  · exact ⟨(hstate.coefficient.firstCore side a r).secondPlus ray,
      hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant,hbnd⟩

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open CanonicalCoefficientClass (IsBaseRayTwist)
open RayFourExpansion (RayCharacter)
variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem canonicalStateCondition_cutoff_retained
    (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
    (hpbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (a : RayCharacter) (r : FirstCoreIndex) (ray : SecondRayIndex) (B : ℝ)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hB : 0<B) (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    let labels':=globalCanonicalLabels p source side q j
    let m':=fixedTripleMask m q
    fixedDepthRank Z K'+1≤fixedDepthRank Z Ksrc ∧
    CanonicalStateCondition base bad Z η (secondRayMinus (firstCoreTwist side a Ψ r) ray)
      m' labels' X' F' K' ∧
    CanonicalStateCondition base bad Z η (secondRayPlus (firstCoreTwist side a Ψ r) ray)
      m' labels' X' F' K' := by
  obtain ⟨hXc,hFc,hKc,hrank,hKglobal,hmass,hinvariant,hm,hlabels⟩ :=
    canonical_retained_scale_closure p hp source side q j hq Z
      (canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z Ksrc)) η X B F Ksrc m
      hZ hZbig hη hηsmall hstate.column_pos hB hstate.label_ge_one hstate.row_ge_one
      hstate.mask_ne_zero hprogress hstate.row_le_global hstate.mass_le hstate.invariant
      hk hb₁ hb₂ hretained
  have hinvariant' : (globalLogRep j 8*Real.exp 1)*‖eisEmbedding (fixedTripleMask m q)‖^2≤
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)*
        Z^(-canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z (globalLogRep j 8*Real.exp 1))) := by
    apply hinvariant.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hXc.le (zero_le_one.trans hFc))
    have hmargin := canonicalRankMargin_step ((1:ℝ)/20) η hη _ _
      (fixedDepthRank_initial Z Ksrc hZ (zero_lt_one.trans_le hstate.row_ge_one) hstate.row_le_global) hrank
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hbad := globalCanonicalLabels_coprime p bad hpbad source side q j
  have hbnd : ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ IsCoprime I bad ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
    intro I hI
    exact ⟨(hlabels I hI).1,(hlabels I hI).2.1,hbad I hI,(hlabels I hI).2.2⟩
  refine ⟨hrank,?_,?_⟩
  · exact ⟨(hstate.coefficient.firstCore side a r).secondMinus ray,
      hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant',hbnd⟩
  · exact ⟨(hstate.coefficient.firstCore side a r).secondPlus ray,
      hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant',hbnd⟩

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

theorem nonzeroRowFamily_le_center (labels : Finset (Ideal ActualEisensteinCubic.O))
    (P : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→ℂ) (K scale B : ℝ) (zero tail : ℂ)
    (hK : 0<K) (hscale : 0<scale)
    (hcenter : ‖(scale:ℂ)⁻¹*((∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*
      (‖P I z‖^2:ℝ))-zero-tail)‖≤B) :
    (∑I∈labels,nonzeroRowMajorantSum (P I) K).re≤
      ‖zero‖+‖tail‖+scale*B := by
  let total : ℂ := ∑I∈labels,∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*(‖P I z‖^2:ℝ)
  have hnonzero : (∑I∈labels,nonzeroRowMajorantSum (P I) K).re≤total.re := by
    simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re,
      Complex.re_sum,Complex.ofReal_re]
    change (∑I∈labels,(∑'z:ActualEisensteinCubic.O,rowMajorant (‖eisEmbedding z‖^2/K)*(‖P I z‖^2:ℝ)).re)-
      ∑I∈labels,‖P I 0‖^2≤_
    have hz : 0≤∑I∈labels,‖P I 0‖^2 := Finset.sum_nonneg (fun I hI=>sq_nonneg _)
    dsimp only [total]
    rw [Complex.re_sum]
    linarith
  have hc : ‖total-zero-tail‖≤scale*B := by
    calc
      _ = scale*‖(scale:ℂ)⁻¹*(total-zero-tail)‖ := by
        rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hscale]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hcenter hscale.le
  apply hnonzero.trans
  calc
    total.re ≤ ‖total‖ := Complex.re_le_norm _
    _ = ‖(total-zero-tail)+zero+tail‖ := by congr 1; ring
    _ ≤ ‖total-zero-tail‖+‖zero‖+‖tail‖ := norm_add₃_le
    _ ≤ _ := by linarith

theorem reopenedCanonicalRow_nonzero_twoPassage
    (g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal ActualEisensteinCubic.O))
      (β:Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (Γ t Ksrc Kcut ell B F H U:ℝ),
      0≤Γ → 0<Ksrc → 0<Kcut → 0<ell → 1≤B → 0<F → 0≤H → 1≤U →
      ell*Real.exp M≤U → (∀u,‖Ψ u‖≤1) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      (∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
           (ConcretePrimeRowBridge.idealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p ell S))) Ksrc).re≤
      ‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc ell‖+
      ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc Kcut ell‖+
      (ell*B^2*F)*(Ksrc/Kcut)*Cfirst*(globalFirstRowCap Kcut ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₁ C₁ Cd₁ Ct₁ (Γ^2) ε Kcut ell B F M H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₂ C₂ Cd₂ Ct₂ (Γ^2) ε Kcut ell B F M H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩ :=
    reopenedCanonicalRow_twoPassage_uniform_height rowMajorant g V M Nv hM hNv hgM hV hWin
      ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc Kcut ell B F H U
    hΓ hKsrc hKcut hell hB hF hH hU hMU hΨ hβ hQ hQB hsf hf
  dsimp only
  have ht := htransfer p hp hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc Kcut ell B F H U
    hΓ hKsrc hKcut hell hB hF hH hU hMU hΨ hβ hQ hQB hsf hf
  have hscale : 0<ell*B^2*F := mul_pos (mul_pos hell (sq_pos_of_pos (zero_lt_one.trans_le hB))) hF
  have hb := nonzeroRowFamily_le_center labels
    (fun I=>reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
      (ConcretePrimeRowBridge.idealGenerator I)
      (fun S=>frequencyTwist g t (columnLog p ell S))) Ksrc (ell*B^2*F)
    ((Ksrc/Kcut)*Cfirst*(globalFirstRowCap Kcut ell B F)^deltaLoss*
      Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool (reopenedCubeFamily Q))
        (normHeightTwist Ψ t) m windows₁ C₁ Cd₁ Ct₁ (Γ^2) ε Kcut ell B F M H U A J N true)*
      Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool (reopenedCubeFamily Q))
        (normHeightTwist Ψ t) m windows₂ C₂ Cd₂ Ct₂ (Γ^2) ε Kcut ell B F M H U A J N false))
    (canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc ell)
    (canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc Kcut ell)
    hKsrc hscale (by simpa only [Complex.ofReal_mul,Complex.ofReal_pow] using ht)
  exact hb.trans_eq (by ring)

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

namespace CubicEisenstein

def euclideanAxisPath (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) : EuclideanSpatial :=
  WithLp.toLp 2 (Function.update p.ofLp j t)

lemma euclideanAxisPath_affine (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) :
    euclideanAxisPath p j t=p+(t-p j)•euclideanCoordinateVector j := by
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext k
  by_cases hk : k=j
  · subst k
    simp [euclideanAxisPath,euclideanCoordinateVector]
  · simp [euclideanAxisPath,euclideanCoordinateVector,Function.update,hk]

lemma euclideanAxisPath_self (p : EuclideanSpatial) (j : Fin 3) :
    euclideanAxisPath p j (p j)=p := by
  rw [euclideanAxisPath_affine,sub_self,zero_smul,add_zero]

lemma euclideanAxisPath_hasDerivAt (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) :
    HasDerivAt (euclideanAxisPath p j) (euclideanCoordinateVector j) t := by
  have he : euclideanAxisPath p j=(fun t => p+(t-p j)•euclideanCoordinateVector j) :=
    funext (euclideanAxisPath_affine p j)
  rw [he]
  simpa only [sub_zero,one_smul,zero_add,Pi.add_apply,id_eq] using!
    (hasDerivAt_const t p).add (((hasDerivAt_id t).sub_const (p j)).smul_const (euclideanCoordinateVector j))

lemma euclideanAxisSlice_deriv (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (j : Fin 3) (t : ℝ) (hf : DifferentiableAt ℝ f (euclideanAxisPath p j t)) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) t=
      fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j) :=
  (hf.hasFDerivAt.comp_hasDerivAt t (euclideanAxisPath_hasDerivAt p j t)).deriv

lemma euclideanAxisSlice_derivatives (f : EuclideanSpatial→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : EuclideanSpatial) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) (p j)=
      fderiv ℝ f p (euclideanCoordinateVector j) ∧
    deriv (deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)) (p j)=
      fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p (euclideanCoordinateVector j) := by
  constructor
  · simpa only [euclideanAxisPath_self] using euclideanAxisSlice_deriv f p j (p j)
      (by simpa only [euclideanAxisPath_self] using (hf p hp).differentiableAt (by simp))
  · have hc : ContinuousAt (fun t => euclideanAxisPath p j t 2) (p j) :=
      (by fun_prop : Continuous (fun q : EuclideanSpatial => q 2)).continuousAt.comp
        (euclideanAxisPath_hasDerivAt p j (p j)).continuousAt
    have hpos : 0<euclideanAxisPath p j (p j) 2 := by rw [euclideanAxisPath_self]; exact hp
    have he : deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)=ᶠ[𝓝 (p j)]
        (fun t => fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j)) := by
      filter_upwards [hc.eventually_const_lt hpos] with t ht
      exact euclideanAxisSlice_deriv f p j t ((hf _ ht).differentiableAt (by simp))
    rw [he.deriv_eq]
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p :=
      (((hf p hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
    have hd' : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j))
        (euclideanAxisPath p j (p j)) := by rwa [euclideanAxisPath_self]
    have hh := hd'.hasFDerivAt.comp_hasDerivAt (p j) (euclideanAxisPath_hasDerivAt p j (p j))
    simpa only [euclideanAxisPath_self,Function.comp_def] using! hh.deriv

def positiveEuclideanLaplacian (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p
    (euclideanCoordinateVector j))+(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector 2)

lemma positiveEuclideanLaplacian_eq_axis (f : EuclideanSpatial→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian f p=-axisLaplacian (fun q => f (WithLp.toLp 2 q)) p.ofLp := by
  unfold positiveEuclideanLaplacian axisLaplacian
  simp only [(euclideanAxisSlice_derivatives f hf p hp _).1,(euclideanAxisSlice_derivatives f hf p hp _).2]
  ring

lemma positiveEuclideanLaplacian_congr (f g : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (he : f=ᶠ[𝓝 p]g) : positiveEuclideanLaplacian f p=positiveEuclideanLaplacian g p := by
  have hd (j : Fin 3) : (fun q => fderiv ℝ f q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  simp only [positiveEuclideanLaplacian,he.fderiv_eq,(hd _).fderiv_eq]

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv Manifold

namespace CubicEisenstein

lemma kernelTestPartitionTerm_tsupport_right {ι : Type*} {S : Set KernelQuotient}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ,SpatialCoordinates) KernelQuotient S)
    (f : kernelSmoothTests) (i : ι) :
    tsupport (kernelTestPartitionTerm ρ f i).1⊆tsupport f.1 :=
  tsupport_smul_subset_right _ _

lemma kernelSmoothTest_finite_chart_partition_subsupport (f : kernelSmoothTests) :
    ∃t : Finset KernelGoodCutoff,∃g : t→kernelSmoothTests,
      (∑i,g i)=f ∧ ∀i,tsupport (g i).1⊆kernelChartCoreImage i.1.1 ∧
        tsupport (g i).1⊆tsupport f.1 := by
  obtain ⟨t,ht⟩ := kernelCompact_finite_chart_cover (tsupport f.1) f.2.2
  have hc : tsupport f.1⊆⋃χ : t,kernelChartCoreImage χ.1.1 := by
    intro q hq
    obtain ⟨χ,hχ,hqχ⟩ := Set.mem_iUnion₂.mp (ht hq)
    exact Set.mem_iUnion.mpr ⟨⟨χ,hχ⟩,hqχ⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,SpatialCoordinates)
    (isClosed_tsupport f.1) (fun χ : t => kernelChartCoreImage χ.1.1)
    (fun χ => kernelChartCoreImage_open χ.1.1) hc
  refine ⟨t,kernelTestPartitionTerm ρ f,kernelTestPartition_sum f ρ,fun i => ?_⟩
  exact ⟨(kernelTestPartitionTerm_tsupport ρ f i).trans (hρ i),
    kernelTestPartitionTerm_tsupport_right ρ f i⟩

lemma kernelDirichletForm_supported_equation_chart (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (f g : kernelSmoothTests) (hg : tsupport g.1⊆kernelChartCoreImage χ)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelEuclideanProjection p∈tsupport g.1→
      kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p)) :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hi : Integrable (fun q => star (A q)*g.1 q) (integralQuotientVolume globalKubotaKernel) :=
    hA.star.integrable_mul (kernelSmoothTests_memLp g)
  have himg : kernelChartCoreImage χ⊆kernelEuclideanProjection '' S :=
    Set.image_mono (kernelChartCore_subset χ)
  rw [kernelDirichletForm_eq_chart_laplacian χ hinj f g hg]
  calc
    _ = ∫p in S,star (upperPositiveLaplacian (kernelCoreLift χ f) p)*kernelCoreLift χ g p/(p 2:ℂ)^3 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
        (fun h => hp (kernelCoreLift_tsupport_outer χ g h))
      rw [hz,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)/(p 2:ℂ)^3 := by
      apply setIntegral_congr_fun hS
      intro p hp
      dsimp only
      rw [kernelCoreLift_eq_on_outer χ hinj g hg hp]
      by_cases hc : p∈kernelChartCore χ
      · by_cases hgp : kernelEuclideanProjection p∈tsupport g.1
        · rw [kernelCoreLift_laplacian χ f p hc,heq p (χ.positive hp) hgp]
          rfl
        · have hz : g.1 (kernelEuclideanProjection p)=0 := image_eq_zero_of_notMem_tsupport hgp
          change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
          rw [hz,mul_zero,zero_div,mul_zero,zero_div]
      · have hz : kernelCoreLift χ g p=0 := image_eq_zero_of_notMem_tsupport
          (fun h => hc (kernelCoreLift_tsupport χ hinj g hg h))
        rw [kernelCoreLift_eq_on_outer χ hinj g hg hp] at hz
        change g.1 (kernelEuclideanProjection p)=0 at hz
        change star _*g.1 (kernelEuclideanProjection p)/_=star _*g.1 (kernelEuclideanProjection p)/_
        rw [hz,mul_zero,zero_div,mul_zero,zero_div]
    _ = ∫p in S,star (A (kernelEuclideanProjection p))*g.1 (kernelEuclideanProjection p)
        ∂hyperbolicEuclideanVolume :=
      (hyperbolicEuclidean_setIntegral_complex S hS χ.positive _).symm
    _ = ∫q in kernelEuclideanProjection '' S,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_integral_complex S hS χ.positive hinj _ hi.aestronglyMeasurable
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      have hz : g.1 q=0 := image_eq_zero_of_notMem_tsupport (fun h => hq (himg (hg h)))
      rw [hz,mul_zero]

theorem kernelDirichletForm_supported_equation (f g : kernelSmoothTests)
    (A : KernelQuotient→ℂ) (hA : MemLp A 2 (integralQuotientVolume globalKubotaKernel))
    (heq : ∀p,0<p 2→kernelEuclideanProjection p∈tsupport g.1→
      kernelCoordinateLaplacian f p=A (kernelEuclideanProjection p))
    :
    kernelDirichletForm f g=∫q,star (A q)*g.1 q∂integralQuotientVolume globalKubotaKernel := by
  obtain ⟨t,G,hG,hGsupp⟩ := kernelSmoothTest_finite_chart_partition_subsupport g
  calc
    _ = ∑i : t,kernelDirichletForm f (G i) := by
      rw [←hG,kernelDirichletForm_sum_right]
    _ = ∑i : t,∫q,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      apply Finset.sum_congr rfl
      intro i hi
      exact kernelDirichletForm_supported_equation_chart i.1.1 i.1.2 f (G i) (hGsupp i).1 A hA (fun p hp hgp => heq p hp ((hGsupp i).2 hgp))
    _ = ∫q,∑i : t,star (A q)*(G i).1 q∂integralQuotientVolume globalKubotaKernel := by
      symm
      exact integral_finsetSum _ (fun i hi => hA.star.integrable_mul (kernelSmoothTests_memLp (G i)))
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun q => by
        have hq := congrArg (fun k : kernelSmoothTests => k.1 q) hG
        simp only [Submodule.coe_sum,Finset.sum_apply] at hq
        dsimp only
        rw [←Finset.mul_sum,hq])

end CubicEisenstein

end

end OAI
