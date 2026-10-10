import OAI.NumberTheory.DirichletL.QuadraticSieve.CommonMasks
import OAI.NumberTheory.DirichletL.Eisenstein.QuotientTopology

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

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct bit parity retained b0Exponent aLabel jLabel j2Label squarefreeLabel b0Label)

variable {ι : Type*} [DecidableEq ι]

def finiteBlockExponent (B : Finset ι) (v : ι → ℕ) : ι →₀ ℕ :=
  Finsupp.onFinset B (fun i => if i∈B then v i else 0) (by
    intro i hi
    by_contra hn
    exact hi (ite_eq_right hn))

def cubeCoordinatesOfBlock (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : CubeCoordinates ι where
  leftExponent := finiteBlockExponent B v₁
  rightExponent := finiteBlockExponent B v₂
  leftDivisor := B.filter (fun i => ε₁ i)
  rightDivisor := B.filter (fun i => ε₂ i)

theorem cubeCoordinatesOfBlock_support (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈B,0 < v₁ i+v₂ i) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).support=B := by
  ext i
  simp only [CubeCoordinates.support,cubeCoordinatesOfBlock,Finset.mem_union,
    Finsupp.mem_support_iff,finiteBlockExponent,Finsupp.onFinset_apply]
  by_cases hi : i∈B
  · simp only [hi,ite_true,iff_true]
    have h := hv i hi
    omega
  · simp [hi]

theorem cubeCoordinatesOfBlock_leftBit (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (i : ι) (hi : i∈B) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).leftBit i=ε₁ i := by
  cases h : ε₁ i <;> simp [CubeCoordinates.leftBit,cubeCoordinatesOfBlock,hi,h]

theorem cubeCoordinatesOfBlock_rightBit (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (i : ι) (hi : i∈B) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).rightBit i=ε₂ i := by
  cases h : ε₂ i <;> simp [CubeCoordinates.rightBit,cubeCoordinatesOfBlock,hi,h]

theorem cubeCoordinatesOfBlock_admissible (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈B,0 < v₁ i+v₂ i) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).Admissible := by
  unfold CubeCoordinates.Admissible
  rw [cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv]
  exact ⟨Finset.filter_subset _ _,Finset.filter_subset _ _⟩

theorem cubeCoordinatesOfBlock_primeProduct (p : ι → O)
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i)
    (f : ℕ → ℕ → Bool → Bool → ℕ) :
    let x := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
    primeProduct p x.support (fun i => f (x.leftExponent i) (x.rightExponent i) (x.leftBit i) (x.rightBit i)) =
      primeProduct p B (fun i => f (v₁ i) (v₂ i) (ε₁ i) (ε₂ i)) := by
  dsimp only
  rw [cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv]
  unfold primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [cubeCoordinatesOfBlock_leftBit B v₁ v₂ ε₁ ε₂ i hi,
    cubeCoordinatesOfBlock_rightBit B v₁ v₂ ε₁ ε₂ i hi]
  simp only [cubeCoordinatesOfBlock,finiteBlockExponent,Finsupp.onFinset_apply,ite_eq_left hi]

def globalSecondOfBlock (B A₀ C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) : GlobalSecondData ι where
  cube := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
  firstCommon := A₀
  common := C
  firstDivisor := D
  source := x

theorem globalSecondOfBlock_injective (B A₀ C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Function.Injective (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂) := by
  intro x y h
  exact congrArg GlobalSecondData.source h

theorem globalSecondOfBlock_admissible (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i)
    (hCB : Disjoint C B) (hD : D⊆C∪B) (x : SecondExpansionData ι) (hE : x.divisor⊆x.sourceCommon) :
    GlobalSecondAdmissible (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) := by
  refine ⟨cubeCoordinatesOfBlock_admissible B v₁ v₂ ε₁ ε₂ hv,hE,?_,?_⟩
  · simpa only [globalSecondOfBlock,cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv] using hCB
  · simpa only [globalSecondOfBlock,cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv] using hD

variable (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondOfBlock_tuple (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i) (x : SecondExpansionData ι) :
    globalSecondTuple p (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) =
      actualSecondTuple p B C D x.divisor x.overlap v₁ v₂ ε₁ ε₂ x.frequency := by
  have hpoly := cubeCoordinatesOfBlock_primeProduct p B v₁ v₂ ε₁ ε₂ hv
  have hspan (f : ℕ → ℕ → Bool → Bool → ℕ) := congrArg (fun a : O => (Ideal.span {a} : Ideal O)) (hpoly f)
  let c := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
  have hJ : jLabel p c.support (fun i => c.leftExponent i+c.rightExponent i) c.leftBit c.rightBit =
      jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ := hpoly (fun a b e₁ e₂ => bit (retained (parity (a+b)) e₁ e₂))
  have hS : squarefreeLabel p c.support (fun i => c.leftExponent i+c.rightExponent i) =
      squarefreeLabel p B (fun i => v₁ i+v₂ i) := hpoly (fun a b _ _ => bit (parity (a+b)))
  have hP₁ : primeProduct p c.support c.leftExponent = primeProduct p B v₁ := hpoly (fun a _ _ _ => a)
  have hP₂ : primeProduct p c.support c.rightExponent = primeProduct p B v₂ := hpoly (fun _ b _ _ => b)
  have hA₁ : aLabel p c.support c.leftBit = aLabel p B ε₁ := hpoly (fun _ _ e₁ _ => bit e₁)
  have hA₂ : aLabel p c.support c.rightBit = aLabel p B ε₂ := hpoly (fun _ _ _ e₂ => bit e₂)
  have hJ₂ : j2Label p c.support (fun i => c.leftExponent i+c.rightExponent i) c.leftBit c.rightBit =
      j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ := hpoly (fun a b e₁ e₂ => bit (FirstPassCubeLabels.evenDouble (a+b) e₁ e₂))
  change actualSecondTuple p c.support C D x.divisor x.overlap c.leftExponent c.rightExponent c.leftBit c.rightBit x.frequency = _
  unfold actualSecondTuple
  rw [hJ,hS,hP₁,hA₁,hA₂,hJ₂,hP₂]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondOfBlock_triple (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i) (x : SecondExpansionData ι) :
    globalSecondFixedTriple p (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) =
    (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂},
      ∏ i∈A₀,Ideal.span {p i},∏ i∈x.sourceCommon\x.divisor,Ideal.span {p i}) := by
  have h := cubeCoordinatesOfBlock_primeProduct p B v₁ v₂ ε₁ ε₂ hv
    (fun a b e₁ e₂ => b0Exponent (a+b) e₁ e₂)
  apply Prod.ext
  · exact congrArg (fun a : O => (Ideal.span {a} : Ideal O)) h
  · rfl

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondOfBlock_label (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i) (x : SecondExpansionData ι) :
    globalSecondLabel p (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) =
      secondSupportLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x) := by
  have h := cubeCoordinatesOfBlock_primeProduct p B v₁ v₂ ε₁ ε₂ hv
    (fun a b e₁ e₂ => bit (retained (parity (a+b)) e₁ e₂))
  unfold globalSecondLabel globalSecondOfBlock secondSupportLabel
  dsimp only [expansionSupportData]
  rw [show jLabel p (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).support
      (fun i => (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).leftExponent i+
        (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).rightExponent i)
      (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).leftBit (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).rightBit =
      jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ from h]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

abbrev GlobalLogIndex := Fin 10 → ℕ

def globalLogRep (j : GlobalLogIndex) (i : Fin 10) : ℝ := normLogScale (j i)

theorem globalLogRep_pos (j : GlobalLogIndex) (i : Fin 10) : 0 < globalLogRep j i := normLogScale_pos _

theorem globalLogRep_ge_one (j : GlobalLogIndex) (i : Fin 10) : 1 ≤ globalLogRep j i := normLogScale_ge_one _

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalScaleVector (side : Bool) (x : GlobalSecondData ι) : Fin 10 → ℝ :=
  ![primeProductNorm p (x.cube.sideDivisor side),primeProductNorm p x.common,
    primeProductNorm p x.firstCommon,primeProductNorm p (x.source.sourceCommon\x.source.divisor),
    globalCubeJNorm p x,primeProductNorm p x.firstDivisor,primeProductNorm p x.source.divisor,
    primeProductNorm p x.source.overlap,‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2,
    (globalCubeActiveRoot p x)^2]

def globalScaleIndex (side : Bool) (x : GlobalSecondData ι) : GlobalLogIndex :=
  fun i => normLogBin (globalScaleVector p side x i)

include hp in
theorem globalScaleVector_ge_one (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    ∀ i,1 ≤ globalScaleVector p side x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  · exact primeProductNorm_ge_one p hp x.common
  · exact primeProductNorm_ge_one p hp x.firstCommon
  · exact primeProductNorm_ge_one p hp (x.source.sourceCommon\x.source.divisor)
  · change 1 ≤ globalCubeJNorm p x
    exact element_norm_ge_one _ (primeProduct_ne_zero p hp x.cube.support _)
  · exact primeProductNorm_ge_one p hp x.firstDivisor
  · exact primeProductNorm_ge_one p hp x.source.divisor
  · exact primeProductNorm_ge_one p hp x.source.overlap
  · change 1 ≤ ‖eisEmbedding (actualSecondRow p x.firstDivisor x.source.divisor x.source.frequency)‖^2
    exact element_norm_ge_one _ (actualSecondRow_ne_zero p _ _ _ hk)
  · change 1 ≤ (globalCubeActiveRoot p x)^2
    exact element_norm_ge_one _ (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

include hp in
theorem globalScaleIndex_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0)
    (i : Fin 10) :
    globalLogRep (globalScaleIndex p side x) i ≤ globalScaleVector p side x i ∧
    globalScaleVector p side x i ≤ globalLogRep (globalScaleIndex p side x) i*Real.exp 1 :=
  normLogBin_scale_bounds _ (globalScaleVector_ge_one p hp side x hk i)

include hp in
theorem globalScaleIndex_error (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0)
    (i : Fin 10) :
    0 ≤ Real.log (globalScaleVector p side x i/globalLogRep (globalScaleIndex p side x) i) ∧
    Real.log (globalScaleVector p side x i/globalLogRep (globalScaleIndex p side x) i) ≤ 1 :=
  normLogBin_error _ (globalScaleVector_ge_one p hp side x hk i)

def globalLogSector (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  s.filter (fun x => globalScaleIndex p side x=j)

end

def globalLogBox (U : Fin 10 → ℝ) : Finset GlobalLogIndex :=
  Fintype.piFinset (fun i => Finset.range (normLogBin (U i)+1))

theorem globalLogBox_card (U : Fin 10 → ℝ) :
    (globalLogBox U).card=∏ i : Fin 10,(normLogBin (U i)+1) := by
  simp only [globalLogBox,Fintype.card_piFinset,Finset.card_range]

theorem globalScaleIndex_mem_box {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (U : Fin 10 → ℝ)
    (hU : ∀ i,globalScaleVector p side x i ≤ U i) :
    globalScaleIndex p side x∈globalLogBox U := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (normLogBin_mono (zero_lt_one.trans_le (globalScaleVector_ge_one p hp side x hk i)) (hU i))

theorem sum_globalLogSector {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (s : Finset (GlobalSecondData ι)) (side : Bool) (U : Fin 10 → ℝ)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hU : ∀ x∈s,∀ i,globalScaleVector p side x i ≤ U i) (f : GlobalSecondData ι → M) :
    ∑ x∈s,f x=∑ j∈globalLogBox U,∑ x∈globalLogSector p s side j,f x := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => globalScaleIndex_mem_box p hp side x (hk x hx) U (hU x hx)) f

def globalPooledColumnScale (ell : ℝ) (j : GlobalLogIndex) : ℝ :=
  ell/(globalLogRep j 0*globalLogRep j 1*globalLogRep j 2*globalLogRep j 3*globalLogRep j 6*globalLogRep j 7)

def globalPooledLabelScale (j : GlobalLogIndex) : ℝ :=
  globalLogRep j 1*globalLogRep j 4*globalLogRep j 6*globalLogRep j 7*Real.exp 4

def globalPooledRowScale (K ell B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)

def globalPooledDelta (B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  B*F*globalLogRep j 0*globalLogRep j 2*globalLogRep j 3

def globalPooledNaturalRow (K B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  K*globalLogRep j 4/((globalPooledDelta B F j)^2*B^2)

theorem globalPooledColumnScale_pos (ell : ℝ) (hell : 0 < ell) (j : GlobalLogIndex) :
    0 < globalPooledColumnScale ell j := by
  unfold globalPooledColumnScale
  apply div_pos hell
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (globalLogRep_pos j 0)
    (globalLogRep_pos j 1)) (globalLogRep_pos j 2)) (globalLogRep_pos j 3))
    (globalLogRep_pos j 6)) (globalLogRep_pos j 7)

theorem globalPooledLabelScale_ge_one (j : GlobalLogIndex) : 1 ≤ globalPooledLabelScale j := by
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 1) (globalLogRep_ge_one j 4))
        (globalLogRep_ge_one j 6)) (globalLogRep_ge_one j 7)) (Real.one_le_exp (by norm_num))

theorem globalPooled_mass (ell B F : ℝ) (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalPooledColumnScale ell j*globalPooledLabelScale j =
      Real.exp 4*((ell*B^3)*F)*globalLogRep j 4/(globalPooledDelta B F j*B^2) := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  unfold globalPooledColumnScale globalPooledLabelScale globalPooledDelta
  field_simp [h]

theorem globalPooled_radial_ratio (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalPooledRowScale K ell B F j*globalLogRep j 8/
      (globalLogRep j 5*(globalLogRep j 6)^2*(globalLogRep j 7)^2*(globalPooledColumnScale ell j)^2) =
    Real.exp 1*(globalLogRep j 8/globalPooledNaturalRow K B F j) := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  unfold globalPooledRowScale globalPooledColumnScale globalPooledNaturalRow globalPooledDelta
  field_simp [h]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem maskedPairDualTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M N K : ℝ),
      G≠0 → I≠0 → J≠0 → 0<M → 1≤N → 0≤K →
      N/2≤(Ideal.absNorm I:ℝ) → (Ideal.absNorm I:ℝ)≤N →
      N/2≤(Ideal.absNorm J:ℝ) → (Ideal.absNorm J:ℝ)≤N →
      ‖maskedPairDualTail G I J W M K‖ ≤
        (2*M/N)*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := dualSquarefreeTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro G I J W M N K hG hI hJ hM hN hK hIl hIu hJl hJu
  have hNG : 0<(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNI : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNJ : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hN0 : 0<N := by linarith
  let t0 := M/((Ideal.absNorm G:ℝ)*N*N)
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 t0)^2*(1+t0*K)^A)
  have ht0 : 0<t0 := by dsimp only [t0]; positivity
  have hT : 0≤T := by dsimp only [T]; positivity
  have hterm (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
        dualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K‖ ≤ T := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hqN : (Ideal.absNorm q:ℝ)≤(Ideal.absNorm G:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by exact_mod_cast hNG) (map_dvd Ideal.absNorm hqG)
    have ht : 0<M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by positivity
    have htlo : t0≤M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
      apply div_le_div_of_nonneg_left hM.le (by positivity)
      gcongr
    have hc : ‖(UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ)‖≤1 := by
      rw [norm_div,norm_mul,Complex.norm_natCast]
      have hp : ‖unrestrictedPairCharacter I J q‖≤1 := by
        rw [unrestrictedPairCharacter,norm_mul]
        exact (mul_le_mul (quadraticRow_norm_le_one _ _) (quadraticRow_norm_le_one _ _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      calc
        _ ≤ (1*1)/(Ideal.absNorm q:ℝ) := by
          gcongr
          exact QuadraticInitialBound.norm_ideal_moebius_le_one q
        _ ≤ 1 := by simpa only [one_mul,div_one] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq1)
    have hb : ‖dualSquarefreeTail I J W
        (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K‖≤T := by
      apply (hbound I J W _ K ht hK).trans
      dsimp only [T]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    rw [norm_mul]
    exact (mul_le_mul hc hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hpref : ‖(M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ)‖≤2*M/N := by
    simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM.le,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one,one_mul] using
      dual_truncation_prefactor_bound M 1 N (Ideal.absNorm I) (Ideal.absNorm J)
        hM (by norm_num) hN0 ⟨hIl,hIu⟩ ⟨hJl,hJu⟩
  rw [maskedPairDualTail,norm_mul]
  calc
    _ ≤ (2*M/N)*(∑ q ∈ idealDivisors G, T) := mul_le_mul hpref
      ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,T,t0]; ring

theorem coprime_pair_error_energy {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (E : ℝ) (hE : 0≤E)
    (error : n → n → ℂ) (herr : ∀ j k, ‖error j k‖≤E) :
    ‖∑ j, ∑ k, if IsCoprime (cols j) (cols k) then star (a j)*a k*error j k else 0‖ ≤
      (Fintype.card n:ℝ)*E*∑ j, ‖a j‖^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖*‖a k‖*E) = (∑ j, ‖a j‖)^2*E := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ ≤ ∑ j, ∑ k, ‖if IsCoprime (cols j) (cols k) then star (a j)*a k*error j k else 0‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j, ∑ k, ‖a j‖*‖a k‖*E := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · simp only [norm_mul,norm_star]
        exact mul_le_mul_of_nonneg_left (herr j k) (by positivity)
      · simp only [norm_zero]
        positivity
    _ = (∑ j, ‖a j‖)^2*E := hs
    _ ≤ ((∑ j, ‖a j‖^2)*(Fintype.card n:ℝ))*E := mul_le_mul_of_nonneg_right hcs hE
    _ = _ := by ring

theorem maskedDualTailFamily_bound (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ)
      (W : 𝓢(ℝ,ℂ)) (M N K : ℝ), G≠0 → Function.Injective cols →
      0<M → 1≤N → 0≤K →
      (∀ j, cols j≠0 ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
      ‖maskedDualTailFamily G cols a W M K‖ ≤
        256*M*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) * ∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,hbound⟩ := maskedPairDualTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro n _ G cols a W M N K hG hinj hM hN hK hcols
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*(1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)
  have hT : 0≤T := by dsimp only [T]; positivity
  have hn := finite_ideal_family_card_bound cols hinj N hN
    (fun j => (hcols j).1) (fun j => (hcols j).2.2)
  have herr (j k : n) : ‖maskedPairDualTail G (cols j) (cols k) W M K‖≤
      (2*M/N)*(idealDivisors G).card*T :=
    hbound G (cols j) (cols k) W M N K hG (hcols j).1 (hcols k).1 hM hN hK
      (hcols j).2.1 (hcols j).2.2 (hcols k).2.1 (hcols k).2.2
  calc
    _ ≤ (Fintype.card n:ℝ)*((2*M/N)*(idealDivisors G).card*T)*∑ j, ‖a j‖^2 :=
      coprime_pair_error_energy cols a _ (by positivity) _ herr
    _ ≤ (128*N)*((2*M/N)*(idealDivisors G).card*T)*∑ j, ‖a j‖^2 := by gcongr
    _ = _ := by dsimp only [T]; field_simp; ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalActualResidualScale (ell : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℝ :=
  globalFirstColumnScale p ell x side/
    (primeProductNorm p x.firstCommon*primeProductNorm p x.source.divisor*
      primeProductNorm p (x.source.sourceCommon\x.source.divisor))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalActualResidualScale_pos (ell : ℝ) (hell : 0 < ell) (side : Bool) (x : GlobalSecondData ι) :
    0 < globalActualResidualScale p ell side x := by
  exact div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (mul_pos (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
      (FirstPassCubeLabels.primeProductNorm_pos p hp _))

include hp in

theorem globalPooled_log_coordinates (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    let j := globalScaleIndex p side x
    let d := expansionSupportData x.common x.firstDivisor x.source
    |secondSectorZ p (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) d| ≤ 6 ∧
    |secondSectorUd p (globalLogRep j 5) d| ≤ 6 ∧
    |secondSectorUe p (globalLogRep j 6) d| ≤ 6 ∧
    |secondSectorUv p (globalLogRep j 7) d| ≤ 6 ∧
    |secondSectorKap p (globalLogRep j 8) d| ≤ 6 := by
  let j := globalScaleIndex p side x
  let I : Finset (Fin 10) := {0,1,2,3,6,7}
  have hpos (i : Fin 10) : 0 < globalScaleVector p side x i :=
    zero_lt_one.trans_le (globalScaleVector_ge_one p hp side x hk i)
  have herr (i : Fin 10) := globalScaleIndex_error p hp side x hk i
  have hn (i : Fin 10) : globalScaleVector p side x i/globalLogRep j i ≠ 0 :=
    div_ne_zero (hpos i).ne' (globalLogRep_pos j i).ne'
  have hprod : primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x =
      ∏ i∈I,globalScaleVector p side x i/globalLogRep j i := by
    have h (i : Fin 10) := (globalLogRep_pos j i).ne'
    have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
    have ht := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).ne'
    have he := (FirstPassCubeLabels.primeProductNorm_pos p hp x.source.divisor).ne'
    have hr := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).ne'
    norm_num [I,globalScaleVector,globalPooledColumnScale,globalActualResidualScale,globalFirstColumnScale]
    field_simp [h]

  have hlog : 0 ≤ Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x) ∧
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
        globalActualResidualScale p ell side x) ≤ 6 := by
    rw [hprod,Real.log_prod (fun i hi => hn i)]
    constructor
    · exact Finset.sum_nonneg (fun i hi => (herr i).1)
    · calc
        _ ≤ ∑ i∈I,(1 : ℝ) := Finset.sum_le_sum (fun i hi => (herr i).2)
        _ = 6 := by norm_num [I]
  have hsmall (i : Fin 10) : |Real.log (globalScaleVector p side x i/globalLogRep j i)| ≤ 6 := by
    rw [abs_of_nonneg (herr i).1]
    exact (herr i).2.trans (by norm_num)
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · change |Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j/
      globalActualResidualScale p ell side x)| ≤ 6
    rw [abs_of_nonneg hlog.1]
    exact hlog.2
  · change |Real.log (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)‖^2 / globalLogRep j 5)| ≤ 6
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact hsmall 5
  · change |Real.log (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor)‖^2 / globalLogRep j 6)| ≤ 6
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact hsmall 6
  · exact hsmall 7
  · exact hsmall 8

include hp in

theorem globalPooled_target_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    let j := globalScaleIndex p side x
    (Ideal.absNorm (SecondPassFiber.newLabel (globalSecondTuple p x)) : ℝ) ≤ globalPooledLabelScale j ∧
    ‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2 ≤ globalLogRep j 8*Real.exp 1 := by
  let j := globalScaleIndex p side x
  have hb (i : Fin 10) := (globalScaleIndex_bounds p hp side x hk i).2
  refine ⟨?_,hb 8⟩
  have he : (Ideal.absNorm (SecondPassFiber.newLabel (globalSecondTuple p x)) : ℝ) =
      globalScaleVector p side x 1*globalScaleVector p side x 4*
        globalScaleVector p side x 6*globalScaleVector p side x 7 := by
    rw [show SecondPassFiber.newLabel (globalSecondTuple p x) =
      secondSupportNewLabel p x.cube.support x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
        (expansionSupportData x.common x.firstDivisor x.source) from rfl,
      secondSupportNewLabel_norm,globalBaseLabel_norm]
    rfl
  rw [he]
  calc
    _ ≤ (globalLogRep j 1*Real.exp 1)*(globalLogRep j 4*Real.exp 1)*
        (globalLogRep j 6*Real.exp 1)*(globalLogRep j 7*Real.exp 1) := by
      have hpos (i : Fin 10) := (globalScaleVector_ge_one p hp side x hk i).trans' (by norm_num : (0:ℝ) ≤ 1)
      have hr1 := (globalLogRep_pos j 1).le
      have hr4 := (globalLogRep_pos j 4).le
      have hr6 := (globalLogRep_pos j 6).le
      have hr7 := (globalLogRep_pos j 7).le
      gcongr <;> first | exact hpos _ | exact hb _
    _ = globalPooledLabelScale j := by
      unfold globalPooledLabelScale
      rw [show (4:ℝ)=1+1+1+1 by norm_num,Real.exp_add,Real.exp_add,Real.exp_add]
      ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

private theorem five_factor_bounds (a b c d e : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) :
    a ≤ a*b*c*d*e ∧ b ≤ a*b*c*d*e ∧ c ≤ a*b*c*d*e ∧ d ≤ a*b*c*d*e ∧ e ≤ a*b*c*d*e := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · calc
      a = a*1*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      b = 1*b*1*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      c = 1*1*c*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      d = 1*1*1*d*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      e = 1*1*1*1*e := by ring
      _ ≤ _ := by gcongr

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSupported_small_norms (ell M : ℝ) (_hell : 0 < ell) (side : Bool)
    (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source) :
    primeProductNorm p (x.cube.sideDivisor side) ≤ ell*Real.exp M ∧
    primeProductNorm p x.common ≤ ell*Real.exp M ∧
    primeProductNorm p x.firstCommon ≤ ell*Real.exp M ∧
    primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ ell*Real.exp M ∧
    primeProductNorm p x.source.divisor ≤ ell*Real.exp M ∧
    primeProductNorm p x.source.overlap ≤ ell*Real.exp M := by
  have ha := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have hc := primeProductNorm_ge_one p hp x.common
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hg := primeProductNorm_ge_one p hp x.source.sourceCommon
  have hv := primeProductNorm_ge_one p hp x.source.overlap
  have hden : 0 < primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*primeProductNorm p x.firstCommon := by positivity
  have heq : (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon)*Real.exp M =
      (ell*Real.exp M)/(primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*primeProductNorm p x.firstCommon) := by
    unfold globalFirstColumnScale
    ring
  have hprod := (le_div_iff₀ hden).mp (hs.2.trans_eq heq)
  have hprod' : primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common*
      primeProductNorm p x.firstCommon*primeProductNorm p x.source.sourceCommon*primeProductNorm p x.source.overlap ≤ ell*Real.exp M := by
    convert hprod using 1 ; ring
  obtain ⟨ha',hc',ht',hg',hv'⟩ := five_factor_bounds _ _ _ _ _ ha hc ht hg hv
  refine ⟨ha'.trans hprod',hc'.trans hprod',ht'.trans hprod',?_,?_,hv'.trans hprod'⟩
  · exact (primeProductNorm_mono p hp Finset.sdiff_subset).trans (hg'.trans hprod')
  · exact (primeProductNorm_mono p hp hx.2.1).trans (hg'.trans hprod')

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCube_radical_bound (B : ℝ) (hB : 0 ≤ B) (x : GlobalSecondData ι)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    primeProductNorm p x.cube.support ≤ B^2 := by
  have hd : (∏ i∈x.cube.support,p i) ∣ primeProduct p x.cube.support x.cube.leftExponent *
      primeProduct p x.cube.support x.cube.rightExponent := by
    rw [← primeProduct_add]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using pow_dvd_pow (p i) (x.cube.support_pos i hi)
  have hb0 := mul_ne_zero (primeProduct_ne_zero p hp x.cube.support x.cube.leftExponent)
    (primeProduct_ne_zero p hp x.cube.support x.cube.rightExponent)
  have hn := element_norm_le_of_dvd hb0 hd
  simp only [map_mul,norm_mul,mul_pow] at hn
  exact hn.trans (by simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB)

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSupported_divisor_bound (ell B M : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    primeProductNorm p x.firstDivisor ≤ (ell*Real.exp M)*B^2 := by
  have hC := (globalSupported_small_norms p hp ell M hell side x hx hs).2.1
  have hrad := globalCube_radical_bound p hp B hB x hb₁ hb₂
  calc
    _ ≤ primeProductNorm p (x.common∪x.cube.support) := primeProductNorm_mono p hp hx.2.2.2
    _ = primeProductNorm p x.common*primeProductNorm p x.cube.support :=
      FirstPassCubeLabels.primeProductNorm_union p _ _ hx.2.2.1
    _ ≤ _ := mul_le_mul hC hrad (FirstPassCubeLabels.primeProductNorm_pos p hp _).le (by positivity)

include hp in

theorem globalSupported_cutoff_row_bound (ell B Y M Z : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hY : 0 < Y) (hZ : 0 ≤ Z) (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      Y M Z x.source.sourceCommon x.source.divisor) :
    ‖eisEmbedding (SecondPassFiber.newRow (globalSecondTuple p x))‖^2 ≤
      3*(ell*Real.exp M)^2*B^2*((⌈Z*(ell*Real.exp M)^2/Y⌉₊ : ℝ)+1)^2 := by
  let X := globalFirstColumnScale p ell x side
  let U := (X/primeProductNorm p x.firstCommon)*Real.exp M
  let lengthScale := ell*Real.exp M
  have hsmall := globalSupported_small_norms p hp ell M hell side x hx hs
  have hD := globalSupported_divisor_bound p hp ell B M hell hB side x hx hs hb₁ hb₂
  have ha := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have hc := primeProductNorm_ge_one p hp x.common
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hX : X ≤ ell := by
    exact div_le_self hell.le (one_le_mul_of_one_le_of_one_le ha hc)
  have hU : U ≤ lengthScale := mul_le_mul_of_nonneg_right
    ((div_le_self (globalFirstColumnScale_pos p hp ell hell x side).le ht).trans hX) (Real.exp_pos M).le
  have hU0 : 0 ≤ U := by
    exact (mul_pos (div_pos (globalFirstColumnScale_pos p hp ell hell x side)
      (FirstPassCubeLabels.primeProductNorm_pos p hp _)) (Real.exp_pos M)).le
  have hden : primeProductNorm p x.source.divisor *
      (((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M)^2 ≤ lengthScale^2 := by
    rw [show ((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M =
      U/primeProductNorm p x.source.sourceCommon by dsimp [U];ring]
    exact (supported_cutoff_denominator _ _ _ (primeProductNorm_mono p hp hx.2.1)
      (primeProductNorm_ge_one p hp _)).trans (pow_le_pow_left₀ hU0 hU 2)
  have hr : Z/(Y/(primeProductNorm p x.source.divisor *
      (((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M)^2)) ≤ Z*lengthScale^2/Y := by
    rw [div_div_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hden hZ) hY.le
  have hceil : (⌈Z/(Y/(primeProductNorm p x.source.divisor *
      (((X/primeProductNorm p x.firstCommon)/primeProductNorm p x.source.sourceCommon)*Real.exp M)^2))⌉₊ : ℝ) ≤
      (⌈Z*lengthScale^2/Y⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hr
  have hf := secondFrequencyCutoff_norm_sq_le _ Z x.source.frequency hk
  simp only [primeSubsetGenerator_norm_eq_productNorm] at hf
  have hf' : ‖eisEmbedding x.source.frequency‖^2 ≤ 3*((⌈Z*lengthScale^2/Y⌉₊ : ℝ)+1)^2 := by
    apply hf.trans
    gcongr
  change ‖eisEmbedding (actualSecondRow p x.firstDivisor x.source.divisor x.source.frequency)‖^2 ≤ _
  simp only [actualSecondRow,map_mul,norm_mul,mul_pow,primeSubsetGenerator_norm_eq_productNorm]
  calc
    _ ≤ (lengthScale*B^2)*lengthScale*(3*((⌈Z*lengthScale^2/Y⌉₊ : ℝ)+1)^2) := by
      exact mul_le_mul (mul_le_mul hD hsmall.2.2.2.2.1 (FirstPassCubeLabels.primeProductNorm_pos p hp _).le (by positivity))
        hf' (sq_nonneg _) (by dsimp [lengthScale]; positivity)
    _ = _ := by dsimp [lengthScale];ring_nf

def globalNormCaps (ell B Y M Z : ℝ) : Fin 10 → ℝ :=
  let lengthScale := ell*Real.exp M
  ![lengthScale,lengthScale,lengthScale,lengthScale,B^2,lengthScale*B^2,lengthScale,lengthScale,3*lengthScale^2*B^2*((⌈Z*lengthScale^2/Y⌉₊ : ℝ)+1)^2,B^2]

include hp in
theorem globalScaleVector_le_caps (ell B Y M Z : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hY : 0 < Y) (hZ : 0 ≤ Z) (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      Y M Z x.source.sourceCommon x.source.divisor) :
    ∀ i,globalScaleVector p side x i ≤ globalNormCaps ell B Y M Z i := by
  obtain ⟨ha,hc,ht,hr,he,hv⟩ := globalSupported_small_norms p hp ell M hell side x hx hs
  have hd := globalSupported_divisor_bound p hp ell B M hell hB side x hx hs hb₁ hb₂
  have hrow := globalSupported_cutoff_row_bound p hp ell B Y M Z hell hB hY hZ side x hx hs hb₁ hb₂ hk
  have hJ := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB hb₁ hb₂).1
  have hrad := globalCube_radical_bound p hp B hB x hb₁ hb₂
  have hactive : (globalCubeActiveRoot p x)^2 ≤ B^2 :=
    (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans hrad
  intro i
  fin_cases i
  · exact ha
  · exact hc
  · exact ht
  · exact hr
  · exact hJ
  · exact hd
  · exact he
  · exact hv
  · exact hrow
  · exact hactive

include hp in

theorem globalScaleIndex_mem_concrete_box (ell B Y M Z : ℝ) (hell : 0 < ell) (hB : 0 ≤ B)
    (hY : 0 < Y) (hZ : 0 ≤ Z) (side : Bool) (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hk0 : x.source.frequency ≠ 0)
    (hk : x.source.frequency ∈ firstCoreSecondCutoff p x.firstCommon (globalFirstColumnScale p ell x side)
      Y M Z x.source.sourceCommon x.source.divisor) :
    globalScaleIndex p side x∈globalLogBox (globalNormCaps ell B Y M Z) :=
  globalScaleIndex_mem_box p hp side x hk0 _
    (globalScaleVector_le_caps p hp ell B Y M Z hell hB hY hZ side x hx hs hb₁ hb₂ hk)

end SecondPassArithmetic

end

end OAI
