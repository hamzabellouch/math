import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich
import OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource

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
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma columnLog_three_split (A C S:Finset ι) (hAC:Disjoint A C)
    (hAS:Disjoint A S) (hCS:Disjoint C S) (ell:ℝ) (hell:0<ell) :
    columnLog p ell ((A∪C)∪S)=columnLog p (ell/(primeProductNorm p A*primeProductNorm p C)) S := by
  unfold columnLog
  rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hAS,hCS⟩),
    primeProductNorm_union p A C hAC]
  congr 1
  have hA := (primeProductNorm_pos p hp A).ne'
  have hC := (primeProductNorm_pos p hp C).ne'
  field_simp

include hp in
lemma canonicalCubeResidual_log
    (b:CubeCoordinates ι) (hb:b.Admissible) (C S:Finset ι)
    (hCB:Disjoint C b.support) (hSC:Disjoint S C) (hSB:Disjoint S b.support)
    (negative:Bool) (Ψ:O→*ℂ) (m f:O) (g:𝓢(ℝ,ℂ)) (ell:ℝ) (hell:0<ell) :
    canonicalCubeResidual p hg b C negative Ψ m f (fun U=>g (columnLog p ell U)) S =
      originalLabelColumn p hg b.support b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p Ψ m (fun U=>g (columnLog p
          (ell/(primeProductNorm p (b.sideDivisor (!negative))*primeProductNorm p C)) U)))
        (∏i∈C,p i) f S := by
  have hA : b.sideDivisor (!negative)⊆b.support := by
    cases negative
    · exact hb.1
    · exact hb.2
  have hlog:=columnLog_three_split p hp (b.sideDivisor (!negative)) C S
    (hCB.symm.mono_left hA) (hSB.symm.mono_left hA) hSC.symm ell hell
  unfold canonicalCubeResidual originalLabelColumn multiplicativeCoreColumn
  have hside : (if negative then b.rightDivisor else b.leftDivisor)=b.sideDivisor (!negative) := by cases negative <;> rfl
  rw [hside]
  dsimp only
  rw [hlog]

lemma actualFirstKernel_insert_windows
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (Ψ₁ Ψ₂:O→*ℂ)
    (m₁ m₂ c f:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (X₁ X₂ K:ℝ) (d h:O)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) c f)
      (originalLabelColumn p hg B ε₁ ε₂ false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) c f)
      W (fun _=>1) (fun _=>1) X₁ X₂ K d h =
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) c f)
      (originalLabelColumn p hg B ε₁ ε₂ false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) c f)
      W V₁ V₂ X₁ X₂ K d h := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP:Disjoint N P
  · simp only [hNP,ite_true,one_mul]
    by_cases h₁:g₁ (columnLog p X₁ N)=0
    · simp only [threeGaussRowFactor,originalLabelColumn,multiplicativeCoreColumn,h₁,mul_zero,zero_mul,star_zero]
    by_cases h₂:g₂ (columnLog p X₂ P)=0
    · simp only [threeGaussRowFactor,originalLabelColumn,multiplicativeCoreColumn,h₂,mul_zero,zero_mul]
    rw [hV₁ _ h₁,hV₂ _ h₂,one_mul,one_mul]
  · simp only [hNP,ite_false]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic

lemma conductor_zero_swap (parityBit a b:Bool) :
    conductorExponent parityBit a b=0 ↔ conductorExponent parityBit b a=0 := by
  cases parityBit <;> cases a <;> cases b <;> decide

lemma conductor_parity_swap (parityBit a b:Bool) :
    (conductorExponent parityBit a b).val%2=(conductorExponent parityBit b a).val%2 := by
  cases parityBit <;> cases a <;> cases b <;> decide

lemma dilationExponent_swap (parityBit a b:Bool) :
    dilationExponent parityBit a b=dilationExponent parityBit b a := by
  cases parityBit <;> cases a <;> cases b <;> rfl

lemma retained_swap (parityBit a b:Bool) : retained parityBit a b=retained parityBit b a := by
  cases parityBit <;> cases a <;> cases b <;> rfl

lemma b0Exponent_swap (m:ℕ) (a b:Bool) : b0Exponent m a b=b0Exponent m b a := by
  cases a <;> cases b <;> simp [b0Exponent,evenDouble]

variable {ι:Type*} (p:ι→O) (B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)

lemma cubeActiveSupport_swap : cubeActiveSupport B v ε₁ ε₂=cubeActiveSupport B v ε₂ ε₁ := by
  ext i
  simp only [cubeActiveSupport,Finset.mem_filter]
  constructor
  · rintro ⟨hi,he⟩
    exact ⟨hi,fun hx=>he ((conductor_zero_swap (parity (v i)) (ε₁ i) (ε₂ i)).mpr hx)⟩
  · rintro ⟨hi,he⟩
    exact ⟨hi,fun hx=>he ((conductor_zero_swap (parity (v i)) (ε₁ i) (ε₂ i)).mp hx)⟩

lemma cubeOddSupport_swap : cubeOddSupport B v ε₁ ε₂=cubeOddSupport B v ε₂ ε₁ := by
  ext i
  simp only [cubeOddSupport,Finset.mem_filter,conductor_parity_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma dilationLabel_swap : dilationLabel p B v ε₁ ε₂=dilationLabel p B v ε₂ ε₁ := by
  unfold dilationLabel primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [dilationExponent_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma jLabel_swap : jLabel p B v ε₁ ε₂=jLabel p B v ε₂ ε₁ := by
  unfold jLabel primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [retained_swap (parity (v i)) (ε₁ i) (ε₂ i)]

lemma b0Label_swap : b0Label p B v ε₁ ε₂=b0Label p B v ε₂ ε₁ := by
  unfold b0Label primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [b0Exponent_swap (v i) (ε₁ i) (ε₂ i)]
end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic FirstPassCubeLabels

theorem firstInputFamilyEnergy_swap {ι:Type*} [DecidableEq ι]
    (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal] (hg:∀i,lambda∉Ideal.span {p i})
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (negative:Bool)
    (Ψ:O→*ℂ) (m:O) (H:Finset ι→ℂ) (V:ℝ→ℂ) (X:ℝ) (c d:O) (J:ℕ) (T:Finset O) :
    firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T =
    firstInputFamilyEnergy p hg F B v ε₂ ε₁ negative Ψ m H V X c d J T := by
  simp only [firstInputFamilyEnergy,firstCoreOuter,firstCoreInputRow,
    cubeOddSupport_swap B v ε₁ ε₂,b0Label_swap p B v ε₁ ε₂,jLabel_swap p B v ε₁ ε₂]

namespace CubeCoordinates
variable {ι:Type*}
def swap (b:CubeCoordinates ι) : CubeCoordinates ι :=
  ⟨b.rightExponent,b.leftExponent,b.rightDivisor,b.leftDivisor⟩
@[simp] lemma swap_swap (b:CubeCoordinates ι) : b.swap.swap=b := by cases b;rfl
end CubeCoordinates
end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def orientedCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) b.common
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  (primeProductNorm p b.firstDivisor : ℂ)⁻¹ * ∑ x∈s,a x*actualFirstKernel p hp hcop hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    (originalLabelColumn p hg b.cube.support b.cube.rightBit b.cube.leftBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.rightBit b.cube.leftBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    W V₁ V₂ X₁ X₂ K d x.2

end

theorem orientedCubeFirstBlock_input_transfer
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
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (K ell B F Ymax : ℝ),
      0<K → 0<ell → 0<B → 0<F →
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
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_full_uniform_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
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
  have hpref : 0≤C*Ymax^deltaLoss := mul_nonneg hC (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      (C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
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
      _ _ hX₁ hX₂ K hK (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
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
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [orientedCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hD.le,←mul_assoc]
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ globalCubeCoefficient p K ell B F true b*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,(C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = (C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = (C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ (C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem orientedTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
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
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := orientedCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Cd₁,Ct₁,hC₁,hCd₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Cd₂,Ct₂,hC₂,hCd₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCfirst,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  have hB0 : 0<B := by linarith
  let T := fun b => globalCubeFirstTargets p b (s b)
  have hT0 (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) : z≠0 :=
    globalCubeFirstTargets_ne_zero p hp b (s b) (hsf b hb) (hs0 b hb) z hz
  have hT (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) :=
    globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB0 hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz
  have hTc (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hblock := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F
    (globalFirstRowCap K ell B F) hK hell hB0 hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB0 hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0 (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx) hT0 hT
  have hl := hleft p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₁ m₁ T
    hΓ hw hK hell hB hF hH hU hellU1 hadm hΨ₁ hb₁ hb₂ hT hT0
  have hr := hright p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₂ m₂ T
    hΓ hw hK hell hB hF hH hU hellU2 hadm hΨ₂ hb₁ hb₂ hTc hT0
  have hprefix : 0≤Cfirst*(globalFirstRowCap K ell B F)^deltaLoss :=
    mul_nonneg hCfirst (Real.rpow_nonneg (globalFirstRowCap_pos K ell B F hK hell hB0 hF).le _)
  exact hblock.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _)))

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

local instance : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
local instance : BorelSpace EuclideanSpatial := ⟨rfl⟩

def euclideanC1cToH1 (f : C1c (E := EuclideanSpatial)) :
    h1 (E := EuclideanSpatial) («μ» := (volume : Measure EuclideanSpatial)) := by
  let gr := graph (E := EuclideanSpatial) («μ» := (volume : Measure EuclideanSpatial))
  refine ⟨gr f,?_⟩
  exact (LinearMap.range gr).le_topologicalClosure ⟨f,rfl⟩

lemma euclideanC1cToH1_norm (f : C1c (E := EuclideanSpatial)) :
    ‖euclideanC1cToH1 f‖=max ‖toL2 («μ» := volume) f‖ ‖toL2Grad («μ» := volume) f‖ := rfl

lemma euclideanC1c_supported_range (K : Set EuclideanSpatial) (hK : MeasurableSet K)
    (f : C1c (E := EuclideanSpatial)) (hf : Function.support f.1⊆K) :
    toL2 («μ» := volume) f∈LinearMap.range
      (Lp.extendByZeroₗᵢ («μ» := (volume : Measure EuclideanSpatial)) (p := (2:ℝ≥0∞)) hK).toLinearMap := by
  have hmem := memLp_of_mem_C1c («μ» := (volume : Measure EuclideanSpatial)) f.2
  have hres : MemLp f.1 2 (volume.restrict K) := hmem.mono_measure Measure.restrict_le_self
  refine ⟨hres.toLp f.1,?_⟩
  apply Lp.ext
  have hext := Lp.extendByZeroₗᵢ_ae_eq («μ» := (volume : Measure EuclideanSpatial)) hK (hres.toLp f.1)
  have hr : ∀ᵐx ∂(volume : Measure EuclideanSpatial),x∈K→hres.toLp f.1 x=f.1 x :=
    (ae_restrict_iff' hK).mp hres.coeFn_toLp
  have hg : (toL2 («μ» := volume) f : EuclideanSpatial→ℝ)=ᵐ[volume]f.1 := hmem.coeFn_toLp
  filter_upwards [hext,hr,hg] with x hx hrx hgx
  simp only [LinearIsometry.coe_toLinearMap]
  rw [hx,hgx]
  by_cases hxm : x∈K
  · simpa only [Set.indicator_of_mem hxm] using hrx hxm
  · rw [Set.indicator_of_notMem hxm]
    symm
    by_contra hne
    exact hxm (hf hne)

def euclideanC1cToSupportedH1 (K : Set EuclideanSpatial) (hK : MeasurableSet K)
    (f : C1c (E := EuclideanSpatial)) (hf : Function.support f.1⊆K) :
    h1On (E := EuclideanSpatial) K hK :=
  ⟨euclideanC1cToH1 f,euclideanC1c_supported_range K hK f hf⟩

lemma compact_clm_closedBall {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ V] [NormedSpace ℝ W] (T : V →L[ℝ] W)
    (hT : IsCompactOperator T) (R : ℝ) : IsCompact (closure (T '' Metric.closedBall 0 R)) :=
  IsCompactOperator.isCompact_closure_image_closedBall (f := T.toLinearMap) hT R

theorem euclidean_C1c_family_precompact (K : Set EuclideanSpatial) (hK : IsCompact K)
    (family : Set (C1c (E := EuclideanSpatial))) (R : ℝ)
    (hsupp : ∀f∈family,Function.support f.1⊆K)
    (hmass : ∀f∈family,‖toL2 («μ» := volume) f‖≤R)
    (hgrad : ∀f∈family,‖toL2Grad («μ» := volume) f‖≤R) :
    IsCompact (closure (toL2 («μ» := (volume : Measure EuclideanSpatial)) '' family)) := by
  let hKm := hK.measurableSet
  have hc := compact_clm_closedBall
    (V := h1On (E := EuclideanSpatial) K hKm)
    (W := Lp ℝ 2 (volume : Measure EuclideanSpatial))
    (h1OnToL2 (E := EuclideanSpatial) K hKm)
    (isCompactOperator_h1OnToL2 (E := EuclideanSpatial) hK hKm) R
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨euclideanC1cToSupportedH1 K hKm f (hsupp f hf),?_,rfl⟩
  have hn : ‖euclideanC1cToSupportedH1 K hKm f (hsupp f hf)‖≤R :=
    max_le (hmass f hf) (hgrad f hf)
  simpa only [Metric.mem_closedBall,dist_zero_right (euclideanC1cToSupportedH1 K hKm f (hsupp f hf))] using hn

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal InnerProductSpace

namespace CubicEisenstein

abbrev KernelFundamentalVolume : Measure HyperbolicSpace :=
  hyperbolicVolume.restrict (hyperbolicFundamentalSet globalKubotaKernel)

abbrev KernelGradientL2 := Lp (EuclideanSpace ℂ (Fin 3)) 2 KernelFundamentalVolume

lemma kernelTestPartial_continuous (f : kernelSmoothTests) (j : Fin 3) :
    Continuous (fun w => kernelTestPartial f w j) := by
  rw [continuous_iff_continuousAt]
  intro w
  exact (((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).continuousAt_fderiv
    (by simp)).clm_apply continuousAt_const).comp
      hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma kernelGradientAt_continuous (f : kernelSmoothTests) :
    Continuous (fun w => kernelGradientAt w f) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  exact (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
    (kernelTestPartial_continuous f j)

lemma kernelGradientAt_memLp (f : kernelSmoothTests) :
    MemLp (fun w => kernelGradientAt w f) 2 KernelFundamentalVolume := by
  apply (memLp_two_iff_integrable_sq_norm
    (kernelGradientAt_continuous f).aestronglyMeasurable).mpr
  have hh := (quotient_projection_measurePreserving globalKubotaKernel).integrable_comp_of_integrable
    (kernelQuotientEnergyDensity_integrable f)
  have he : (fun w => kernelQuotientEnergyDensity f (integralOrbitProjection globalKubotaKernel w))=
      kernelTestEnergyDensity f := rfl
  dsimp only [Function.comp_def] at hh
  rw [he] at hh
  simpa only [kernelGradientAt_norm_sq] using hh

def kernelGradientToL2 (f : kernelSmoothTests) : KernelGradientL2 :=
  (kernelGradientAt_memLp f).toLp (fun w => kernelGradientAt w f)

lemma kernelGradientToL2_coe (f : kernelSmoothTests) :
    (kernelGradientToL2 f : HyperbolicSpace → EuclideanSpace ℂ (Fin 3))=ᵐ[KernelFundamentalVolume]
      fun w => kernelGradientAt w f := (kernelGradientAt_memLp f).coeFn_toLp

lemma kernelGradientToL2_inner (f g : kernelSmoothTests) :
    inner ℂ (kernelGradientToL2 f) (kernelGradientToL2 g)=kernelDirichletForm f g := by
  rw [L2.inner_def,kernelDirichletForm,integralQuotientVolume_integral _ _
    (kernelDirichletPairDensity_integrable f g).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [kernelGradientToL2_coe f,kernelGradientToL2_coe g] with w hf hg
  rw [hf,hg,kernelDirichletPairDensity_coordinate]

lemma kernelGradientToL2_norm_sq (f : kernelSmoothTests) :
    ‖kernelGradientToL2 f‖^2=kernelDirichletEnergy f := by
  have hh := kernelGradientToL2_inner f f
  rw [inner_self_eq_norm_sq_to_K,kernelDirichletForm_self] at hh
  rw [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow] at hh
  exact Complex.ofReal_injective hh

def kernelGradientLinear : kernelSmoothTests →ₗ[ℂ] KernelGradientL2 where
  toFun := kernelGradientToL2
  map_add' f g := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (f+g),kernelGradientToL2_coe f,
      kernelGradientToL2_coe g,Lp.coeFn_add (kernelGradientToL2 f) (kernelGradientToL2 g)]
      with w hfg hf hg hadd
    simp only [hfg,hadd,Pi.add_apply,hf,hg,map_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [kernelGradientToL2_coe (c•f),kernelGradientToL2_coe f,
      Lp.coeFn_smul c (kernelGradientToL2 f)] with w hcf hf hsmul
    simp only [RingHom.id_apply,hcf,hsmul,Pi.smul_apply,hf,map_smul]

def kernelInitialGradientGraph : Submodule ℂ (KernelQuotientL2 × KernelGradientL2) :=
  LinearMap.range (kernelSmoothTestsToL2.prod kernelGradientLinear)

lemma kernelInitialGradientGraph_unique (x : KernelQuotientL2 × KernelGradientL2)
    (hx : x∈kernelInitialGradientGraph) (hz : x.1=0) : x.2=0 := by
  obtain ⟨f,hf⟩ := hx
  have hf1 : kernelSmoothTestsToL2 f=x.1 := congrArg Prod.fst hf
  have hf2 : kernelGradientLinear f=x.2 := congrArg Prod.snd hf
  have hzero : f=0 := kernelSmoothTestsToL2_injective (by
    simpa only [map_zero] using hf1.trans hz)
  rw [hzero,map_zero] at hf2
  exact hf2.symm

def kernelInitialGradient : KernelQuotientL2 →ₗ.[ℂ] KernelGradientL2 :=
  kernelInitialGradientGraph.toLinearPMap

lemma kernelInitialGradient_graph :
    kernelInitialGradient.graph=kernelInitialGradientGraph :=
  Submodule.toLinearPMap_graph_eq _ kernelInitialGradientGraph_unique

lemma kernelInitialGradient_dense_domain :
    Dense (kernelInitialGradient.domain : Set KernelQuotientL2) := by
  apply kernelSmoothTestsToL2_dense.mono
  rintro _ ⟨f,rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph
  rw [kernelInitialGradient_graph]
  exact ⟨f,rfl⟩

end CubicEisenstein

end

end OAI
