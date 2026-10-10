import OAI.NumberTheory.DirichletL.CubicSieve.LiteralSources

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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

def GlobalFirstAdmissible (b : GlobalFirstData ι) : Prop :=
  b.cube.Admissible ∧ Disjoint b.common b.cube.support ∧ b.firstDivisor ⊆ b.common∪b.cube.support

variable (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstIndex (side : Bool) (b : GlobalFirstData ι) : GlobalLogIndex :=
  globalScaleIndex p side (b.append ⟨∅,∅,∅,1⟩)

def globalFirstPooledRow (K ell B F : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  globalPooledRowScale K ell B F (globalFirstIndex p side b)

def globalFirstCoefficient (K ell B F : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  globalBinFirstCoefficient K ell B F (globalFirstIndex p side b)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalPooledRowScale_first (K ell B F : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    globalPooledRowScale K ell B F (globalScaleIndex p side x)=
      globalFirstPooledRow p K ell B F side x.first := by
  have hc (i : Fin 10) (hi : i=1 ∨ i=4 ∨ i=5 ∨ i=9) :
      globalLogRep (globalScaleIndex p side x) i=globalLogRep (globalFirstIndex p side x.first) i := by
    rcases hi with rfl|rfl|rfl|rfl <;>
      simp [globalLogRep,globalFirstIndex,globalScaleIndex,globalScaleVector,GlobalFirstData.append,GlobalSecondData.first,globalCubeJNorm,globalCubeActiveRoot]
  unfold globalFirstPooledRow globalPooledRowScale
  rw [hc 1 (by simp),hc 4 (by simp),hc 5 (by simp)]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalBinFirstCoefficient_first (K ell B F : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    globalBinFirstCoefficient K ell B F (globalScaleIndex p side x)=
      globalFirstCoefficient p K ell B F side x.first := by
  have hc (i : Fin 10) (hi : i=5 ∨ i=9) :
      globalLogRep (globalScaleIndex p side x) i=globalLogRep (globalFirstIndex p side x.first) i := by
    rcases hi with rfl|rfl <;>
      simp [globalLogRep,globalFirstIndex,globalScaleIndex,globalScaleVector,GlobalFirstData.append,GlobalSecondData.first,globalCubeJNorm,globalCubeActiveRoot]
  unfold globalFirstCoefficient globalBinFirstCoefficient
  rw [hc 5 (by simp),hc 9 (by simp)]

def globalFirstConcreteCutoff (K ell B F M H : ℝ) (side : Bool) (b : GlobalFirstData ι) :
    Finset ι → Finset ι → Finset O :=
  firstCoreSecondCutoff p b.firstCommon (globalFirstBlockColumnScale p ell side b)
    (globalFirstPooledRow p K ell B F side b) M H

def globalFirstSupportedPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) : Finset (GlobalSecondData ι) :=
  (globalFirstExpansionPool pool s cutoff).filter (fun x =>
    SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstSupportedPool_admissible (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hx : x∈globalFirstSupportedPool p pool s cutoff ell M side) : GlobalSecondAdmissible x := by
  have hm := (mem_globalFirstExpansionPool pool s cutoff x).mp (Finset.mem_filter.mp hx).1
  have hb := hs x.first hm.1
  have hE := ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.1
  exact ⟨hb.1,hE,hb.2.1,hb.2.2⟩

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstSupportedPool_frequency_ne_zero (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hx : x∈globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side) :
    x.source.frequency ≠ 0 := by
  have hm := (mem_globalFirstExpansionPool pool s _ x).mp (Finset.mem_filter.mp hx).1
  exact (Finset.mem_erase.mp ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.2.2).1

include hp in

theorem globalFirstSupportedPool_index_mem_box
    (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (K ell B F M H : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H)
    (side : Bool)
    (hb₁ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (x : GlobalSecondData ι)
    (hx : x∈globalFirstSupportedPool p pool s
      (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side) :
    globalScaleIndex p side x ∈ globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) := by
  have hm := (mem_globalFirstExpansionPool pool s _ x).mp (Finset.mem_filter.mp hx).1
  have hk := (Finset.mem_erase.mp ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.2.2)
  apply globalScaleIndex_mem_uniform_box p hp K ell B F M H hK hell hB hF hH side x
    (globalFirstSupportedPool_admissible p pool s hs _ ell M side x hx)
    (Finset.mem_filter.mp hx).2 (hb₁ x.first hm.1) (hb₂ x.first hm.1) hk.1
  simpa only [globalFirstConcreteCutoff,globalPooledRowScale_first,globalFirstBlockColumnScale,
    globalFirstColumnScale,GlobalSecondData.first] using hk.2

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem globalSecondLiteralTerm_zero_of_not_support
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (g W : 𝓢(ℝ,ℂ)) (ell Y M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hell : 0<ell) (hgM : ∀ t,g t ≠ 0 → |t|≤M) (hE : x.source.divisor⊆x.source.sourceCommon)
    (hs : ¬SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source) :
    globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell Y side x=0 := by
  have hX := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon)
  have hz := secondExpansionSource_singleton_zero_of_not_support p hp hcop hg hinj
    (globalSecondRawPool pool x) Ψ (m*globalFirstBlockBadLabel p x.first)
    (globalFirstBlockLabel p x.first) (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    ray g W (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) Y M hX hgM x.source hE hs
  unfold globalSecondLiteralTerm
  dsimp only
  simp only [globalFirstBlockBadLabel,globalFirstBlockLabel,GlobalSecondData.first] at hz
  rw [hz,mul_zero]

theorem globalFirstTruncatedSource_eq_supported
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell M : ℝ) (hell : 0<ell)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      ∑ ray : SecondRayIndex,∑ x∈globalFirstSupportedPool p pool s cutoff ell M side,
        w x.first*globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell (Y x.first) side x := by
  rw [globalFirstTruncatedSource_eq_literal p hp hcop hg hinj hc hpr]
  apply Finset.sum_congr rfl
  intro ray hray
  unfold globalFirstSupportedPool
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs,globalSecondLiteralTerm_zero_of_not_support p hp hcop hg hinj pool Ψ m ray g W ell (Y x.first) M side x hell hgM]
    · ring
    · exact ((mem_secondExpansionPool _ _ _).mp ((mem_globalFirstExpansionPool pool s cutoff x).mp hx).2).2.1
    · exact hs

theorem globalFirstTruncatedSource_eq_bins
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (K ell B F M H : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool)
    (hb₁ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
    let source := globalFirstSupportedPool p pool s cutoff ell M side
    globalFirstTruncatedSource p hp hg hinj pool s
      (fun b => w b*globalFirstCoefficient p K ell B F side b) cutoff Ψ m g W ell side
      (globalFirstPooledRow p K ell B F side) =
      ∑ j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
        (globalBinFirstCoefficient K ell B F j : ℂ)*
          globalSecondLiteralBinSource p hp hcop hg (fun x => w x.first) source side j pool Ψ m
            g g W ell (globalPooledRowScale K ell B F j) := by
  dsimp only
  rw [globalFirstTruncatedSource_eq_supported p hp hcop hg hinj hc hpr]
  · let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
    let source := globalFirstSupportedPool p pool s cutoff ell M side
    have hmap : ∀ x∈source,globalScaleIndex p side x∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) :=
      fun x hx => globalFirstSupportedPool_index_mem_box p hp pool s hs K ell B F M H hK hell hB hF hH side hb₁ hb₂ x hx
    change (∑ ray : SecondRayIndex,∑ x∈source,
      (w x.first*globalFirstCoefficient p K ell B F side x.first)*
        globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell
          (globalFirstPooledRow p K ell B F side x.first) side x) = _
    simp only [globalSecondLiteralBinSource,Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ray hray
    have hsplit := Finset.sum_fiberwise_of_maps_to hmap
      (fun x => (w x.first*globalFirstCoefficient p K ell B F side x.first)*
        globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell
          (globalFirstPooledRow p K ell B F side x.first) side x)
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro x hx
    have hxj := (Finset.mem_filter.mp hx).2
    have hy := globalPooledRowScale_first p K ell B F side x
    have hc' := globalBinFirstCoefficient_first p K ell B F side x
    rw [hxj] at hy hc'
    rw [← hy,← hc']
    ring
  · exact hell
  · exact hgM

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy)
open JointLogSeparation (frequencyTwist)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalChildBudget (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε θ₁ θ₂ K ell B F M H : ℝ) (A J : ℕ) (side : Bool) : ℝ :=
  ∑ j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
    ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p source side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))

end

theorem globalFirstTruncatedSource_actual_transfer
    (ε : ℝ) (hε : 0<ε) (g W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0≤C ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℂ) (Γ θ K ell B F H : ℝ) (side : Bool)
      (Ψ : O →* ℂ) (m : O),
      0≤Γ → (∀ b∈s,‖w b‖≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
      let source := globalFirstSupportedPool p pool s cutoff ell M side
      ‖globalFirstTruncatedSource p hp hg hinj pool s
        (fun b => w b*globalFirstCoefficient p K ell B F side b) cutoff Ψ m
        (frequencyTwist g θ) W ell side (globalFirstPooledRow p K ell B F side)‖ ≤
      globalChildBudget p hp hcop hg pool source Ψ m windows (Γ*C) ε θ θ K ell B F M H A J side := by
  obtain ⟨windows,C,hC,hwc,hws,hwb,htrans⟩ := globalSecondLiteralBinSource_transfer ε hε g g W M hM hgM hgM A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ θ K ell B F H side Ψ m hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂
  dsimp only
  let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
  let source := globalFirstSupportedPool p pool s cutoff ell M side
  have htw : ∀ t,frequencyTwist g θ t ≠ 0 → |t|≤M := by
    intro t ht
    apply hgM t
    intro hz
    exact ht (by simp [JointLogSeparation.frequencyTwist_apply,hz])
  rw [globalFirstTruncatedSource_eq_bins p hp hcop hg hinj hc hpr pool s hs w Ψ m
    (frequencyTwist g θ) W K ell B F M H hK hell hB hF hH htw side hb₁ hb₂]
  apply (norm_sum_le _ _).trans
  unfold globalChildBudget
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j)]
  apply htrans p hp hcop hg hinj hc hpr θ θ K ell B F source side j pool Ψ m
    (fun x => w x.first) Γ hK hell hB hF hΓ
  · intro x hx
    exact hw x.first ((mem_globalFirstExpansionPool pool s cutoff x).mp (Finset.mem_filter.mp hx).1).1
  · exact hΨ
  · exact fun x hx => globalFirstSupportedPool_admissible p pool s hs cutoff ell M side x hx
  · exact fun x hx => globalFirstSupportedPool_frequency_ne_zero p pool s
      (globalFirstConcreteCutoff p K ell B F M H side) ell M side x hx

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem globalFirstCoreRows_actual_transfer
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0≤C ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℝ) (Γ K ell B F H : ℝ)
      (Ψ : O →* ℂ) (m : O) (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
      (T : GlobalFirstData ι → Finset O),
      0≤Γ → (∀ b∈s,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side b) →
      (∀ b∈s,∀ z∈T b,z≠0) →
      let cutoff := globalFirstConcreteCutoff p K ell B F M H side
      let source := globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side
      let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
      let Ψmode := firstCoreTwist side χ Ψ r
      let profile := firstCoreModeProfile g V side t
      (∑ b∈s,weight b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
        globalFirstCoreCorrection p g V ell side t b)) ≤
      globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε t t K ell B F M H A J side +
      ‖globalFirstSourceZero p hg pool s (fun b => weight b) cutoff Ψmode m profile rowMajorant ell side
        (globalFirstPooledRow p K ell B F side)‖ +
      ‖globalFirstSourceTail p hp hg hinj pool s (fun b => weight b) cutoff Ψmode m profile rowMajorant ell side
        (globalFirstPooledRow p K ell B F side)‖ := by
  have hbase : ∀ x,firstCoreBaseProfile g V side x≠0 → |x|≤M := by
    intro x hx
    apply hgM x
    intro hz
    exact hx (by rw [firstCoreBaseProfile_apply,hz,zero_mul])
  obtain ⟨windows,C,hC,hwc,hws,hwb,htrans⟩ := globalFirstTruncatedSource_actual_transfer
    ε hε (firstCoreBaseProfile g V side) rowMajorant M hM hbase A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ K ell B F H Ψ m χ r t T hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂ hT hT0
  dsimp only
  let cutoff := globalFirstConcreteCutoff p K ell B F M H side
  let source := globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side
  let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
  let Ψmode := firstCoreTwist side χ Ψ r
  have hweight : ∀ b∈s,0≤weight b := by
    intro b hb
    exact mul_nonneg (hw b hb).1 (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hY : ∀ b∈s,0<globalFirstPooledRow p K ell B F side b := by
    intro b hb
    exact globalPooledRowScale_pos K ell B F hK hell hB hF _
  have hsource := htrans p hp hcop hg hinj hc hpr pool s (fun b => (w b : ℂ)) Γ
    (firstCoreModeHeight side t) K ell B F H side Ψmode m hΓ
    (fun b hb => by rw [Complex.norm_real,Real.norm_of_nonneg (hw b hb).1]; exact (hw b hb).2)
    hK hell hB hF hH hs (fun a => (firstCoreTwist_norm_le side χ Ψ r a).trans (hΨ a)) hb₁ hb₂
  have hfinite := globalFirstCoreRows_finite_le_sources p hp hg hinj hc pool s weight hweight cutoff Ψ m g V ell hell
    side χ r t (globalFirstPooledRow p K ell B F side) hY T hT hT0
  have hheight : ‖firstCoreModeHeight side t‖=‖t‖ := by cases side <;> simp [firstCoreModeHeight]
  have hbudget : globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε
      (firstCoreModeHeight side t) (firstCoreModeHeight side t) K ell B F M H A J side =
      globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε t t K ell B F M H A J side := by
    simp only [globalChildBudget,globalDescentWeight,hheight]
  dsimp only at hsource
  change _ ≤ globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε
    (firstCoreModeHeight side t) (firstCoreModeHeight side t) K ell B F M H A J side at hsource
  rw [hbudget] at hsource
  apply hfinite.trans
  apply add_le_add
  · apply add_le_add
    · simpa only [weight,firstCoreModeProfile,Complex.ofReal_mul] using hsource
    · exact le_rfl
  · exact le_rfl

end SecondPassArithmetic

open scoped BigOperators Classical
namespace InitialMeanSquare

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

structure Datum where
  divisor : Ideal O
  shared : Ideal O
  frequency : O
  deriving DecidableEq

def newRow (x : Datum) : O := idealGenerator x.divisor*x.frequency
def newLabel (x : Datum) : Ideal O := x.divisor*x.shared
def oldCommon (b : Ideal O) (x : Datum) : Ideal O := b*x.divisor
def observation (x : Datum) : O × Ideal O := (newRow x,newLabel x)

theorem span_newRow (x : Datum) :
    Ideal.span {newRow x}=x.divisor*Ideal.span {x.frequency} := by
  rw [newRow,←Ideal.span_singleton_mul_span_singleton,span_idealGenerator]

theorem divisor_dvd_row (x : Datum) : x.divisor∣Ideal.span {newRow x} := by
  rw [span_newRow]
  exact dvd_mul_right _ _

theorem divisor_dvd_label (x : Datum) : x.divisor∣newLabel x := dvd_mul_right _ _

theorem divisor_ne_zero_of_row (x : Datum) (hx : newRow x≠0) : x.divisor≠0 := by
  intro hd
  have hs : Ideal.span {newRow x}=(0 : Ideal O) := by rw [span_newRow,hd,zero_mul]
  exact hx (Ideal.span_singleton_eq_bot.mp hs)

theorem divisor_injective_on_fiber (y : O) (f : Ideal O) (hy : y≠0) :
    Set.InjOn Datum.divisor {x : Datum | observation x=(y,f)} := by
  intro x hx z hz hd
  have hxrow : newRow x=y := congrArg Prod.fst hx
  have hzrow : newRow z=y := congrArg Prod.fst hz
  have hxlabel : newLabel x=f := congrArg Prod.snd hx
  have hzlabel : newLabel z=f := congrArg Prod.snd hz
  have hdx := divisor_ne_zero_of_row x (by rwa [hxrow])
  have hshared : x.shared=z.shared := by
    apply mul_left_cancel₀ hdx
    calc
      x.divisor*x.shared = f := hxlabel
      _ = z.divisor*z.shared := hzlabel.symm
      _ = x.divisor*z.shared := by rw [hd]
  have hfreq : x.frequency=z.frequency := by
    apply mul_left_cancel₀ (idealGenerator_ne_zero x.divisor hdx)
    calc
      idealGenerator x.divisor*x.frequency = y := hxrow
      _ = idealGenerator z.divisor*z.frequency := hzrow.symm
      _ = idealGenerator x.divisor*z.frequency := by rw [hd]
  cases x
  cases z
  simp_all

theorem fiber_card_le (s : Finset Datum) (y : O) (f : Ideal O) (hy : y≠0) :
    (s.filter (fun x => observation x=(y,f))).card≤(idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by
    intro hz
    exact hy (Ideal.span_singleton_eq_bot.mp hz)
  apply Finset.card_le_card_of_injOn Datum.divisor
  · intro x hx
    change x.divisor∈idealDivisors (Ideal.span {y})
    rw [mem_idealDivisors hyI]
    have he : newRow x=y := congrArg Prod.fst (Finset.mem_filter.mp hx).2
    rw [←he]
    exact divisor_dvd_row x
  · intro x hx z hz he
    exact divisor_injective_on_fiber y f hy (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hz).2 he

theorem fiber_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (s : Finset Datum) (y : O) (f : Ideal O), y≠0 →
      ((s.filter (fun x => observation x=(y,f))).card:ℝ)≤
        C*(Ideal.absNorm (Ideal.span {y}):ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s y f hy
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by
    intro hz
    exact hy (Ideal.span_singleton_eq_bot.mp hz)
  exact (show ((s.filter (fun x => observation x=(y,f))).card:ℝ)≤
    (idealDivisors (Ideal.span {y})).card by exact_mod_cast fiber_card_le s y f hy).trans (hdiv _ hyI)

theorem weighted_energy_pushforward (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (s : Finset Datum) (t : Finset (O×Ideal O))
      (w : Datum→ℂ) (P : O×Ideal O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,observation x∈t) →
      (∀y∈t,y.1≠0) → (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      (∑x∈s,‖w x‖*‖P (observation x)‖^2)≤A*C*K^ε*∑y∈t,‖P y‖^2 := by
  obtain ⟨C,hC,hfiber⟩ := fiber_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s t w P A K hA hK hmap ht hnorm hw
  apply (DescentWeightedCauchy.bounded_energy_pushforward s t observation w P A hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hc := (hfiber s y.1 y.2 (ht y hy)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm y hy) hε.le) hC.le)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hA) (sq_nonneg ‖P y‖)
  simpa only [Prod.eta,mul_assoc] using hh

theorem norm_newRow (x : Datum) :
    Ideal.absNorm (Ideal.span {newRow x})=Ideal.absNorm x.divisor*Ideal.absNorm (Ideal.span {x.frequency}) := by
  rw [span_newRow,map_mul]

theorem norm_newLabel (x : Datum) :
    Ideal.absNorm (newLabel x)=Ideal.absNorm x.divisor*Ideal.absNorm x.shared := by
  rw [newLabel,map_mul]

theorem norm_oldCommon (b : Ideal O) (x : Datum) :
    Ideal.absNorm (oldCommon b x)=Ideal.absNorm b*Ideal.absNorm x.divisor := by
  rw [oldCommon,map_mul]

end

theorem label_and_mask (b : Ideal O) (x : Datum)
    (hC : Squarefree (oldCommon b x)) (hs : Squarefree x.shared)
    (hcop : IsCoprime (oldCommon b x) x.shared) :
    Squarefree (newLabel x) ∧ IsCoprime b (newLabel x) := by
  have hC' : Squarefree (b*x.divisor) := hC
  have hcop' : IsCoprime (b*x.divisor) x.shared := hcop
  have hds : IsCoprime x.divisor x.shared :=
    hcop'.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
  have hbs : IsCoprime b x.shared :=
    hcop'.of_isCoprime_of_dvd_left (dvd_mul_right _ _)
  have hbd : IsCoprime b x.divisor := by
    apply Ideal.isCoprime_iff_gcd.mpr
    have hh := (IsRelPrime.of_squarefree_mul hC')
      (GCDMonoid.gcd_dvd_left b x.divisor) (GCDMonoid.gcd_dvd_right b x.divisor)
    simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp hh
  exact ⟨squarefree_mul_iff.mpr ⟨hds.isRelPrime,hC'.of_mul_right,hs⟩,hbd.mul_right hbs⟩

def columnScale (Z B F : ℝ) : ℝ := Z/(B*F)
def rowScale (Z H B : ℝ) : ℝ := Z^2/(H*B^2)

theorem initial_prefactor (Z H b d : ℝ) (hd : d≠0) :
    H*(b*d)/(Z^2*d)=H*b/Z^2 := by field_simp

theorem initial_column_scale (Z b d s : ℝ) :
    Z/((b*d)*s)=columnScale Z b (d*s) := by unfold columnScale; ring

theorem initial_row_bound (Z H b d h : ℝ) (hH : 0<H) (hb : 0<b) (hd : 0<d)
    (hh : h≤Z^2*d/(H*(b*d)^2)) : d*h≤rowScale Z H b := by
  have h := mul_le_mul_of_nonneg_left hh hd.le
  have he : d*(Z^2*d/(H*(b*d)^2))=rowScale Z H b := by
    unfold rowScale
    field_simp

  exact h.trans_eq he

theorem initial_mass (Z B F : ℝ) (hF : F≠0) : columnScale Z B F*F=Z/B := by
  unfold columnScale
  field_simp

theorem initial_invariant_identity (Z H B F R : ℝ)
    (hZ : Z≠0) (hB : B≠0) (hF : F≠0) :
    rowScale Z H B*R/(columnScale Z B F*F)=(Z/H)*(R/B) := by
  unfold rowScale columnScale
  field_simp

theorem initial_invariant_bound (Z H B F R c : ℝ)
    (hZ : 0<Z) (hH : 0<H) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) :
    rowScale Z H B*R/(columnScale Z B F*F)≤c*(Z/H) := by
  rw [initial_invariant_identity Z H B F R hZ.ne' hB.ne' hF.ne']
  have hh : R/B≤c := (div_le_iff₀ hB).mpr hR
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (div_nonneg hZ.le hH.le)

theorem initial_invariant_power_general (Z B F R c σ : ℝ)
    (hZ : 0<Z) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) :
    rowScale Z (Z^(1+σ)) B*R/(columnScale Z B F*F)≤c*Z^(-σ) := by
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    calc
      _ = Z^((1:ℝ)-(1+σ)) := by rw [Real.rpow_sub hZ,Real.rpow_one]
      _ = _ := by congr 1; ring
  simpa only [he] using initial_invariant_bound Z (Z^(1+σ)) B F R c
    hZ (Real.rpow_pos_of_pos hZ _) hB hF hR

theorem initial_invariant_power (Z B F R c : ℝ)
    (hZ : 1≤Z) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) :
    rowScale Z (Z^((11:ℝ)/10)) B*R/(columnScale Z B F*F)≤c*Z^(-(1:ℝ)/10) := by
  have hZ0 : 0<Z := by linarith
  have he : Z/(Z^((11:ℝ)/10))=Z^(-(1:ℝ)/10) := by
    calc
      _ = Z^((1:ℝ)-(11:ℝ)/10) := by rw [Real.rpow_sub hZ0,Real.rpow_one]
      _ = _ := by norm_num
  simpa only [he] using initial_invariant_bound Z (Z^((11:ℝ)/10)) B F R c
    hZ0 (Real.rpow_pos_of_pos hZ0 _) hB hF hR

theorem initial_invariant_reserved_margin (Z B F R c : ℝ)
    (hZ : 1≤Z) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) (hc : c≤Z^((1:ℝ)/20)) :
    rowScale Z (Z^((11:ℝ)/10)) B*R≤
      columnScale Z B F*F*Z^(-(1:ℝ)/20) := by
  have hZ0 : 0<Z := by linarith
  have hmass : 0<columnScale Z B F*F := by unfold columnScale; positivity
  rw [mul_comm (columnScale Z B F*F)]
  apply (div_le_iff₀ hmass).mp
  apply (initial_invariant_power Z B F R c hZ hB hF hR).trans
  calc
    c*Z^(-(1:ℝ)/10) ≤ Z^((1:ℝ)/20)*Z^(-(1:ℝ)/10) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hZ0.le _)
    _ = Z^(-(1:ℝ)/20) := by rw [←Real.rpow_add hZ0]; norm_num

theorem initial_budget_identity (Z H B : ℝ) (hZ : Z≠0) (hB : B≠0) :
    (H*B/Z^2)*B*(Z/B)*(Z/B)=H := by field_simp

end InitialMeanSquare

end

end OAI
