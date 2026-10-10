import OAI.NumberTheory.DirichletL.CubicSieve.CubeBlocks

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

section
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open JointLogSeparation (halfNormalizationCLM)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (elementNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def residualScale (Z : ℝ) (x : SecondExpansionData ι) : ℝ :=
  Z/(elementNorm (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)*
    elementNorm (secondExpansionQuotient p x))

def sourceWeight (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
    (Z H : ℝ) (x : SecondExpansionData ι) : ℂ :=
  secondNormalizedExpansionWeight p hp hcop hg Ψ m 1 1 ray Z H x *
    (residualScale p Z x : ℂ)⁻¹

theorem sourceWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex) (Z H : ℝ) (x : SecondExpansionData ι)
    (hZ : 0<Z) (hH : 0≤H)
    (hΨG : ‖Ψ (∏i∈x.sourceCommon,p i)‖≤1) (hΨV : ‖Ψ (∏i∈x.overlap,p i)‖≤1) :
    ‖sourceWeight p hp hcop hg Ψ m ray Z H x‖≤
      H*elementNorm (secondExpansionQuotient p x)/Z^2*‖secondRayCoefficient ray‖ := by
  simpa only [sourceWeight,residualScale,elementNorm,secondExpansionScale,expansionSupportData] using
    secondNormalizedExpansionWeight_norm_le p hp hcop hg hinj hc ∅ ∅ Ψ m 1 1
      (secondExpansionQuotient p x) ray Z H hZ hH x hΨG hΨV

end

theorem initial_source_fixed_profiles
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hU₁ : ∀t,g₁ t≠0→U t=1) (hU₂ : ∀t,g₂ t≠0→U t=1)
    (hg₁ : ∀t,g₁ t≠0→|t|≤A) (hg₂ : ∀t,g₂ t≠0→|t|≤A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m : O) (ray : SecondRayIndex)
        (x : SecondExpansionData ι) (Z H E V₀ X₀ K : ℝ),
        x.divisor⊆x.sourceCommon → x.frequency≠0 →
        0<Z → 0<E → 0<V₀ → 0<X₀ → 0<K →
        let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
        let r := secondExpansionQuotient p x
        let X := residualScale p Z x
        let z := Real.log (primeProductNorm p x.overlap*X₀/X)
        let ue := Real.log (elementNorm e/E)
        let uv := Real.log (primeProductNorm p x.overlap/V₀)
        let kap := Real.log (elementNorm (e*x.frequency)/K)
        |z|≤B → |ue|≤B → |uv|≤B → |kap|≤B →
        secondExpansionSource p hp hcop hg F Ψ m 1 1 ray {x}
          (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
          (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H =
        sourceWeight p hp hcop hg Ψ m ray Z H x *
          postCommonSmoothPair p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
            (m*r) (e*∏i∈x.overlap,p i) (e*x.frequency) (-(e*x.frequency))
            A₁ A₂ W windows z 0 ue uv kap X₀ X₀ (H*K/(E^2*V₀^2*X₀^2)) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A B hA hB h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray x Z H E V₀ X₀ K hE hk hZ hEs hV hX₀ hK
  dsimp only
  intro hz hue huv hkap
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
  let r := secondExpansionQuotient p x
  have he : e≠0 := primeSubsetGenerator_ne_zero _ _
  have hq : secondMaskQuotient p x.divisor x.sourceCommon hE=r :=
    (secondExpansionQuotient_of_subset p x hE).symm
  have hr : r≠0 := by
    rw [←hq]
    intro hr0
    have hs := secondMaskQuotient_spec p x.divisor x.sourceCommon hE
    rw [hr0,mul_zero] at hs
    exact (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) hs
  have hX : 0<residualScale p Z x := div_pos hZ
    (mul_pos (SecondPassIntegration.elementNorm_pos e he) (SecondPassIntegration.elementNorm_pos r hr))
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.sourceCommon x.divisor hE F x.overlap Ψ Ψ m 1 1 x.frequency r ray
      (congrArg (fun a:O => Ideal.span {a}) hq) Z H hZ U hUc hUs g₁ g₂ W hU₁ hU₂
  dsimp only at hnorm
  have hnormone : elementNorm (1:O)=1 := by simp [elementNorm]
  have hid' := hid p hp hcop hg 1 E V₀ (residualScale p Z x) X₀ K H
    (by norm_num) hEs hV hX hX₀ hK F x.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      m r 1 1 e x.frequency one_ne_zero he hk hz
      (by simpa only [hnormone,div_one,Real.log_one,abs_zero] using hB) hue huv
      (by simpa only [one_mul] using hkap)
  simp only [one_mul,mul_neg,hnormone,div_one,Real.log_one] at hid'
  have hscale : Z/(‖eisEmbedding e‖^2*‖eisEmbedding r‖^2)=residualScale p Z x := rfl
  rw [hscale,hid'] at hnorm
  rw [hq] at hnorm
  have hgoal := congrArg (fun t:ℂ => ((H:ℂ)*secondSourceCommonCoefficient p hg Ψ m 1 1 x.sourceCommon x.divisor)*t) hnorm
  simp only [secondExpansionSource,Finset.sum_singleton,sourceWeight,
    secondNormalizedExpansionWeight,e,r,mul_assoc] at hgoal ⊢
  exact hgoal

end

open ActualEisensteinCubic SecondPassArithmetic IdealMobiusDivisorSum
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

def sourceElementData (x : SecondExpansionData ι) : ElementDatum where
  divisor := ∏i∈x.divisor,Ideal.span {p i}
  shared := ∏i∈x.overlap,p i
  frequency := x.frequency

def sourceObservation (x : SecondExpansionData ι) : O×O :=
  (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor*x.frequency,
   primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor*∏i∈x.overlap,p i)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceObservation_eq (x : SecondExpansionData ι) :
    sourceObservation p x=elementObservation idealGenerator (sourceElementData p x) := rfl

include hinj in

theorem sourceElementData_injective (r : O) :
    Set.InjOn (sourceElementData p) {x | InSecondQuotientSector p r x} := by
  intro x hx y hy heq
  have hE := congrArg ElementDatum.divisor heq
  have hV := congrArg ElementDatum.shared heq
  have hk := congrArg ElementDatum.frequency heq
  have he : x.divisor=y.divisor := FirstCauchyArithmetic.family_product_injective _ hinj hE
  have hv : x.overlap=y.overlap := by
    apply FirstCauchyArithmetic.family_product_injective _ hinj
    have hh := congrArg (fun a:O => Ideal.span {a}) hV
    simpa only [sourceElementData,FiniteGaussPhase.span_finset_prod] using hh
  apply expansionSupportData_injOn p hinj ∅ ∅ r hx hy
  exact SecondSupportData.ext rfl rfl he hv hk

include hinj in

theorem source_fiber_card_le (r : O) (s : Finset (SecondExpansionData ι))
    (hs : ∀x∈s,InSecondQuotientSector p r x) (y f : O) (hy : y≠0) :
    (s.filter (fun x => sourceObservation p x=(y,f))).card≤
      (idealDivisors (Ideal.span {y})).card := by
  have hmap : (s.filter (fun x => sourceObservation p x=(y,f))).card≤
      ((s.image (sourceElementData p)).filter (fun x => elementObservation idealGenerator x=(y,f))).card := by
    apply Finset.card_le_card_of_injOn (sourceElementData p)
    · intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hx).1,rfl⟩,?_⟩
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy he
      exact sourceElementData_injective p hinj r (hs x (Finset.mem_filter.mp hx).1)
        (hs y (Finset.mem_filter.mp hy).1) he
  exact hmap.trans (element_fiber_card_le idealGenerator span_idealGenerator _ y f hy)

end

theorem source_weighted_energy_pushforward (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (t : Finset (O×O))
      (w : SecondExpansionData ι→ℂ) (P : O×O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈t) → (∀y∈t,y.1≠0) →
      (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      (∑x∈s,‖w x‖*‖P (sourceObservation p x)‖^2)≤A*C*K^ε*∑y∈t,‖P y‖^2 := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p _ hinj r s t w P A K hA hK hs hmap ht hnorm hw
  apply (DescentWeightedCauchy.bounded_energy_pushforward s t (sourceObservation p) w P A hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hyI : (Ideal.span {y.1}:Ideal O)≠0 := by intro hz; exact ht y hy (Ideal.span_singleton_eq_bot.mp hz)
  have hcard : ((s.filter (fun x => sourceObservation p x=y)).card:ℝ)≤C*K^ε := by
    calc
      _ ≤ ((idealDivisors (Ideal.span {y.1})).card:ℝ) := by
        exact_mod_cast source_fiber_card_le p hinj r s hs y.1 y.2 (ht y hy)
      _ ≤ C*(Ideal.absNorm (Ideal.span {y.1}):ℝ)^ε := hdiv _ hyI
      _ ≤ C*K^ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm y hy) hε.le) hC.le
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hA) (sq_nonneg ‖P y‖)
  simpa only [mul_assoc] using hh

theorem source_weighted_cauchy (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (t : Finset (O×O))
      (w : SecondExpansionData ι→ℂ) (P Q : O×O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈t) → (∀y∈t,y.1≠0) →
      (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      ‖∑x∈s,w x*P (sourceObservation p x)*star (Q (sourceObservation p x))‖≤
        A*C*K^ε*Real.sqrt (∑y∈t,‖P y‖^2)*Real.sqrt (∑y∈t,‖Q y‖^2) := by
  obtain ⟨C,hC,hpool⟩ := source_weighted_energy_pushforward ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p _ hinj r s t w P Q A K hA hK hs hmap ht hnorm hw
  have hP := hpool p hinj r s t w P A K hA hK hs hmap ht hnorm hw
  have hQ := hpool p hinj r s t w Q A K hA hK hs hmap ht hnorm hw
  have hD : 0≤A*C*K^ε := by positivity
  apply (DescentWeightedCauchy.weighted_cauchy s w (fun x => P (sourceObservation p x))
    (fun x => Q (sourceObservation p x))).trans
  calc
    _ ≤ Real.sqrt (A*C*K^ε*∑y∈t,‖P y‖^2)*Real.sqrt (A*C*K^ε*∑y∈t,‖Q y‖^2) := by gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD,Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt (A*C*K^ε))^2*Real.sqrt (∑y∈t,‖P y‖^2)*Real.sqrt (∑y∈t,‖Q y‖^2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end InitialMeanSquare

namespace CubicEisenstein

section
open Filter MeasureTheory LineDeriv
open scoped BigOperators Classical Topology SchwartzMap LineDeriv

abbrev EuclideanL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)
abbrev EuclideanGradientL2 := PiLp 2 (fun _ : Fin 3 => EuclideanL2)
example : InnerProductSpace ℂ EuclideanGradientL2 := inferInstance
example : CompleteSpace EuclideanGradientL2 := inferInstance
abbrev EuclideanDistributions := TemperedDistribution EuclideanSpatial ℂ

def euclideanCoordinateVector (j : Fin 3) : EuclideanSpatial := WithLp.toLp 2 (Pi.single j 1)
def euclideanL2Distribution : EuclideanL2 →L[ℂ] EuclideanDistributions :=
  Lp.toTemperedDistributionCLM ℂ volume 2

lemma euclideanL2Distribution_injective : Function.Injective euclideanL2Distribution := by
  apply LinearMap.ker_eq_bot.mp
  exact Lp.ker_toTemperedDistributionCLM_eq_bot

def euclideanGradientEquations : EuclideanL2 × EuclideanGradientL2 →L[ℂ]
    (Fin 3 → EuclideanDistributions) :=
  ContinuousLinearMap.pi (fun j =>
    (lineDerivOpCLM ℂ EuclideanDistributions (euclideanCoordinateVector j)).comp
      (euclideanL2Distribution.comp (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2))-
    euclideanL2Distribution.comp ((PiLp.proj 2 (fun _ : Fin 3 => EuclideanL2) j).comp
      (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2)))

def euclideanWeakGradientGraph : Submodule ℂ (EuclideanL2 × EuclideanGradientL2) :=
  euclideanGradientEquations.ker

lemma mem_euclideanWeakGradientGraph (f : EuclideanL2) (g : EuclideanGradientL2) :
    (f,g)∈euclideanWeakGradientGraph ↔ ∀j,
      ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)=euclideanL2Distribution (g j) := by
  change (fun j => ∂_{euclideanCoordinateVector j} (euclideanL2Distribution f)-
    euclideanL2Distribution (g j))=0 ↔ _
  simp only [funext_iff,Pi.zero_apply,sub_eq_zero]

lemma euclideanWeakGradientGraph_unique (x : EuclideanL2 × EuclideanGradientL2)
    (hx : x∈euclideanWeakGradientGraph) (hzero : x.1=0) : x.2=0 := by
  have hh := (mem_euclideanWeakGradientGraph x.1 x.2).mp hx
  apply (WithLp.equiv 2 (Fin 3 → EuclideanL2)).injective
  funext j
  change x.2 j=(0:EuclideanL2)
  apply euclideanL2Distribution_injective
  simpa only [hzero,map_zero,lineDerivOp_zero,WithLp.ofLp_zero,Pi.zero_apply] using (hh j).symm

def euclideanWeakGradient : EuclideanL2 →ₗ.[ℂ] EuclideanGradientL2 :=
  euclideanWeakGradientGraph.toLinearPMap

lemma euclideanWeakGradient_graph : euclideanWeakGradient.graph=euclideanWeakGradientGraph :=
  Submodule.toLinearPMap_graph_eq _ euclideanWeakGradientGraph_unique

theorem euclideanWeakGradient_closed : euclideanWeakGradient.IsClosed := by
  rw [LinearPMap.IsClosed,euclideanWeakGradient_graph]
  exact euclideanGradientEquations.isClosed_ker

lemma schwartz_mem_euclideanWeakGradientGraph (f : 𝓢(EuclideanSpatial,ℂ)) :
    (f.toLp 2 volume,WithLp.toLp 2 (fun j => (∂_{euclideanCoordinateVector j} f).toLp 2 volume))∈euclideanWeakGradientGraph := by
  apply (mem_euclideanWeakGradientGraph _ _).mpr
  intro j
  dsimp only [euclideanL2Distribution]
  simp only [Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_toLp_eq]
  exact TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq («μ» := volume) f _

theorem euclideanWeakGradient_dense_domain : Dense (euclideanWeakGradient.domain : Set EuclideanL2) := by
  apply (SchwartzMap.denseRange_toLpCLM (E := EuclideanSpatial) (F := ℂ) (p := 2)
    («μ» := volume) (by norm_num)).mono
  rintro _ ⟨f,rfl⟩
  apply LinearPMap.mem_domain_of_mem_graph
  rw [euclideanWeakGradient_graph]
  exact schwartz_mem_euclideanWeakGradientGraph f

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology SchwartzMap LineDeriv

abbrev EuclideanH1Ambient := WithLp 2 (EuclideanL2 × EuclideanGradientL2)

def euclideanH1Submodule : Submodule ℂ EuclideanH1Ambient :=
  euclideanWeakGradientGraph.comap (WithLp.linearEquiv 2 ℂ (EuclideanL2 × EuclideanGradientL2)).toLinearMap

lemma euclideanH1Submodule_isClosed : IsClosed (euclideanH1Submodule : Set EuclideanH1Ambient) := by
  have hg : IsClosed (euclideanWeakGradientGraph : Set (EuclideanL2 × EuclideanGradientL2)) :=
    euclideanGradientEquations.isClosed_ker
  exact hg.preimage (WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).continuous

abbrev EuclideanH1 := euclideanH1Submodule

instance euclideanH1Complete : CompleteSpace EuclideanH1 :=
  euclideanH1Submodule_isClosed.completeSpace_coe
example : InnerProductSpace ℂ EuclideanH1 := inferInstance

def euclideanH1Embedding : EuclideanH1 →L[ℂ] EuclideanL2 :=
  (ContinuousLinearMap.fst ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

def euclideanH1Gradient : EuclideanH1 →L[ℂ] EuclideanGradientL2 :=
  (ContinuousLinearMap.snd ℂ EuclideanL2 EuclideanGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ EuclideanL2 EuclideanGradientL2).toContinuousLinearMap.comp
      euclideanH1Submodule.subtypeL)

lemma euclideanH1Embedding_eq_zero (u : EuclideanH1) (hu : euclideanH1Embedding u=0) : u=0 := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (EuclideanL2 × EuclideanGradientL2)).injective
  apply Prod.ext
  · exact hu
  · exact euclideanWeakGradientGraph_unique u.1.ofLp u.2 hu

lemma euclideanH1Embedding_injective : Function.Injective euclideanH1Embedding := by
  intro u v huv
  apply sub_eq_zero.mp
  apply euclideanH1Embedding_eq_zero
  rw [map_sub,huv,sub_self]

lemma euclideanH1Embedding_dense : DenseRange euclideanH1Embedding := by
  apply euclideanWeakGradient_dense_domain.mono
  intro f hf
  obtain ⟨g,hg⟩ := LinearPMap.mem_domain_iff.mp hf
  rw [euclideanWeakGradient_graph] at hg
  refine ⟨⟨WithLp.toLp 2 (f,g),hg⟩,?_⟩
  rfl

lemma euclideanH1_norm_sq (u : EuclideanH1) :
    ‖u‖^2=‖euclideanH1Embedding u‖^2+‖euclideanH1Gradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

end CubicEisenstein

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge

def normCharacter {q : ℕ} (χ : DirichletCharacter ℂ q) : O→*ℂ where
  toFun a := χ (Ideal.absNorm (Ideal.span {a}))
  map_one' := by simp
  map_mul' a b := by
    rw [←Ideal.span_singleton_mul_span_singleton]
    simp

lemma normCharacter_prod {ι : Type*} (p : ι→O) (S : Finset ι)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normCharacter χ (∏i∈S,p i)=χ (Ideal.absNorm (∏i∈S,Ideal.span {p i})) := by
  change χ (Ideal.absNorm (Ideal.span {∏i∈S,p i}))=_
  rw [FiniteGaussPhase.span_finset_prod]

lemma pool_support_product (F : Finset (Ideal O)) (S : Finset (primePool F)) :
    idealSupport F (∏i∈S,i.val)=S := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏i∈S,i.val)≠(0:Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  ext i
  rw [mem_idealSupport_iff,UniqueFactorizationMonoid.mem_normalizedFactors_iff hn]
  simp only [family_prime_dvd_product_iff _ Subtype.val_injective S i,hp,true_and]

theorem sum_selected_ideals (F : Finset (Ideal O)) (hF : ∀I∈F,Squarefree I)
    (a : Ideal O→ℂ) :
    (∑I∈F,a I)=∑S∈(Finset.univ:Finset (primePool F)).powerset,
      if (∏i∈S,i.val)∈F then a (∏i∈S,i.val) else 0 := by
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun S _ => ∏i∈S,i.val)
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · intro S hS T hT he
    exact family_product_injective (fun i:primePool F => i.val) Subtype.val_injective he
  · intro I hI
    refine ⟨idealSupport F I,?_,idealSupport_product_eq F hI (hF I hI)⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),?_⟩
    rwa [idealSupport_product_eq F hI (hF I hI)]
  · intro S hS
    rfl

def selectedIdealTest (F : Finset (Ideal O)) (W : ℕ→ℂ) (S : Finset (primePool F)) : ℂ :=
  if (∏i∈S,i.val)∈F then W (Ideal.absNorm (∏i∈S,i.val)) else 0

theorem idealRowSum_eq_mobiusRow (F : Finset (Ideal O)) (hF : ∀I∈F,Admissible I)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ→ℂ) (z : O) :
    let hFpos := fun I hI => (hF I hI).1
    let hFgood := fun I hI P hP => ((hF I hI).2.2 P hP).1
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowSum F hFpos hFgood χ W z=
      mobiusRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ (normCharacter χ) 1
        (selectedIdealTest F W) z := by
  dsimp only
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hP : (fun i:primePool F => Ideal.span {poolPrimary F i})=(fun i:primePool F => i.val) :=
    funext (poolPrimary_span F hF)
  unfold idealRowSum
  rw [sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  unfold mobiusRow
  apply Finset.sum_congr rfl
  intro S hS
  have ht := normCharacter_prod (poolPrimary F) S χ
  simp only [hP] at ht
  by_cases hs : (∏i∈S,i.val)∈F
  · rw [ite_eq_left hs]
    simp only [inputColumn,selectedIdealTest,ite_eq_left hs,mul_one,ht]
    have hm : rowCoprimeMask (fun i => Ideal.span {poolPrimary F i}) S 1=1 := by
      simp [rowCoprimeMask,Ideal.IsPrime.one_notMem]
    rw [hm,mul_one]
    simp only [supportMobius,hP,baseChangeWeight,idealSexticRow,pool_support_product]
    ring
  · rw [ite_eq_right hs]
    simp only [inputColumn,selectedIdealTest,ite_eq_right hs,mul_zero,zero_mul]

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def sourceChildEnergy (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) : ℝ :=
  ∑u∈T,‖fixedChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b testNegative)
    u.2 (if rowNegative then -u.1 else u.1)‖^2

def sourceEnergyMagnitude (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (testNegative rowNegative : Bool) : ℝ :=
  ∑u∈T,(rowMagnitude p hp hcop hg F Ψ m u.2 (if rowNegative then -u.1 else u.1)
    V X testNegative)^2

lemma sourceChildEnergy_le (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (tn rn : Bool) (a b : ℝ) :
    sourceChildEnergy p hp hcop hg F Ψ m T V X tn rn a b≤
      sourceEnergyMagnitude p hp hcop hg F Ψ m T V X tn rn := by
  unfold sourceChildEnergy sourceEnergyMagnitude
  apply Finset.sum_le_sum
  intro u hu
  exact pow_le_pow_left₀ (norm_nonneg _) (fixedRow_norm_le p hp hcop hg F Ψ m _ _ V X a b tn) 2

lemma sourceChildEnergy_continuous (F : Finset ι) (Ψ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V : ℝ→ℂ) (X : ℝ) (tn rn : Bool) (τ σ : Frequency→ℝ)
    (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun q => sourceChildEnergy p hp hcop hg F Ψ m T V X tn rn (τ q) (σ q)) := by
  unfold sourceChildEnergy
  apply continuous_finsetSum
  intro u hu
  exact (fixedRow_continuous p hp hcop hg F Ψ m _ _ V X tn τ σ hτ hσ).norm.pow 2

def sourceGeometricMean (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (T : Finset (O×O))
    (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℝ :=
  Real.sqrt (sourceChildEnergy p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2)*
    Real.sqrt (sourceChildEnergy p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2)

def sourceFixedMode (s : Finset (SecondExpansionData ι)) (w : Frequency→SecondExpansionData ι→ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℂ :=
  ∑x∈s,w q x*
    star (fixedChildRow p hp hcop hg F Ψ₁ m (fixedSecondTest p V₁ X₁ q.1 q.2.2 true)
      (sourceObservation p x).2 (sourceObservation p x).1)*
    fixedChildRow p hp hcop hg F Ψ₂ m (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false)
      (sourceObservation p x).2 (-(sourceObservation p x).1)

def integratedSourceMode (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (s : Finset (SecondExpansionData ι)) (w : Frequency→SecondExpansionData ι→ℂ)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ) : ℂ :=
  ∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)*
    sourceFixedMode p hp hcop hg s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ (t₁,t₂,t₃)

end

private theorem weighted_conjugate_pair_swap {α : Type*} (s : Finset α)
    (w P Q : α → ℂ) (B X Y : ℝ)
    (h : ‖∑ x ∈ s, w x * P x * star (Q x)‖ ≤ B * X * Y) :
    ‖∑ x ∈ s, w x * star (Q x) * P x‖ ≤ B * (Y * X) := by
  have he : (∑ x ∈ s, w x * star (Q x) * P x) =
      ∑ x ∈ s, w x * P x * star (Q x) := by
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [he]
  exact h.trans_eq (by ring)

theorem integrated_source_transfer (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (T : Finset (O×O))
      (w : Frequency→SecondExpansionData ι→ℂ) (A K : ℝ)
      (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m : O) (V₁ V₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
      (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈T) → (∀y∈T,y.1≠0) →
      (∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀q,∀x∈s,‖w q x‖≤A) → (∀x∈s,Continuous (fun q => w q x)) →
      ‖integratedSourceMode p hp hcop hg b₁ b₂ b₃ s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂‖≤
        A*C*K^ε*(∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖*
          sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨C,hC,hpointwise⟩ := source_weighted_cauchy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg hinj r s T w A K F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ b₁ b₂ b₃ hA hK hs hmap hT hnorm hw hwc
  let f := sourceFixedMode p hp hcop hg s w F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂
  let G := sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := sourceChildEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q:Frequency => q.1) (fun q:Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := sourceChildEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q:Frequency => q.2.1) (fun q:Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀q,0≤G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (sourceEnergyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false)*
    Real.sqrt (sourceEnergyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀q,G q≤M := by
    intro q
    dsimp [G,sourceGeometricMean,M]
    gcongr
    · exact sourceChildEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact sourceChildEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hf : Continuous f := by
    unfold f sourceFixedMode
    apply continuous_finsetSum
    intro x hx
    have h₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (sourceObservation p x).2 (sourceObservation p x).1 V₁ X₁ true
      (fun q:Frequency => q.1) (fun q:Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (sourceObservation p x).2 (-(sourceObservation p x).1) V₂ X₂ false
      (fun q:Frequency => q.2.1) (fun q:Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact ((hwc x hx).mul h₁.star).mul h₂
  have hpoint : ∀q,‖f q‖≤(A*C*K^ε)*G q := by
    intro q
    let P : O × O → ℂ := fun u => fixedChildRow p hp hcop hg F Ψ₂ m
      (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false) u.2 (-u.1)
    let Q : O × O → ℂ := fun u => fixedChildRow p hp hcop hg F Ψ₁ m
      (fixedSecondTest p V₁ X₁ q.1 q.2.2 true) u.2 u.1
    have hh := hpointwise p hinj r s T (w q) P Q
      A K hA hK hs hmap hT hnorm (hw q)
    have hh' := weighted_conjugate_pair_swap s (w q)
      (fun x => P (sourceObservation p x)) (fun x => Q (sourceObservation p x))
      (A*C*K^ε) _ _ hh
    simpa only [f,G,sourceFixedMode,sourceGeometricMean,sourceChildEnergy,P,Q,
      Bool.false_eq_true,ite_false,ite_true] using hh'
  exact triple_integral_bound b₁ b₂ b₃ f G hf hG hG0 (A*C*K^ε) M (by positivity) hM hpoint

end InitialMeanSquare

end

end OAI
