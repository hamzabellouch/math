import OAI.NumberTheory.DirichletL.GaussSum.FixedRayFibers

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

namespace CubicEisenstein

section
open scoped BigOperators Classical ContDiff MatrixGroups

open ActualEisensteinCubic CompletedGauss CompletedDyadic CubicKubota CubicJacobiGlobal ConcreteTraceCRT
open LocalReflectionBrackets ShortDraftCusp
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

lemma stratum_model_coefficient (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (m:ℕ) (I J:Ideal Eis) :
    G.shape.amplitude u m I J*
      (star D.fixedFactor*A4BadPhase G.c0 G.denominator_ne_zero (D.matrix (fun _=>1) 1 1) D.U
        (G.dualNumerator u m I J))*D.bracketProduct hp hg j (G.dualNumerator u m I J)=
    D.modelRowPhase G.shape hp hg j u m*
      ∑e:ι→Fin 3,G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u m I J*
        reflectedBranch (fun i=>Ideal.span {p i}) hg j e (primaryGenerator I) (primaryGenerator J) :=
  D.model_coefficient G.shape hp G.denominator_ne_zero hg j u m I J

theorem reflectedValue_eq_model_series (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) :
    D.reflectedValue G.shape hp G.denominator_ne_zero hg j W X=
    fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
      ∑'t:ThetaFullIndex,
        (D.modelRowPhase G.shape hp hg j t.1 t.2.1*
          ∑e:ι→Fin 3,
            G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U))
              t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
            reflectedBranch (fun i=>Ideal.span {p i}) hg j e
              (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
          ((ramifiedScale 1 completedRamifiedStep t.2.1*
            Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)*
        CubicReflectionKernel.paperKernel (Vstar W)
          ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
            (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3) := by
  unfold ControlledStratumArithmetic.reflectedValue
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro t
  rw [fixed_stratum_kernel_scale]
  have he:=G.stratum_model_coefficient D hp hg j t.1 t.2.1 t.2.2.1.val t.2.2.2.val
  have hx:sourceCuspPhaseNumerator G.shape.index (G.shape.upper 0 0) (thetaFullFrequency t)=
      G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  rw [hx]
  let denominator:ℂ:=((ramifiedScale 1 completedRamifiedStep t.2.1*
    Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)
  let kernel:ℂ:=CubicReflectionKernel.paperKernel (Vstar W)
    ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
      (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)
  change _/denominator*kernel*_=_/denominator*kernel
  calc
    _=(G.shape.amplitude t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      (star D.fixedFactor*A4BadPhase G.c0 G.denominator_ne_zero (D.matrix (fun _=>1) 1 1) D.U
        (G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val))*
      D.bracketProduct hp hg j (G.dualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val))/denominator*kernel := by ring
    _=_:=by rw [he]

end FixedFourierGeometry
end

open ActualEisensteinCubic CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

abbrev CuspIdealIndex := Eisˣ×ℕ×NonzeroDualIdeal×NonzeroDualIdeal

def thetaFullToIdealIndex (t:ThetaFullIndex) : CuspIdealIndex :=
  (t.1,t.2.1,primaryCubePairToMellinIndex t.2.2)

lemma thetaFullToIdealIndex_injective : Function.Injective thetaFullToIdealIndex := by
  intro t v h
  apply Prod.ext
  · exact congrArg (fun x:CuspIdealIndex=>x.1) h
  · apply Prod.ext
    · exact congrArg (fun x:CuspIdealIndex=>x.2.1) h
    · apply primaryCubePairToMellinIndex_injective
      exact congrArg (fun x:CuspIdealIndex=>x.2.2) h

lemma fixedCuspArrayWithPhase_eligible (j:Fin 3) (u:Eisˣ)
    (φ:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (I J:Ideal Eis)
    (h:fixedCuspArrayWithPhase j u φ m I J≠0) : fixedCuspArrayEligible I J := by
  by_contra he
  exact h (fixedCuspArrayWithPhase_zero j u φ m I J he)

theorem fixedCuspArrayWithPhase_tsum_primary_pairs (j:Fin 3) (u:Eisˣ)
    (φ:ℕ→Ideal Eis→Ideal Eis→ℂ) (m:ℕ) (w:CompletedMellinIndex→ℂ) :
    (∑'t:CompletedMellinIndex,fixedCuspArrayWithPhase j u φ m t.1.val t.2.val*w t)=
    ∑'t:ThetaPrimaryCubePair,fixedCuspArrayWithPhase j u φ m t.1.val t.2.val*
      w (primaryCubePairToMellinIndex t) := by
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun t=>primaryCubePairToMellinIndex t.val)
  · exact primaryCubePairToMellinIndex_injective.comp Subtype.val_injective
  · intro t ht
    change fixedCuspArrayWithPhase j u φ m t.1.val t.2.val*w t≠0 at ht
    have ha:fixedCuspArrayWithPhase j u φ m t.1.val t.2.val≠0:=by
      intro hz
      exact ht (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=fixedCuspArrayWithPhase_eligible j u φ m t.1.val t.2.val ha
    let v:ThetaPrimaryCubePair:=(⟨t.1.val,hs,hI⟩,⟨t.2.val,hJ⟩)
    have hv:primaryCubePairToMellinIndex v=t:=Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
    refine ⟨⟨v,?_⟩,hv⟩
    change fixedCuspArrayWithPhase j u φ m (primaryCubePairToMellinIndex v).1.val
      (primaryCubePairToMellinIndex v).2.val*w (primaryCubePairToMellinIndex v)≠0
    rwa [hv]
  · intro t
    rfl

theorem fixedCuspArrayWithPhase_tsum_full_index
    (j:Eisˣ→Fin 3) (φ:Eisˣ→ℕ→Ideal Eis→Ideal Eis→ℂ) (w:CuspIdealIndex→ℂ) :
    (∑'t:CuspIdealIndex,fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1)
      t.2.1 t.2.2.1.val t.2.2.2.val*w t)=
    ∑'t:ThetaFullIndex,fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1)
      t.2.1 t.2.2.1.val t.2.2.2.val*w (thetaFullToIdealIndex t) := by
  apply tsum_eq_tsum_of_ne_zero_bij (fun t=>thetaFullToIdealIndex t.val)
  · exact thetaFullToIdealIndex_injective.comp Subtype.val_injective
  · intro t ht
    change fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1) t.2.1 t.2.2.1.val t.2.2.2.val*w t≠0 at ht
    have ha:fixedCuspArrayWithPhase (j t.1) t.1 (φ t.1) t.2.1 t.2.2.1.val t.2.2.2.val≠0:=by
      intro hz
      exact ht (by rw [hz,zero_mul])
    obtain ⟨hs,hI,hJ⟩:=fixedCuspArrayWithPhase_eligible _ _ _ _ _ _ ha
    let v:ThetaFullIndex:=(t.1,t.2.1,⟨t.2.2.1.val,hs,hI⟩,⟨t.2.2.2.val,hJ⟩)
    have hv:thetaFullToIdealIndex v=t:=
      Prod.ext rfl (Prod.ext rfl (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)))
    refine ⟨⟨v,?_⟩,hv⟩
    change fixedCuspArrayWithPhase (j (thetaFullToIdealIndex v).1) (thetaFullToIdealIndex v).1
      (φ (thetaFullToIdealIndex v).1) (thetaFullToIdealIndex v).2.1
      (thetaFullToIdealIndex v).2.2.1.val (thetaFullToIdealIndex v).2.2.2.val*
      w (thetaFullToIdealIndex v)≠0
    rwa [hv]
  · intro t
    rfl

end CubicEisenstein

open scoped Classical BigOperators

namespace CompletedGauss
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def mandatoryActiveEquiv (R:Finset ι) :
    {A:Finset ι // R⊆A}≃Finset {i:ι // i∉R} where
  toFun A:=A.val.subtype (fun i=>i∉R)
  invFun B:=⟨R∪B.image Subtype.val,Finset.subset_union_left⟩
  left_inv A:=by
    apply Subtype.ext
    ext i
    simp only [Finset.mem_union,Finset.mem_image,Finset.mem_subtype]
    constructor
    · rintro (hi|⟨j,hj,rfl⟩)
      · exact A.property hi
      · exact hj
    · intro hi
      by_cases hr:i∈R
      · exact Or.inl hr
      · exact Or.inr ⟨⟨i,hr⟩,hi,rfl⟩
  right_inv B:=by
    ext i
    simp only [Finset.mem_subtype,Finset.mem_union,Finset.mem_image]
    constructor
    · rintro (hi|⟨j,hj,hji⟩)
      · exact False.elim (i.property hi)
      · have he:j=i:=Subtype.ext hji
        simpa only [he] using hj
    · intro hi
      exact Or.inr ⟨i,hi,rfl⟩

lemma sum_mandatory_active {V:Type*} [AddCommMonoid V]
    (R:Finset ι) (F:Finset ι→V) (hz:∀A,¬R⊆A→F A=0) :
    (∑A:Finset ι,F A)=
      ∑B:Finset {i:ι // i∉R},F (R∪B.image Subtype.val) := by
  calc
    _=∑A:Finset ι,if R⊆A then F A else 0:=by
      apply Finset.sum_congr rfl
      intro A hA
      by_cases h:R⊆A
      · simp only [ite_eq_left h]
      · simp only [ite_eq_right h,hz A h]
    _=∑A:{A:Finset ι // R⊆A},F A.val:=by
      rw [←Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (fun A:Finset ι=>R⊆A)) (by simp) F
    _=_:=by
      apply Fintype.sum_equiv (mandatoryActiveEquiv R)
      intro A
      exact congrArg F (congrArg Subtype.val ((mandatoryActiveEquiv R).left_inv A)).symm

theorem inactive_weight_mandatory_active (R:Finset ι) (z:ι→ℂ)
    (hz:∀i∈R,z i=0) (F:Finset ι→ℂ) :
    (∑A:Finset ι,(∏i∈(Finset.univ:Finset ι)\A,z i)*F A)=
      ∑B:Finset {i:ι // i∉R},
        (∏i∈(Finset.univ:Finset ι)\(R∪B.image Subtype.val),z i)*
          F (R∪B.image Subtype.val) := by
  apply sum_mandatory_active R
  intro A hA
  have hex:∃i∈R,i∉A:=by
    by_contra! hn
    exact hA hn
  obtain ⟨i,hi,hni⟩:=hex
  have hm:i∈(Finset.univ:Finset ι)\A:=by simp [hni]
  rw [Finset.prod_eq_zero hm (hz i hi),zero_mul]

lemma inactive_product_complement (R:Finset ι) (z:ι→ℂ)
    (B:Finset {i:ι // i∉R}) :
    (∏i∈(Finset.univ:Finset ι)\(R∪B.image Subtype.val),z i)=
      ∏i∈(Finset.univ:Finset {i:ι // i∉R})\B,z i.val := by
  symm
  apply Finset.prod_bij (fun i _=>i.val)
  · intro i hi
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and] at hi ⊢
    intro hmem
    rcases Finset.mem_union.mp hmem with hr|hb
    · exact i.property hr
    · obtain ⟨j,hj,hji⟩:=Finset.mem_image.mp hb
      exact hi ((Subtype.ext hji) ▸ hj)
  · intro i hi j hj he
    exact Subtype.ext he
  · intro i hi
    have hnot:i∉R∪B.image Subtype.val:=(Finset.mem_sdiff.mp hi).2
    have hr:i∉R:=fun h=>hnot (Finset.mem_union_left _ h)
    refine ⟨⟨i,hr⟩,?_,rfl⟩
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
    intro hb
    exact hnot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨i,hr⟩,hb,rfl⟩))
  · intro i hi
    rfl

theorem inactive_weight_optional_active (R:Finset ι) (z:ι→ℂ)
    (hz:∀i∈R,z i=0) (F:Finset ι→ℂ) :
    (∑A:Finset ι,(∏i∈(Finset.univ:Finset ι)\A,z i)*F A)=
      ∑B:Finset {i:ι // i∉R},
        (∏i∈(Finset.univ:Finset {i:ι // i∉R})\B,z i.val)*
          F (R∪B.image Subtype.val) := by
  rw [inactive_weight_mandatory_active R z hz F]
  apply Finset.sum_congr rfl
  intro B hB
  rw [inactive_product_complement]

end CompletedGauss

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
local notation "Eis" => ActualEisensteinCubic.O

lemma excluded_prime_dvd_row_mask (q:ℕ) (m:Eis) (F P:Ideal Eis)
    (hP:P∈reflectionExcludedPrimes q) :
    P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F := by
  apply dvd_mul_of_dvd_left
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_le.mpr
  exact Set.singleton_subset_iff.mpr (P.mul_mem_left m (excludedGenerator_mem _ hP))

lemma residual_prime_not_excluded (q:ℕ) (m:Eis) (F I P:Ideal Eis) (hP:Prime P)
    (hres:P∣rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) :
    P∉reflectionExcludedPrimes q := by
  intro hmem
  have hn:¬P∣Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F:=
    ((prime_dvd_rowResidualPart_iff _ _ P hP).mp hres).2
  exact hn (excluded_prime_dvd_row_mask q m F P hmem)

lemma residual_coprime_fixed_conductor (q:ℕ) (hq:q≠0) (m:Eis) (F I:Ideal Eis) :
    IsCoprime (Ideal.span {reflectionConductor q})
      (rowResidualPart I (Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F)) := by
  let Q:=Ideal.span {m*excludedGenerator (reflectionExcludedPrimes q)}*F
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))
    (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp
  apply Finset.disjoint_left.mpr
  intro P hfixed hres
  have hp:Prime P:=support_prime hfixed
  have hd:P∣Ideal.span {reflectionConductor q}:=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hfixed)
  have hr:P∣rowResidualPart I Q:=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hres)
  exact residual_prime_not_excluded q m F I P hp hr (reflectionConductor_prime_mem q hq P hp hd)

end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def representativeRowFiber (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) : Finset (Ideal Eis) :=
  completedRowFiber rows Q (rowPowerfulPart I) (rowMaskPart I Q)

def reconstructFiberRow (I Q k:Ideal Eis) : Ideal Eis :=
  rowPowerfulPart I*rowMaskPart I Q*k

lemma reconstructFiberRow_ne_zero (I Q k:Ideal Eis) (hk:k≠0) : reconstructFiberRow I Q k≠0 :=
  mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) hk

lemma reconstructFiberRow_of_original (rows:Finset (Ideal Eis)) (I Q J:Ideal Eis)
    (hJ:J∈representativeRowFiber rows I Q) (hJ0:J≠0) :
    reconstructFiberRow I Q (rowResidualPart J Q)=J := by
  obtain ⟨_,hA,hT⟩:=Finset.mem_filter.mp hJ
  rw [reconstructFiberRow,←hA,←hT]
  exact row_powerful_mask_residual_product J Q hJ0

lemma residual_reconstructFiberRow (rows:Finset (Ideal Eis)) (I Q k:Ideal Eis)
    (hk:k≠0) (hmem:reconstructFiberRow I Q k∈representativeRowFiber rows I Q) :
    rowResidualPart (reconstructFiberRow I Q k) Q=k := by
  have he:=reconstructFiberRow_of_original rows I Q _ hmem (reconstructFiberRow_ne_zero I Q k hk)
  exact mul_left_cancel₀ (mul_ne_zero (rowPowerfulPart_ne_zero I)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) he

lemma representativeRowFiber_injective (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (hrows:∀J∈rows,J≠0) :
    Set.InjOn (fun J=>rowResidualPart J Q) (representativeRowFiber rows I Q) :=
  rowResidualPart_injective_on_fiber rows Q (rowPowerfulPart I) (rowMaskPart I Q) hrows

def fiberResidualIndex (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J:representativeRowFiber rows I Q) : idealRange (completedResidualScale K I Q) :=
  ⟨rowResidualPart J.val Q,completedRowFiber_residual_range rows Q
    (rowPowerfulPart I) (rowMaskPart I Q) hbad K hrows J.val J.property⟩

lemma fiberResidualIndex_injective (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K) :
    Function.Injective (fiberResidualIndex rows I Q K hbad hrows) := by
  intro J lengthScale he
  apply Subtype.ext
  apply representativeRowFiber_injective rows I Q (fun J hJ=>(hrows J hJ).1) J.property lengthScale.property
  exact congrArg Subtype.val he

def extendFiberRowScalar {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) : ℂ :=
  if h:reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q then
    scalar a ⟨reconstructFiberRow I Q k.val,h⟩ else 0

lemma extendFiberRowScalar_norm_le_one {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (hscalar:∀a J,‖scalar a J‖≤1)
    (a:α) (k:idealRange (completedResidualScale K I Q)) :
    ‖extendFiberRowScalar rows I Q K scalar a k‖≤1 := by
  unfold extendFiberRowScalar
  split_ifs
  · exact hscalar _ _
  · simp

lemma extendFiberRowScalar_zero {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q))
    (hk:reconstructFiberRow I Q k.val∉representativeRowFiber rows I Q) :
    extendFiberRowScalar rows I Q K scalar a k=0 := by
  simp only [extendFiberRowScalar,dite_eq_right hk]

lemma extendFiberRowScalar_at_original {α:Type*} (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (J:representativeRowFiber rows I Q) :
    extendFiberRowScalar rows I Q K scalar a (fiberResidualIndex rows I Q K hbad hrows J)=scalar a J := by
  have hJ0:J.val≠0:=(hrows J.val (Finset.mem_filter.mp J.property).1).1
  have he:=reconstructFiberRow_of_original rows I Q J.val J.property hJ0
  simp only [extendFiberRowScalar,fiberResidualIndex,he,dite_eq_left J.property]

def extendSelectedFiberRowScalar {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (t:τ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) : ℂ :=
  extendFiberRowScalar rows I Q K (fun a J=>if selector a J=t then scalar a J else 0) a k

lemma extendSelectedFiberRowScalar_norm_le_one {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (hscalar:∀a J,‖scalar a J‖≤1)
    (t:τ) (a:α) (k:idealRange (completedResidualScale K I Q)) :
    ‖extendSelectedFiberRowScalar rows I Q K selector scalar t a k‖≤1 := by
  apply extendFiberRowScalar_norm_le_one
  intro a J
  split_ifs
  · exact hscalar a J
  · simp

lemma extendSelectedFiberRowScalar_at_original {α τ:Type*} [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (t:τ) (a:α)
    (J:representativeRowFiber rows I Q) :
    extendSelectedFiberRowScalar rows I Q K selector scalar t a
      (fiberResidualIndex rows I Q K hbad hrows J)=
        if selector a J=t then scalar a J else 0 :=
  extendFiberRowScalar_at_original rows I Q K hbad hrows _ a J

lemma sum_extendSelectedFiberRowScalar {α τ:Type*} [Fintype τ] [DecidableEq τ]
    (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (selector:α → representativeRowFiber rows I Q → τ)
    (scalar:α → representativeRowFiber rows I Q → ℂ) (a:α)
    (k:idealRange (completedResidualScale K I Q)) :
    (∑t:τ,extendSelectedFiberRowScalar rows I Q K selector scalar t a k)=
      extendFiberRowScalar rows I Q K scalar a k := by
  by_cases hk:reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q
  · simp [extendSelectedFiberRowScalar,extendFiberRowScalar,hk]
  · simp only [extendSelectedFiberRowScalar,extendFiberRowScalar,dite_eq_right hk,Finset.sum_const_zero]

end

open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

theorem reconstructFiberRow_valid_iff (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (k:idealRange (completedResidualScale K I Q)) :
    reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q ↔
      ∃J:representativeRowFiber rows I Q,fiberResidualIndex rows I Q K hbad hrows J=k := by
  constructor
  · intro hk
    refine ⟨⟨reconstructFiberRow I Q k.val,hk⟩,?_⟩
    apply Subtype.ext
    exact residual_reconstructFiberRow rows I Q k.val (mem_idealRange.mp k.property).1.1 hk
  · rintro ⟨J,rfl⟩
    have hJ0:J.val≠0:=(hrows J.val (Finset.mem_filter.mp J.property).1).1
    change reconstructFiberRow I Q (rowResidualPart J.val Q)∈representativeRowFiber rows I Q
    rw [reconstructFiberRow_of_original rows I Q J.val J.property hJ0]
    exact J.property

lemma representativeFiber_parts (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (J:representativeRowFiber rows I Q) :
    rowPowerfulPart J.val=rowPowerfulPart I ∧ rowMaskPart J.val Q=rowMaskPart I Q :=
  (Finset.mem_filter.mp J.property).2

lemma representativeFiber_pool (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q) :
    completedReflectionPool J.val Q=completedReflectionPool I Q := by
  have hs:=representativeFiber_parts rows I Q J
  exact completedReflectionPool_eq_on_fiber J.val I Q
    (hrows J.val (Finset.mem_filter.mp J.property).1) hI hQ hs.1 hs.2

lemma representativeFiber_filtered_pool (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q) (free:Ideal Eis → Prop) [DecidablePred free] :
    (completedReflectionPool J.val Q).filter free=(completedReflectionPool I Q).filter free := by
  rw [representativeFiber_pool rows I Q hI hQ hrows J]

lemma representativeFiber_exponent (rows:Finset (Ideal Eis)) (I F Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q) (P:completedReflectionPool I Q) :
    completedLocalExponent J.val F P.val=completedLocalExponent I F P.val := by
  have hs:=representativeFiber_parts rows I Q J
  exact (completedReflectionPool_exponent_eq I J.val F Q hI
    (hrows J.val (Finset.mem_filter.mp J.property).1) hQ hs.1.symm hs.2.symm P).symm

lemma representativeFiber_extractedDivisor {ι:Type*} [Fintype ι]
    (rows:Finset (Ideal Eis)) (I F Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q)
    (P:ι → Ideal Eis) (hP:∀i,P i∈completedReflectionPool I Q) (e:ι → Fin 3) (v:Fin 3) :
    reflectionExtractedDivisor P (fun i=>completedLocalExponent J.val F (P i)) e v=
      reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e v := by
  have he:(fun i=>completedLocalExponent J.val F (P i))=
      (fun i=>completedLocalExponent I F (P i)):=by
    funext i
    exact representativeFiber_exponent rows I F Q hI hQ hrows J ⟨P i,hP i⟩
  rw [he]

lemma representativeFiber_residualScale (rows:Finset (Ideal Eis)) (I Q:Ideal Eis)
    (J:representativeRowFiber rows I Q) (K:ℝ) :
    completedResidualScale K J.val Q=completedResidualScale K I Q := by
  have hs:=representativeFiber_parts rows I Q J
  exact completedResidualScale_eq_on_fiber K J.val I Q hs.1 hs.2

lemma representativeFiber_branchScale {ι:Type*} [Fintype ι]
    (rows:Finset (Ideal Eis)) (I F Q:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hrows:∀J∈rows,J≠0)
    (J:representativeRowFiber rows I Q)
    (P:ι → Ideal Eis) (hP:∀i,P i∈completedReflectionPool I Q) (e:ι → Fin 3) (K X:ℝ) :
    completedBranchScale K X J.val F Q P e=completedBranchScale K X I F Q P e := by
  have hs:=representativeFiber_parts rows I Q J
  exact (completedBranchScale_eq_on_fiber K X I J.val F Q hI
    (hrows J.val (Finset.mem_filter.mp J.property).1) hQ hs.1.symm hs.2.symm P hP e).symm

end CompletedGauss

open scoped Classical BigOperators

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

def fixedRayFiberFromRows (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1) :
    ReflectedFiberData (fixedReflectionRayCount c hc) (fixedCuspLevelBound c) K I F Q :=
  fixedRayFiber c hc I F Q Q0 hI hQ K (fun _=>1) (by intro x;simp)
    (fun x m=>extendFiberRowScalar rows I Q K scalar (x,m))
    (fun x m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar (x,m))

lemma fixedRayFiberFromRows_rowPhase (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J:representativeRowFiber rows I Q) (r:FixedReflectionRay c hc)
    (e:pool I Q Q0→Fin 6) (i:ℕ×ℕ×ℕ) :
    ((fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).branch
      (fixedReflectionRayEquiv c hc r,e)).rowPhase i
        (fiberResidualIndex rows I Q K hbad hrows J)=scalar ((r,e),i.1) J := by
  change extendFiberRowScalar rows I Q K scalar
    ((((fixedReflectionRayEquiv c hc).symm (fixedReflectionRayEquiv c hc r)),e),i.1)
    (fiberResidualIndex rows I Q K hbad hrows J)=_
  rw [Equiv.symm_apply_apply]
  exact extendFiberRowScalar_at_original rows I Q K hbad hrows scalar ((r,e),i.1) J

lemma fixedRayFiberFromRows_weight (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (r:FixedReflectionRay c hc) (e:pool I Q Q0→Fin 6) :
    (fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).weight
      (fixedReflectionRayEquiv c hc r,e)=reflectionSixInactiveWeight I F Q Q0 e := by
  change 1*reflectionSixInactiveWeight I F Q Q0 e=_
  exact one_mul _

end CompletedGauss.FreeReflection

end

end OAI
