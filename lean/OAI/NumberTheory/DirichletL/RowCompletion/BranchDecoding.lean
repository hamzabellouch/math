import OAI.NumberTheory.DirichletL.RowCompletion.ReflectedFibers

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

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma initialOrbit_reflection_inputs {q:ℕ} (χ:DirichletCharacter ℂ q)
    (Ψ:Eis→*ℂ) (hΨ:IsBaseRayTwist (initialBase χ) Ψ) :
    FactorsModulo (fixedBaseConductor q) Ψ ∧ (∀n:Eis,‖Ψ n‖≤1) :=
  ⟨initialOrbit_factorsModulo χ Ψ hΨ,fun n=>hΨ.norm_le (initialBase_norm χ) n⟩

lemma canonicalLabel_squarefree {X:ℝ} (f:idealRange X) : Squarefree f.val :=
  (mem_idealRange.mp f.property).1.2.1

lemma canonicalLabel_generator_ne_zero {X:ℝ} (f:idealRange X) :
    ConcretePrimeRowBridge.idealGenerator f.val≠0 :=
  ConcretePrimeRowBridge.idealGenerator_ne_zero f.val (mem_idealRange.mp f.property).1.1

lemma unitRowFamily_actual {X:ℝ} (f:idealRange X) (Ψ:Eis→*ℂ) (q:ℕ) (m:Eis)
    (u:Eisˣ) (I:Ideal Eis) :
    CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator (reflectionExcludedPrimes q)) u f I=
      rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator f.val)
        (u.val*ConcretePrimeRowBridge.idealGenerator I) := rfl

theorem fixedShellModels_of_actual_fiber_identity
    (q:ℕ) (hq:q≠0) (χ:DirichletCharacter ℂ q) (scale:ℂ)
    [Fintype (Eis⧸Ideal.span {reflectionConductor q})]
    (hidentity:
      ∀(Ψ:Eis→*ℂ),FactorsModulo (fixedBaseConductor q) Ψ→
      ∀hΨnorm:(∀n:Eis,‖Ψ n‖≤1),∀(m:Eis)(hm:m≠0),
      ∀(F:Ideal Eis)(hF:Squarefree F)(u:Eisˣ),∀(W:ℝ→ℂ)(a b:ℝ),
      0<a→Function.support W⊆Set.Icc a b→ContDiff ℝ ∞ W→
      ∀(K X:ℝ),0<K→0<X→∀rows:Finset (Ideal Eis),
      ∀hrows:(∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K),
      ∀(R:Ideal Eis)(hR:R∈rows),∀J:ActualFiber.RowIndex q m rows R F,
        completedT (rowTwist Ψ (ActualFiber.maskElement q m)
          (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
        scale*(ActualFiber.reflectedFiber q hq m hm rows R F (hrows R hR).1 hF
          (fun I hI=>(hrows I hI).1) u K Ψ hΨnorm).idealValue W X 1 completedRamifiedStep
            (rowResidualPart J.val (ActualFiber.maskIdeal q m F))) :
    HasFixedShellModels (reflectionExcludedPrimes q) (initialBase χ)
      (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq)) scale
      1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) := by
  intro Ψ hΨ m hm Xlabel f u W a b ha hs hW K X hK hX rows hrows
  obtain ⟨hperiod,hnorm⟩:=initialOrbit_reflection_inputs χ Ψ hΨ
  let models:=fun (R:Ideal Eis) (hR:R∈rows)=>
    ActualFiber.reflectedFiber q hq m hm rows R f.val (hrows R hR).1 (canonicalLabel_squarefree f)
      (fun I hI=>(hrows I hI).1) u K Ψ hnorm
  apply hasExactCompletedModels_of_representative_identity
    (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq))
    rows K X 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q)) f.val
    (ActualFiber.maskIdeal q m f.val) W
    (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator (reflectionExcludedPrimes q)) u f)
    scale models
  intro R hR J hJ
  rw [unitRowFamily_actual]
  exact hidentity Ψ hperiod hnorm m hm f.val (canonicalLabel_squarefree f) u W a b ha hs hW
    K X hK hX rows hrows R hR ⟨J,hJ⟩

end

theorem finite_selected_branch_collection
    {H U B:Type*} {R:H→Type*} {E:B→Type*}
    [Fintype H] [Fintype U] [Fintype B]
    [∀h,Fintype (R h)] [∀b,Fintype (E b)]
    (f:(h:H)→R h→U→(b:B)→E b→ℂ)
    (g:H→U→(b:B)→E b→ℂ)
    (chosen:(h:H)→B→R h) (α:H→ℂ) (shape:H→B→ℂ) (w:B→ℂ)
    (hbranch:∀h r u b e,4*f h r u b e=
      if r=chosen h b then α h*shape h b*g h u b e else 0) :
    4*(∑h,∑r:R h,∑u,∑b,w b*∑e:E b,f h r u b e)=
      ∑h,α h*∑b,w b*shape h b*∑u,∑e:E b,g h u b e := by
  have hpoint (h:H) (b:B) :
      4*(∑r:R h,∑u,∑e:E b,f h r u b e)=
        α h*shape h b*(∑u,∑e:E b,g h u b e) := by
    simp_rw [Finset.mul_sum,hbranch]
    calc
      _=∑r:R h,if r=chosen h b then
          α h*shape h b*(∑u,∑e:E b,g h u b e) else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases he:r=chosen h b
        · simp only [he,ite_true,Finset.mul_sum]
        · simp only [he,ite_false,Finset.sum_const_zero]
      _=_:=by simp [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hswap : (∑r:R h,∑u,∑b,w b*∑e:E b,f h r u b e)=
      ∑b,w b*(∑r:R h,∑u,∑e:E b,f h r u b e) := by
    calc
      _=∑r:R h,∑b,∑u,w b*∑e:E b,f h r u b e := by
        apply Finset.sum_congr rfl
        intro r hr
        exact Finset.sum_comm
      _=∑b,∑r:R h,∑u,w b*∑e:E b,f h r u b e := Finset.sum_comm
      _=_:=by simp_rw [Finset.mul_sum]
  rw [hswap,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    _=w b*(4*(∑r:R h,∑u,∑e:E b,f h r u b e)) := by ring
    _=w b*(α h*shape h b*(∑u,∑e:E b,g h u b e)) := by rw [hpoint]
    _=_:=by ring

end CanonicalRowCompletion

open scoped BigOperators Classical ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

theorem fixedRayFiberFromRows_value
    (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ)→ representativeRowFiber rows I Q→ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (W:ℝ→ℂ) (X ρ q:ℝ) (k:idealRange (completedResidualScale K I Q)) :
    let d:=fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar
    d.value W X ρ q k=
      ∑r:FixedReflectionRay c hc,∑B:Finset (pool I Q Q0),
        reflectionInactiveStratumWeight I F Q Q0 B*
          ∑l:B→Fin 3,(d.branch (fixedReflectionRayEquiv c hc r,encodeReflectionSix ⟨B,l⟩)).value W X ρ q k := by
  dsimp only
  unfold fixedRayFiberFromRows
  rw [fixedRayFiber_value]
  simp only [mul_one, Finset.mul_sum]

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_value (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (W:ℝ→ℂ) (X:ℝ) (k:idealRange (completedResidualScale K R (maskIdeal q m F))) :
    let d:=reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ
    d.value W X 1 completedRamifiedStep k=
      ∑r:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq),
        ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
          FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
            ∑l:B→Fin 3,(d.branch (fixedReflectionRayEquiv (reflectionConductor q)
              (reflectionConductor_ne_zero q hq) r,encodeReflectionSix ⟨B,l⟩)).value W X 1 completedRamifiedStep k := by
  exact FreeReflection.fixedRayFiberFromRows_value (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    rows R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun a J=>rowScalar q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J)
    (fun a J=>rowScalar_norm q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J)
    W X 1 completedRamifiedStep k

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

omit [Fintype (Eis ⧸ Ideal.span {reflectionConductor q})] in
theorem sourceStratumValue_eq_compressed
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    sourceStratumValue q hq m hm rows R F hR hF hrows v h B J W X=
      fixedRadialCoefficientScalar*
        (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).shape.stratumShapeFactor
          ((fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).c0*
            ∏P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
              freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) P.val)*
        ∑'u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X := by
  let lengthScale:Ideal Eis:=(data q m hm rows R F hF hrows v J).movingIdeal
  have hL:Supported lengthScale:=(data q m hm rows R F hF hrows v J).movingSupported
  let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
  let p:A→Eis:=fun P=>freePrimaryPrime lengthScale (freeConductor q) P.val
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let E:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) B
  let j:A→ℕ:=fun P=>(UniqueFactorizationMonoid.normalizedFactors lengthScale).count P.val.val.val%6
  let : ∀P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
      (Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ (data q m hm rows R F hF hrows v J).movingSupported P.val
  have hjres (P:PrimeIndex (rowResidualPart J.val (maskIdeal q m F))) : j (E (Sum.inl P))=1:=by
    change (UniqueFactorizationMonoid.normalizedFactors lengthScale).count
      (E (Sum.inl P)).val.val.val%6=1
    rw [selectedActiveEquiv_inl]
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inl P)
  have hPB:(fun b:B=>Ideal.span {p (E (Sum.inr b))}:B→Ideal Eis)=(fun b=>b.val.val):=by
    funext b
    rw [show p (E (Sum.inr b))=freePrimaryPrime lengthScale (freeConductor q) (E (Sum.inr b)).val from rfl,
      freePrimaryPrime_span lengthScale (freeConductor q) hL,selectedActiveEquiv_inr]
    exact splitIndex_prime_val q hq m hm rows R F hR hF hrows v J (Sum.inr b.val)
  have hjB:(fun b:B=>j (E (Sum.inr b)))=(fun b=>completedLocalExponent R F b.val.val):=by
    funext b
    change (UniqueFactorizationMonoid.normalizedFactors lengthScale).count
      (E (Sum.inr b)).val.val.val%6=completedLocalExponent R F b.val.val
    rw [selectedActiveEquiv_inr]
    exact splitIndex_local_exponent q hq m hm rows R F hR hF hrows v J (Sum.inr b.val)
  have hdiv (l:B→Fin 3) (side:Fin 3) :
      reflectionExtractedDivisor (fun b:B=>Ideal.span {p (E (Sum.inr b))})
        (fun b:B=>j (E (Sum.inr b))) l side=sourceDivisor q m R F B l side := by
    rw [hPB,hjB]
    rfl
  have hcop:Pairwise (fun a b:A=>IsCoprime (Ideal.span {p a}) (Ideal.span {p b})):=by
    intro a b hab
    exact freePrimaryPrime_coprime lengthScale (freeConductor q) hL (fun he=>hab (Subtype.ext he))
  have he := @FixedFourierGeometry.smoothedValue_eq_nonresidual_equiv _ _ G
    _ B A _ (Finset.Subtype.fintype B) (Finset.Subtype.fintype A) p _ E
    (sourceStratum q hq m hm rows R F hR hF hrows v h B J)
    (fun P => freePrimaryPrime_maximal lengthScale (freeConductor q) hL P.val)
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ p (fun P _=>freePrimaryPrime_primary lengthScale (freeConductor q) hL P.val))
    (fun P=>freePrimaryPrime_ne_zero lengthScale (freeConductor q) hL P.val) hcop
    (fun P=>freePrimaryPrime_good lengthScale (freeConductor q) hL P.val)
    (fun P=>freePrimaryPrime_odd lengthScale (freeConductor q) hL P.val) j
    (fun _=>Nat.mod_lt _ (by decide)) hjres W lo hi hlo hsupp hW X hX
  refine he.trans ?_
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏P:A,p P)*z)
  apply tsum_congr
  intro u
  apply Finset.sum_congr (by ext l; simp only [Finset.mem_univ])
  intro l hl
  unfold sourceCompressedTerm
  dsimp only
  apply tsum_congr
  intro x
  congr 1
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun I:Ideal Eis=>I*x.2.1.val) (hdiv l 1)
    · apply Subtype.ext
      exact congrArg (fun I:Ideal Eis=>I*x.2.2.val) (hdiv l 2)

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma one_le_residualScale (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis))
    (R F:Ideal Eis) (K:ℝ)
    (hrows:∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F) :
    1≤completedResidualScale K R (maskIdeal q m F) := by
  have hJ:=hrows J.val (Finset.mem_filter.mp J.property).1
  rw [←representativeFiber_residualScale rows R (maskIdeal q m F) J K]
  exact one_le_completedResidualScale K J.val (maskIdeal q m F) hJ.1 hJ.2.2

lemma residual_shell (q:ℕ) (m:Eis) (rows:Finset (Ideal Eis))
    (R F:Ideal Eis) (K:ℝ)
    (hrows:∀I∈rows,I≠0 ∧ K/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F) :
    0<completedResidualScale K R (maskIdeal q m F) ∧
      completedResidualScale K R (maskIdeal q m F)/2≤
        (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ) := by
  refine ⟨lt_of_lt_of_le zero_lt_one (one_le_residualScale q m rows R F K hrows J),?_⟩
  have hJ:=hrows J.val (Finset.mem_filter.mp J.property).1
  rw [←representativeFiber_residualScale rows R (maskIdeal q m F) J K]
  exact actualResidualModelRow_shell K J.val (maskIdeal q m F) hJ.1
    (mask_bad q m F) hJ.2.2 hJ.2.1

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance sourceUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

noncomputable def sourceShapeFactor
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) : ℂ :=
  (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).shape.stratumShapeFactor
    ((fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).c0*
      ∏P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
        freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q) P.val)

noncomputable def sourceFixedCoefficient
    (Ψ:Eis→*ℂ) (h:Eis⧸Ideal.span {reflectionConductor q})
    (J:RowIndex q m rows R F) : ℂ :=
  fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    ((data q m hm rows R F hF hrows v J).fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h

noncomputable def compressedSourceTotal (Ψ:Eis→*ℂ)
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  ∑h:Eis⧸Ideal.span {reflectionConductor q},
    sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J*
    ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
      FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
      sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J*
      ∑u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X

theorem completedT_eq_compressedSourceTotal
    (Ψ:Eis→*ℂ)
    (hΨ:CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ)
    (hΨnorm:∀n,‖Ψ n‖≤1)
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      (thetaDerivativeScalar⁻¹*fixedRadialCoefficientScalar)*
        compressedSourceTotal q hq m hm rows R F hR hF hrows v Ψ J W X := by
  rw [completedT_eq_nonresidual_source q hq m hm rows R F hR hF hrows v Ψ hΨ hΨnorm
    J W lo hi hlo hsupp hW X hX]
  unfold compressedSourceTotal
  rw [mul_assoc]
  apply congrArg (fun z:ℂ=>thetaDerivativeScalar⁻¹*z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [mul_left_comm fixedRadialCoefficientScalar]
  apply congrArg (fun z:ℂ=>sourceFixedCoefficient q hq m hm rows R F hF hrows v Ψ h J*z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  rw [sourceStratumValue_eq_compressed q hq m hm rows R F hR hF hrows v h B J
    W lo hi hlo hsupp hW X hX,tsum_fintype]
  change _=(fixedRadialCoefficientScalar*
    (FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
      sourceShapeFactor q hq m hm rows R F hR hF hrows v h B J*
        ∑u:Eisˣ,∑l:B→Fin 3,sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X))
  dsimp only [sourceShapeFactor]
  ring

end CanonicalRowCompletion.ActualFiber

open scoped Classical BigOperators

namespace CompletedGauss
variable {α β γ ι:Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

omit [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] in
lemma residualLabelVia_nonresidual_equiv (E:α⊕β≃ι) (T:β≃γ)
    (l:β→Fin 3) (l':γ→Fin 3) (hl:∀b,l' (T b)=l b) :
    residualLabelVia ((Equiv.sumCongr (Equiv.refl α) T.symm).trans E) l'=
      residualLabelVia E l := by
  let E':=((Equiv.sumCongr (Equiv.refl α) T.symm).trans E)
  funext i
  obtain ⟨a,rfl⟩:=E.surjective i
  cases a with
  | inl a=>
    have he:E (Sum.inl a)=E' (Sum.inl a):=rfl
    calc
      _=residualLabelVia E' l' (E' (Sum.inl a)):=by rw [he]
      _=0:=residualLabelVia_apply E' l' (Sum.inl a)
      _=_:=(residualLabelVia_apply E l (Sum.inl a)).symm
  | inr b=>
    have he:E (Sum.inr b)=E' (Sum.inr (T b)):=by simp [E']
    calc
      _=residualLabelVia E' l' (E' (Sum.inr (T b))):=by rw [he]
      _=l' (T b):=residualLabelVia_apply E' l' (Sum.inr (T b))
      _=l b:=hl b
      _=_:=(residualLabelVia_apply E l (Sum.inr b)).symm

end CompletedGauss

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma activeModelPrimeEquiv_labels
    (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F) :
    residualLabelVia (activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J)
      (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e)=
    residualLabelVia (selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J)
      (reflectionSixSupport e)) (fun b=>reflectionSixLabel (e b.val)) := by
  exact residualLabelVia_nonresidual_equiv _
    (FreeReflection.supportActivePoolEquiv R (maskIdeal q m F) (freeConductor q) e)
    _ _ (fun _=>rfl)

lemma reflectionSixLabel_encode_at {β:Type*} [Fintype β]
    (B:Finset β) (l:B→Fin 3) (b:B) :
    reflectionSixLabel (encodeReflectionSix ⟨B,l⟩ b.val)=l b := by
  classical
  apply Fin.ext
  simp only [encodeReflectionSix,dite_eq_left b.property,reflectionSixLabel]
  change (3+(l b).val)%3=(l b).val
  have hb:=(l b).isLt
  omega

end CanonicalRowCompletion.ActualFiber

open scoped BigOperators Classical ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

lemma supportActivePoolEquiv_divisor (I F Q Q0:Ideal Eis)
    (e:pool I Q Q0 → Fin 6) (side:Fin 3) :
    reflectionExtractedDivisor
      (fun P:reflectionActivePool I Q Q0 e=>P.val)
      (fun P=>completedLocalExponent I F P.val) (reflectionActiveLabel I Q Q0 e) side=
    reflectionExtractedDivisor (fun b:reflectionSixSupport e=>b.val.val)
      (fun b=>completedLocalExponent I F b.val.val) (fun b=>reflectionSixLabel (e b.val)) side := by
  unfold reflectionExtractedDivisor
  symm
  apply Fintype.prod_equiv (supportActivePoolEquiv I Q Q0 e)
  intro b
  rfl

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_decoded_branch_exact
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let B:=reflectionSixSupport e
    let l:=fun b:B=>reflectionSixLabel (e b.val)
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,
        e)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*d.value W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
      else 0 := by
  let D:=data q m hm rows R F hF hrows v J
  let A:=activeSet q hq m hm rows R F hR hF hrows v e J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let S:=D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ideal q) h G A
  let Em:=activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J
  let Es:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) (reflectionSixSupport e)
  let labels:=fun b:reflectionSixSupport e=>reflectionSixLabel (e b.val)
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*
      Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ D.movingSupported P.val
  let hp:=fun P:A=>freePrimaryPrime_ne_zero _ _ D.movingSupported P.val
  let hg:=fun P:A=>freePrimaryPrime_good _ _ D.movingSupported P.val
  let j:=fun P:A=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6
  have ht:=reflectedFiber_branch_exact q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound J h rho u
    e W lo hi hlo hsupp hW X hX hK hk
  refine ht.trans (congrArg (fun z:ℂ=>if rho=D.sourceRowResidue
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
    h G A then fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
      G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*z
    else 0) ?_)
  unfold sourceCompressedTerm
  apply tsum_congr
  intro x
  have hlabel:residualLabelVia Em (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e)=
      residualLabelVia Es labels:=activeModelPrimeEquiv_labels q hq m hm rows R F hR hF hrows v e J
  have hdiv (side:Fin 3):columnDivisor q m R F e side=
      sourceDivisor q m R F (reflectionSixSupport e) labels side:=
    FreeReflection.supportActivePoolEquiv_divisor R F (maskIdeal q m F) (freeConductor q) e side
  have harg:nonzeroDualDilation (columnDivisor q m R F e 1) (columnDivisor q m R F e 2)
      (columnDivisor_ne_zero q m R F e 1) (columnDivisor_ne_zero q m R F e 2) x=
    nonzeroDualDilation (sourceDivisor q m R F (reflectionSixSupport e) labels 1)
      (sourceDivisor q m R F (reflectionSixSupport e) labels 2)
      (sourceDivisor_ne_zero q m R F (reflectionSixSupport e) labels 1)
      (sourceDivisor_ne_zero q m R F (reflectionSixSupport e) labels 2) x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> apply Subtype.ext <;> dsimp only [nonzeroDualDilation] <;> rw [hdiv]
  exact congrArg₂ (fun label arg =>
    @FixedFourierGeometry.stratumBranchTerm _ _ G A (Finset.Subtype.fintype A)
      _ _ S _ hp hg j u label W X arg) hlabel harg

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

theorem reflectedFiber_encoded_branch_exact
    (K:ℝ) (Ψ:Eis→*ℂ) (hΨ:∀n,‖Ψ n‖≤1)
    (hbound:∀I∈rows,(Ideal.absNorm I:ℝ)≤K)
    (J:RowIndex q m rows R F)
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue)
    (u:Eisˣ) (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q))) (l:B→Fin 3)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X)
    (hK:0<completedResidualScale K R (maskIdeal q m F))
    (hk:completedResidualScale K R (maskIdeal q m F)/2≤
      (Ideal.absNorm (rowResidualPart J.val (maskIdeal q m F)):ℝ)) :
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,
        encodeReflectionSix ⟨B,l⟩)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    4*d.value W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        sourceCompressedTerm q hq m hm rows R F hR hF hrows v h B J u l W X
      else 0 := by
  let result:(ΣB:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),B→Fin 3) → ℂ := fun x =>
    let D:=data q m hm rows R F hF hrows v J
    let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v x.1 J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
      (reflectionConductor_ideal q) h G A then
      fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
        (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
      G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
      sourceCompressedTerm q hq m hm rows R F hR hF hrows v h x.1 J u x.2 W X
    else 0
  have ht:=reflectedFiber_decoded_branch_exact q hq m hm rows R F hR hF hrows v K Ψ hΨ hbound J h rho u
    (encodeReflectionSix ⟨B,l⟩) W lo hi hlo hsupp hW X hX hK hk
  change _=result (decodeReflectionSix (encodeReflectionSix ⟨B,l⟩)) at ht
  rw [decode_encodeReflectionSix] at ht
  change _=result ⟨B,l⟩
  exact ht

end CanonicalRowCompletion.ActualFiber

end

end OAI
