import OAI.NumberTheory.DirichletL.GaussSum.ActiveReindexing

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

namespace CanonicalRowCompletion.GoodMaskRowData
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

theorem sum_selectedSourceRowScalar_mul {m f z:Eis} (D:GoodMaskRowData m f z)
    (Q:Ideal Eis) (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)})))
    [Fintype G.PhaseResidue] (Ψ:Eis→*ℂ) (u:Eisˣ) (n:ℕ)
    (k dN dB:Ideal Eis) (weight:G.PhaseResidue → ℂ) :
    (∑rho:G.PhaseResidue,D.selectedSourceRowScalar Q c hc hcQ h G A Ψ u n rho k dN dB*weight rho)=
      (D.sourceRowScalar Q c hc hcQ h G A Ψ u n*residualArgumentPhase k 1 dN dB)*
        weight (D.sourceRowResidue Q c hcQ h G A) := by
  simp only [selectedSourceRowScalar,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end CanonicalRowCompletion.GoodMaskRowData

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance rayUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    [Fintype (Eis⧸Ideal.span {reflectionConductor q})]
    [∀h:Eis⧸Ideal.span {reflectionConductor q},
      Fintype (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue]

def rowResidue (h:Eis⧸Ideal.span {reflectionConductor q})
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (J:RowIndex q m rows R F) :
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue :=
  (data q m hm rows R F hF hrows v J).sourceRowResidue
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ideal q) h
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    (activeSet q hq m hm rows R F hR hF hrows v e J)

def rowAmplitude (Ψ:Eis→*ℂ) (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (n:ℕ) (J:RowIndex q m rows R F) : ℂ :=
  (data q m hm rows R F hF hrows v J).sourceRowScalar
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) h
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    (activeSet q hq m hm rows R F hR hF hrows v e J) Ψ u n*
      residualArgumentPhase (rowResidualPart J.val (maskIdeal q m F)) 1
        (columnDivisor q m R F e 1) (columnDivisor q m R F e 2)

omit [∀ h : Eis ⧸ Ideal.span {reflectionConductor q},
  Fintype (fixedFourierGeometry (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) h).PhaseResidue] in
lemma rowScalar_eq_ite (Ψ:Eis→*ℂ)
    (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (n:ℕ) (J:RowIndex q m rows R F)
    (rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue) :
    rowScalar q hq m hm rows R F hR hF hrows v Ψ (⟨h,rho,u⟩,e) n J=
      if rho=rowResidue q hq m hm rows R F hR hF hrows v h e J then
        rowAmplitude q hq m hm rows R F hR hF hrows v Ψ h u e n J else 0 := rfl

theorem sum_rowScalar_phase_mul (Ψ:Eis→*ℂ)
    (h:Eis⧸Ideal.span {reflectionConductor q}) (u:Eisˣ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (n:ℕ) (J:RowIndex q m rows R F)
    (weight:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue → ℂ) :
    (∑rho:(fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue,
      rowScalar q hq m hm rows R F hR hF hrows v Ψ (⟨h,rho,u⟩,e) n J*weight rho)=
      rowAmplitude q hq m hm rows R F hR hF hrows v Ψ h u e n J*
        weight (rowResidue q hq m hm rows R F hR hF hrows v h e J) := by
  exact (data q m hm rows R F hF hrows v J).sum_selectedSourceRowScalar_mul
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) h
    (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    (activeSet q hq m hm rows R F hR hF hrows v e J) Ψ u n
    (rowResidualPart J.val (maskIdeal q m F))
    (columnDivisor q m R F e 1) (columnDivisor q m R F e 2) weight

theorem sum_rowScalar_fixedRays (Ψ:Eis→*ℂ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (n:ℕ) (J:RowIndex q m rows R F)
    (weight:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq) → ℂ) :
    (∑ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq),
      rowScalar q hq m hm rows R F hR hF hrows v Ψ (ray,e) n J*weight ray)=
      ∑h:Eis⧸Ideal.span {reflectionConductor q},∑u:Eisˣ,
        rowAmplitude q hq m hm rows R F hR hF hrows v Ψ h u e n J*
          weight ⟨h,rowResidue q hq m hm rows R F hR hF hrows v h e J,u⟩ := by
  rw [sum_fixedReflectionRay]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact sum_rowScalar_phase_mul q hq m hm rows R F hR hF hrows v Ψ h u e n J _

theorem sum_rowScalar_fixedRayFin (Ψ:Eis→*ℂ)
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6)
    (n:ℕ) (J:RowIndex q m rows R F)
    (weight:Fin (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq)) → ℂ) :
    (∑i:Fin (fixedReflectionRayCount (reflectionConductor q) (reflectionConductor_ne_zero q hq)),
      rowScalar q hq m hm rows R F hR hF hrows v Ψ
        ((fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq)).symm i,e)
        n J*weight i)=
      ∑h:Eis⧸Ideal.span {reflectionConductor q},∑u:Eisˣ,
        rowAmplitude q hq m hm rows R F hR hF hrows v Ψ h u e n J*
          weight (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq)
            ⟨h,rowResidue q hq m hm rows R F hR hF hrows v h e J,u⟩) := by
  calc
    _=(∑ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq),
      rowScalar q hq m hm rows R F hR hF hrows v Ψ (ray,e) n J*
        weight (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray)):=by
      symm
      apply Fintype.sum_equiv (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq))
      intro ray
      simp only [Equiv.symm_apply_apply]
    _=_:=sum_rowScalar_fixedRays q hq m hm rows R F hR hF hrows v Ψ e n J _

end CanonicalRowCompletion.ActualFiber

namespace CompletedGauss
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

theorem hasExactCompletedModels_of_representative_identity
    (rays:ℕ) (rows:Finset (Ideal Eis)) (K X ρ q levelBound:ℝ)
    (F Q:Ideal Eis) (W:ℝ→ℂ) (Ψ:Ideal Eis→Eis→*ℂ) (scale:ℂ)
    (model:∀I:Ideal Eis,I∈rows→ReflectedFiberData rays levelBound K I F Q)
    (hmodel:∀(I:Ideal Eis) (hI:I∈rows),∀J∈representativeRowFiber rows I Q,
      completedT (Ψ J) W X=scale*(model I hI).idealValue W X ρ q (rowResidualPart J Q)) :
    HasExactCompletedModels rays rows K X ρ q levelBound F Q W Ψ scale := by
  intro A hA T hT hnonempty
  obtain ⟨I,hI⟩:=hnonempty
  obtain ⟨hIrows,hIA,hIT⟩:=Finset.mem_filter.mp hI
  refine ⟨I,hI,model I hIrows,?_⟩
  intro J hJ
  apply hmodel I hIrows J
  simpa only [representativeRowFiber,hIA,hIT] using hJ

end CompletedGauss

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

noncomputable def sourcePrimeSet (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) :
    Finset (FreePrimeIndex (data q m hm rows R F hF hrows v J).movingIdeal (freeConductor q)) :=
  completeActiveSet (splitIndex q hq m hm rows R F hR hF hrows v J) B

omit [Fintype (Eis ⧸ span {reflectionConductor q})] in
lemma sourcePrimeSet_encode (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (e:B→Fin 3) (J:RowIndex q m rows R F) :
    activeSet q hq m hm rows R F hR hF hrows v (encodeReflectionSix ⟨B,e⟩) J=
      sourcePrimeSet q hq m hm rows R F hR hF hrows v B J := by
  unfold activeSet sourcePrimeSet
  rw [reflectionSixSupport_encode]

noncomputable abbrev sourceStratum
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) :=
  (data q m hm rows R F hF hrows v J).activeStratum
    (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q) (reflectionConductor_ideal q)
    h (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J)

noncomputable def sourceStratumValue
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  let lengthScale:Ideal Eis:=(data q m hm rows R F hF hrows v J).movingIdeal
  have hL:Supported lengthScale:=(data q m hm rows R F hF hrows v J).movingSupported
  let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  letI : ∀P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
      (Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ (data q m hm rows R F hF hrows v J).movingSupported P.val
  exact @ControlledStratumArithmetic.smoothedValue A (Finset.Subtype.fintype A)
    _ _ _ _ _ (sourceStratum q hq m hm rows R F hR hF hrows v h B J) _
    (mul_dvd_mul_left 9 G.denominator_dvd)
    (primary_finset_product Finset.univ (fun P:A=>freePrimaryPrime lengthScale (freeConductor q) P.val)
      (fun P _=>freePrimaryPrime_primary lengthScale (freeConductor q) hL P.val))
    G.primary G.shape (fun P=>freePrimaryPrime_ne_zero lengthScale (freeConductor q) hL P.val)
    G.denominator_ne_zero (fun P=>freePrimaryPrime_good lengthScale (freeConductor q) hL P.val)
    (fun P=>(UniqueFactorizationMonoid.normalizedFactors lengthScale).count P.val.val.val%6) W X

private lemma finset_union_image_decidableEq_eq {α β : Type*} (d₁ d₂ : DecidableEq β)
    (t : Finset β) (f : α → β) (s : Finset α) :
    @Union.union (Finset β) (@Finset.instUnion β d₁) t (@Finset.image α β d₁ f s) =
      @Union.union (Finset β) (@Finset.instUnion β d₂) t (@Finset.image α β d₂ f s) := by
  cases Subsingleton.elim d₁ d₂
  rfl

theorem completedT_eq_nonresidual_source
    (Ψ:Eis→*ℂ)
    (hΨ:CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ)
    (hΨnorm:∀n,‖Ψ n‖≤1)
    (J:RowIndex q m rows R F) (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo)
    (hsupp:Function.support W⊆Set.Icc lo hi) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT (rowTwist Ψ (maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator J.val)) W X=
      thetaDerivativeScalar⁻¹*
        ∑h:Eis⧸Ideal.span {reflectionConductor q},
          fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
            ((data q m hm rows R F hF hrows v J).fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
          ∑B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)),
            FreeReflection.reflectionInactiveStratumWeight R F (maskIdeal q m F) (freeConductor q) B*
              sourceStratumValue q hq m hm rows R F hR hF hrows v h B J W X := by
  let D:=data q m hm rows R F hF hrows v J
  let : ∀P:FreePrimeIndex D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}),
      (Ideal.span {freePrimaryPrime D.movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported
  let (A:Finset (FreePrimeIndex D.movingIdeal (freeConductor q))) :
      ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal D.movingIdeal _ D.movingSupported P.val
  have hJ:J.val≠0:=hrows J.val (Finset.mem_filter.mp J.property).1
  have hz:Ideal.span {v.val*ConcretePrimeRowBridge.idealGenerator J.val}=J.val:=by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,ConcretePrimeRowBridge.span_idealGenerator]
  have parts:=representativeFiber_parts rows R (maskIdeal q m F) J
  have hsplit:splitIndex q hq m hm rows R F hR hF hrows v J=
      D.primeFiberEquiv R J.val F (freeConductor q) hR hJ hF (maskElement_ne_zero q m hm)
        (ConcretePrimeRowBridge.span_idealGenerator F) hz (mask_bad q m F)
        (residual_coprime_free_base q hq m F J.val) parts.1.symm parts.2.symm := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    cases x <;> rfl
  have hml:lambda∣maskElement q m:=by
    exact ((reflectionExcludedGenerator_bad q).1).trans (dvd_mul_left _ m)
  have hm2:(2:Eis)∣maskElement q m:=by
    exact ((reflectionExcludedGenerator_bad q).2).trans (dvd_mul_left _ m)
  rw [D.completedT_eq_actualControlledSource (CanonicalCoefficientClass.fixedBaseConductor q)
    (CanonicalCoefficientClass.fixedBaseConductor_ne_zero q hq) (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q)
    (fun h=>fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h)
    Ψ hΨ hΨnorm hml hm2 W lo hi hlo hsupp hW X hX]
  unfold actualControlledSource
  apply congrArg (fun z:ℂ=>thetaDerivativeScalar⁻¹*z)
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun z:ℂ=>fixedThetaRowCoeff (reflectionConductor q)
    (reflectionConductor_ne_zero q hq) (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*z)
  let weight : Finset (FreePrimeIndex D.movingIdeal (freeConductor q)) → ℂ := fun A =>
    @ControlledStratumArithmetic.smoothedValue A (Finset.Subtype.fintype A)
      _ _ _ _ _ (D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q)
        (reflectionConductor q) (reflectionConductor_ideal q) h
        (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h) A) _
      (mul_dvd_mul_left 9 (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).denominator_dvd)
      (primary_finset_product Finset.univ (fun P:A=>freePrimaryPrime D.movingIdeal (freeConductor q) P.val)
        (fun P _=>freePrimaryPrime_primary D.movingIdeal (freeConductor q) D.movingSupported P.val))
      (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).primary
      (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).shape
      (fun P=>freePrimaryPrime_ne_zero D.movingIdeal (freeConductor q) D.movingSupported P.val)
      (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).denominator_ne_zero
      (fun P=>freePrimaryPrime_good D.movingIdeal (freeConductor q) D.movingSupported P.val)
      (fun P=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6) W X
  convert D.inactive_source_reindex R J.val F (freeConductor q) hR hJ hF
    (maskElement_ne_zero q m hm) (ConcretePrimeRowBridge.span_idealGenerator F) hz
    (mask_bad q m F) (residual_coprime_free_base q hq m F J.val) parts.1.symm parts.2.symm
    weight using 1
  · apply Finset.sum_congr (by ext A; exact iff_of_true (Finset.mem_univ A) (Finset.mem_univ A))
    intro A hA
    rfl
  · apply Finset.sum_congr (by ext B; exact iff_of_true (Finset.mem_univ B) (Finset.mem_univ B))
    intro B hB
    congr 1
    calc
      sourceStratumValue q hq m hm rows R F hR hF hrows v h B J W X=
          weight (sourcePrimeSet q hq m hm rows R F hR hF hrows v B J):=by
        rfl
      _=_:=by
        apply congrArg weight
        rw [sourcePrimeSet, completeActiveSet, hsplit]
        exact finset_union_image_decidableEq_eq _ _ _ _ _

end CanonicalRowCompletion.ActualFiber

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedRayFiber_branch (c:Eis) (hc:c≠0) (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0)
    (K:ℝ)
    (rayWeight:FixedBranchIndex c hc I Q Q0→ℂ) (hray:∀x,‖rayWeight x‖≤1)
    (rowPhase:FixedBranchIndex c hc I Q Q0→ℕ→idealRange (completedResidualScale K I Q)→ℂ)
    (hrow:∀x m k,‖rowPhase x m k‖≤1)
    (r:FixedReflectionRay c hc) (e:pool I Q Q0→Fin 6) :
    let G:=fixedFourierGeometry c hc r.1
    (fixedRayFiber c hc I F Q Q0 hI hQ K rayWeight hray rowPhase hrow).branch
      (fixedReflectionRayEquiv c hc r,e)=
      sixPhaseFixedCuspBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c) G.levelScale
        G.levelScale_pos (G.levelScale_le hc) e G.shape.index r.2.2
        (G.staticPhase r.2.1 r.2.2) (G.staticPhase_norm_le_one r.2.1 r.2.2)
        (rowPhase (r,e)) (hrow (r,e)) := by
  let f : FixedReflectionRay c hc → ReflectedBranchData (fixedCuspLevelBound c) K I F Q := fun t =>
    let G:=fixedFourierGeometry c hc t.1
    sixPhaseFixedCuspBranch I F Q Q0 hI hQ K (fixedCuspLevelBound c) G.levelScale
      G.levelScale_pos (G.levelScale_le hc) e G.shape.index t.2.2
      (G.staticPhase t.2.1 t.2.2) (G.staticPhase_norm_le_one t.2.1 t.2.2)
      (rowPhase (t,e)) (hrow (t,e))
  change f ((fixedReflectionRayEquiv c hc).symm ((fixedReflectionRayEquiv c hc) r))=f r
  exact congrArg f ((fixedReflectionRayEquiv c hc).symm_apply_apply r)

theorem fixedRayFiberFromRows_branch_value
    (c:Eis) (hc:c≠0) (rows:Finset (Ideal Eis))
    (I F Q Q0:Ideal Eis) (hI:I≠0) (hQ:Q≠0) (K:ℝ)
    (scalar:(FixedBranchIndex c hc I Q Q0×ℕ) → representativeRowFiber rows I Q → ℂ)
    (hscalar:∀a J,‖scalar a J‖≤1)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (J:representativeRowFiber rows I Q) (r:FixedReflectionRay c hc)
    (e:pool I Q Q0→Fin 6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X ρ q:ℝ) (hX:0<X) (hρ:0<ρ) (hq:1<q)
    (hK:0<completedResidualScale K I Q)
    (hk:completedResidualScale K I Q/2≤
      (Ideal.absNorm (fiberResidualIndex rows I Q K hbad hrows J).val:ℝ)) :
    let G:=fixedFourierGeometry c hc r.1
    let d:=(fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).branch
      (fixedReflectionRayEquiv c hc r,e)
    let A:=reflectionExtractedDivisor (fun P:d.primes=>P.val)
      (fun P=>completedLocalExponent I F P.val) d.label 1
    let B:=reflectionExtractedDivisor (fun P:d.primes=>P.val)
      (fun P=>completedLocalExponent I F P.val) d.label 2
    d.value W X ρ q (fiberResidualIndex rows I Q K hbad hrows J)=
      d.rawValue (fun m n b=>G.array r.2.1 r.2.2 m (A*n) (B*b))
        (fun m _=>scalar ((r,e),m) J) W X ρ q (fiberResidualIndex rows I Q K hbad hrows J) := by
  let G:=fixedFourierGeometry c hc r.1
  let σ:ℕ→idealRange (completedResidualScale K I Q)→ℂ:=
    fun m=>extendFiberRowScalar rows I Q K scalar ((r,e),m)
  have hσ:∀m k,‖σ m k‖≤1:=fun m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar ((r,e),m)
  have hb:=fixedRayFiber_branch c hc I F Q Q0 hI hQ K (fun _=>1) (by intro x;simp)
    (fun x m=>extendFiberRowScalar rows I Q K scalar (x,m))
    (fun x m=>extendFiberRowScalar_norm_le_one rows I Q K scalar hscalar (x,m)) r e
  change (fixedRayFiberFromRows c hc rows I F Q Q0 hI hQ K scalar hscalar).branch _=_ at hb
  let P (d : ReflectedBranchData (fixedCuspLevelBound c) K I F Q) : Prop :=
    let A := reflectionExtractedDivisor (fun P : d.primes => P.val)
      (fun P => completedLocalExponent I F P.val) d.label 1
    let B := reflectionExtractedDivisor (fun P : d.primes => P.val)
      (fun P => completedLocalExponent I F P.val) d.label 2
    d.value W X ρ q (fiberResidualIndex rows I Q K hbad hrows J) =
      d.rawValue (fun m n b => G.array r.2.1 r.2.2 m (A * n) (B * b))
        (fun m _ => scalar ((r, e), m) J) W X ρ q
        (fiberResidualIndex rows I Q K hbad hrows J)
  apply Eq.mpr (congrArg P hb)
  dsimp only [P]
  rw [G.sixPhaseFixedCuspBranch_value_eq_geometric_rawValue I F Q Q0 hI hQ K
    (fixedCuspLevelBound c) (G.levelScale_le hc) e r.2.1 r.2.2 σ hσ
    W a b ha hsupp hW X ρ q hX hρ hq hK (fiberResidualIndex rows I Q K hbad hrows J) hk]
  apply ReflectedBranchData.rawValue_congr_phase_at
  intro m
  exact extendFiberRowScalar_at_original rows I Q K hbad hrows scalar ((r,e),m) J

end CompletedGauss.FreeReflection

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

omit [Fintype (Eis ⧸ span {reflectionConductor q})] in
lemma columnDivisor_ne_zero
    (e:FreeReflection.pool R (maskIdeal q m F) (freeConductor q) → Fin 6) (side:Fin 3) :
    columnDivisor q m R F e side≠0 := by
  let : ∀P:FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e,
      P.val.IsMaximal:=fun P=>FreeReflection.pool_maximal R (maskIdeal q m F) (freeConductor q)
        ⟨P.val,FreeReflection.reflectionActivePool_subset R (maskIdeal q m F) (freeConductor q) e P.property⟩
  exact reflectionExtractedDivisor_ne_zero
    (fun P:FreeReflection.reflectionActivePool R (maskIdeal q m F) (freeConductor q) e=>P.val)
    (fun P=>NeZero.ne P.val) _ _ _

theorem reflectedFiber_branch_exact
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
    let D:=data q m hm rows R F hF hrows v J
    let A:=activeSet q hq m hm rows R F hR hF hrows v e J
    let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
    let S:=D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
      (reflectionConductor_ideal q) h G A
    let E:=activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J
    letI : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
      fun P=>freePrimaryPrime_maximal _ _ D.movingSupported P.val
    let hp:=fun P:A=>freePrimaryPrime_ne_zero _ _ D.movingSupported P.val
    let hg:=fun P:A=>freePrimaryPrime_good _ _ D.movingSupported P.val
    let j:=fun P:A=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6
    let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
    let d:=(reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
      (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,e)
    let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
    let dN:=columnDivisor q m R F e 1
    let dB:=columnDivisor q m R F e 2
    let hdN:=columnDivisor_ne_zero q m R F e 1
    let hdB:=columnDivisor_ne_zero q m R F e 2
    4*d.value W X 1 completedRamifiedStep k=
      if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
        (reflectionConductor_ideal q) h G A then
        fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
          (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
        G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)*
        ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
          @FixedFourierGeometry.stratumBranchTerm _ _ G A (Finset.Subtype.fintype A) _ _ S _ hp hg j u
            (residualLabelVia E (FreeReflection.reflectionActiveLabel R (maskIdeal q m F) (freeConductor q) e))
            W X (nonzeroDualDilation dN dB hdN hdB x)
      else 0 := by
  let D:=data q m hm rows R F hF hrows v J
  let A:=activeSet q hq m hm rows R F hR hF hrows v e J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let S:=D.activeStratum (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
    (reflectionConductor_ideal q) h G A
  let E:=activeModelPrimeEquiv q hq m hm rows R F hR hF hrows v e J
  let : ∀P:A,(Ideal.span {freePrimaryPrime D.movingIdeal (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ D.movingSupported P.val
  let hp:=fun P:A=>freePrimaryPrime_ne_zero _ _ D.movingSupported P.val
  let hg:=fun P:A=>freePrimaryPrime_good _ _ D.movingSupported P.val
  let j:=fun P:A=>(UniqueFactorizationMonoid.normalizedFactors D.movingIdeal).count P.val.val.val%6
  let ray:FixedReflectionRay (reflectionConductor q) (reflectionConductor_ne_zero q hq):=⟨h,rho,u⟩
  let k:=fiberResidualIndex rows R (maskIdeal q m F) K (mask_bad q m F)
    (fun I hI=>⟨hrows I hI,hbound I hI⟩) J
  let scalar:(FreeReflection.FixedBranchIndex (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      R (maskIdeal q m F) (freeConductor q)×ℕ) → RowIndex q m rows R F → ℂ:=fun a J=>rowScalar q hq m hm rows R F hR hF hrows v Ψ a.1 a.2 J
  have hscalar:∀a J,‖scalar a J‖≤1:=fun a J=>rowScalar_norm q hq m hm rows R F hR hF hrows v Ψ hΨ a.1 a.2 J
  let σ:ℕ→idealRange (completedResidualScale K R (maskIdeal q m F))→ℂ:=
    fun n=>extendFiberRowScalar rows R (maskIdeal q m F) K scalar ((ray,e),n)
  have hσ:∀n k,‖σ n k‖≤1:=fun n=>extendFiberRowScalar_norm_le_one rows R (maskIdeal q m F)
    K scalar hscalar ((ray,e),n)
  let d:=FreeReflection.sixPhaseFixedCuspBranch R F (maskIdeal q m F) (freeConductor q) hR
    (maskIdeal_ne_zero q m hm F hF.ne_zero) K (fixedCuspLevelBound (reflectionConductor q))
    G.levelScale G.levelScale_pos (G.levelScale_le (reflectionConductor_ne_zero q hq))
    e G.shape.index u (G.staticPhase rho u) (G.staticPhase_norm_le_one rho u) σ hσ
  have hb:=FreeReflection.fixedRayFiber_branch (reflectionConductor q) (reflectionConductor_ne_zero q hq)
    R F (maskIdeal q m F) (freeConductor q) hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K
    (fun _=>1) (by intro;simp)
    (fun x n=>extendFiberRowScalar rows R (maskIdeal q m F) K scalar (x,n))
    (fun x n=>extendFiberRowScalar_norm_le_one rows R (maskIdeal q m F) K scalar hscalar (x,n)) ray e
  change (reflectedFiber q hq m hm rows R F hR hF hrows v K Ψ hΨ).branch
    (fixedReflectionRayEquiv (reflectionConductor q) (reflectionConductor_ne_zero q hq) ray,e)=d at hb
  dsimp only
  rw [hb]
  let dN:=columnDivisor q m R F e 1
  let dB:=columnDivisor q m R F e 2
  let η:=fun n I J=>G.array rho u n (dN*I) (dB*J)
  let τ:=fun n (l:idealRange (completedResidualScale K R (maskIdeal q m F)))=>
    @ControlledStratumArithmetic.modelRowPhase A (Finset.Subtype.fintype A) _ _ _ _ _ S _ G.shape hp hg j u n*residualArgumentPhase l.val 1 dN dB
  let weight:=fixedThetaRowCoeff (reflectionConductor q) (reflectionConductor_ne_zero q hq)
      (D.fixedFactor Ψ (CanonicalCoefficientClass.fixedBaseConductor q)) h*
    G.shape.stratumShapeFactor (G.c0*∏P:A,freePrimaryPrime D.movingIdeal (freeConductor q) P.val)
  have hraw:d.value W X 1 completedRamifiedStep k=d.rawValue η σ W X 1 completedRamifiedStep k:=by
    exact G.sixPhaseFixedCuspBranch_value_eq_geometric_rawValue R F (maskIdeal q m F) (freeConductor q)
      hR (maskIdeal_ne_zero q m hm F hF.ne_zero) K (fixedCuspLevelBound (reflectionConductor q))
      (G.levelScale_le (reflectionConductor_ne_zero q hq)) e rho u σ hσ
      W lo hi hlo hsupp hW X 1 completedRamifiedStep hX (by norm_num) completedRamifiedStep_gt_one hK k hk
  rw [hraw]
  have hσrow (n:ℕ):σ n k=rowScalar q hq m hm rows R F hR hF hrows v Ψ (ray,e) n J:=
    extendFiberRowScalar_at_original rows R (maskIdeal q m F) K (mask_bad q m F)
      (fun I hI=>⟨hrows I hI,hbound I hI⟩) scalar ((ray,e),n) J
  by_cases hphase:rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q)
    (reflectionConductor q) (reflectionConductor_ideal q) h G A
  · rw [ite_eq_left hphase]
    have hσmatch (n:ℕ):σ n k=weight*τ n k := by
      rw [hσrow]
      change (if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q)
        (reflectionConductor q) (reflectionConductor_ideal q) h G A then
        D.sourceRowScalar (CanonicalCoefficientClass.fixedBaseConductor q) (reflectionConductor q)
          (reflectionConductor_ne_zero q hq) (reflectionConductor_ideal q) h G A Ψ u n*
            residualArgumentPhase k.val 1 dN dB else 0)=_
      rw [ite_eq_left hphase]
      dsimp only [GoodMaskRowData.sourceRowScalar,weight,τ]
      change (weight*@ControlledStratumArithmetic.modelRowPhase A (Finset.Subtype.fintype A) _ _ _ _ _ S _ G.shape hp hg j u n)*residualArgumentPhase k.val 1 dN dB=
        weight*(@ControlledStratumArithmetic.modelRowPhase A (Finset.Subtype.fintype A) _ _ _ _ _ S _ G.shape hp hg j u n*residualArgumentPhase k.val 1 dN dB)
      exact mul_assoc _ _ _
    rw [d.rawValue_congr_phase_at η σ (fun n l=>weight*τ n l) W X 1 completedRamifiedStep k hσmatch,
      d.rawValue_mul_phase_at η τ W X 1 completedRamifiedStep k (fun _=>weight)]
    have hterm:=@FixedFourierGeometry.stratumBranchTerm_tsum_eq_rawValue_at_row _ _ G A
      (Finset.Subtype.fintype A) _ _ S _ hp hg j _ _ _ _ _ d hK k E
      (fun P=>activeModelPrimeEquiv_span q hq m hm rows R F hR hF hrows v e J (Sum.inl P))
      (fun P=>activeModelPrimeEquiv_span q hq m hm rows R F hR hF hrows v e J (Sum.inr P))
      (fun P=>activeModelPrimeEquiv_exponent q hq m hm rows R F hR hF hrows v e J (Sum.inl P))
      (fun P=>activeModelPrimeEquiv_exponent q hq m hm rows R F hR hF hrows v e J (Sum.inr P)) rfl u W X
    have harr:η=fun n I J=>G.array
        (Ideal.Quotient.mk _ (-(@ControlledStratumArithmetic.matrix A (Finset.Subtype.fintype A) _ _ _ _ _ S (fun _=>1) 1 1)*(@ControlledStratumArithmetic.U A (Finset.Subtype.fintype A) _ _ _ _ _ S))) u n (dN*I) (dB*J):=by
      dsimp only [η]
      rw [hphase]
      rfl
    rw [harr]
    calc
      _=weight*(4*d.rawValue
          (fun n I J=>G.array (Ideal.Quotient.mk _ (-(@ControlledStratumArithmetic.matrix A (Finset.Subtype.fintype A) _ _ _ _ _ S (fun _=>1) 1 1)*(@ControlledStratumArithmetic.U A (Finset.Subtype.fintype A) _ _ _ _ _ S))) u n (dN*I) (dB*J))
          τ W X 1 completedRamifiedStep k):=by ring
      _=_:=congrArg (fun z:ℂ=>weight*z) hterm.symm
  · rw [ite_eq_right hphase]
    have hσzero (n:ℕ):σ n k=0 := by
      rw [hσrow]
      change (if rho=D.sourceRowResidue (CanonicalCoefficientClass.fixedBaseConductor q)
        (reflectionConductor q) (reflectionConductor_ideal q) h G A then _ else 0)=0
      rw [ite_eq_right hphase]
    rw [d.rawValue_congr_phase_at η σ (fun _ _=>0) W X 1 completedRamifiedStep k hσzero,
      d.rawValue_zero_phase η W X 1 completedRamifiedStep k,mul_zero]

end CanonicalRowCompletion.ActualFiber

open scoped Classical

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CubicEisenstein CanonicalCoefficientClass
local notation "Eis" => ActualEisensteinCubic.O

theorem dirichletTarget_of_reflection_shells
    (hmodels:∀(q₀:ℕ) [NeZero q₀] (χ:DirichletCharacter ℂ q₀),
      ∃(rays:ℕ) (scale:ℂ),
        HasFixedShellModels (reflectionExcludedPrimes q₀) (initialBase χ)
          rays scale 1 completedRamifiedStep (fixedCuspLevelBound (reflectionConductor q₀))) :
    ShortDraft.DirichletTarget := by
  apply dirichletTarget_of_theta_models
  intro q₀ hq₀ χ
  obtain ⟨rays,scale,hm⟩:=hmodels q₀ χ
  refine ⟨reflectionExcludedPrimes q₀,reflectionExcludedPrimes_bad q₀,
    reflectionExcludedPrimes_prime q₀,1,completedRamifiedStep,
    fixedCuspLevelBound (reflectionConductor q₀),by norm_num,
    completedRamifiedStep_gt_one,reflectionLevelBound_ge_one q₀ (NeZero.ne q₀),?_⟩
  exact hasCanonicalThetaModels_of_fixed_shell_models
    (reflectionExcludedPrimes q₀) (initialBase χ) rays scale 1 completedRamifiedStep
    (fixedCuspLevelBound (reflectionConductor q₀)) hm

end CanonicalRowCompletion

namespace ShortDraft

theorem zeta_nonvanishing_of_dirichletTarget (h:DirichletTarget)
    (s:ℂ) (hs:(23/24:ℝ)<s.re) (hs1:s≠1) : riemannZeta s≠0 := by
  have he:=h 1 (1:DirichletCharacter ℂ 1) s hs (by simp only [true_and]; exact hs1)
  simpa only [DirichletCharacter.LFunction_modOne_eq] using he

end ShortDraft

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

def sourceDivisor (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (l:B→Fin 3) (side:Fin 3) : Ideal Eis :=
  reflectionExtractedDivisor (fun b:B=>b.val.val) (fun b=>completedLocalExponent R F b.val.val) l side

omit [Fintype (Eis ⧸ span {reflectionConductor q})] in
lemma sourceDivisor_ne_zero (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (l:B→Fin 3) (side:Fin 3) : sourceDivisor q m R F B l side≠0 := by
  have hn (b:B):b.val.val≠0:=by
    let : b.val.val.IsMaximal:=FreeReflection.pool_maximal R (maskIdeal q m F) (freeConductor q) b.val
    exact NeZero.ne _
  exact reflectionExtractedDivisor_ne_zero _ hn
    (fun b=>completedLocalExponent R F b.val.val) l side

noncomputable def sourceCompressedTerm
    (h:Eis⧸Ideal.span {reflectionConductor q})
    (B:Finset (FreeReflection.pool R (maskIdeal q m F) (freeConductor q)))
    (J:RowIndex q m rows R F) (u:Eisˣ) (l:B→Fin 3) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  let lengthScale:Ideal Eis:=(data q m hm rows R F hF hrows v J).movingIdeal
  have hL:Supported lengthScale:=(data q m hm rows R F hF hrows v J).movingSupported
  let A:=sourcePrimeSet q hq m hm rows R F hR hF hrows v B J
  let G:=fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h
  let E:=selectedActiveEquiv (splitIndex q hq m hm rows R F hR hF hrows v J) B
  letI : ∀P:sourcePrimeSet q hq m hm rows R F hR hF hrows v B J,
      (Ideal.span {freePrimaryPrime (data q m hm rows R F hF hrows v J).movingIdeal
        (CanonicalCoefficientClass.fixedBaseConductor q*Ideal.span {(72:Eis)}) P.val}:Ideal Eis).IsMaximal:=
    fun P=>freePrimaryPrime_maximal _ _ (data q m hm rows R F hF hrows v J).movingSupported P.val
  exact ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
    @FixedFourierGeometry.stratumBranchTerm _ _ G A (Finset.Subtype.fintype A) _ _
      (sourceStratum q hq m hm rows R F hR hF hrows v h B J) _
      (fun P:A=>freePrimaryPrime_ne_zero lengthScale (freeConductor q) hL P.val)
      (fun P:A=>freePrimaryPrime_good lengthScale (freeConductor q) hL P.val)
      (fun P:A=>(UniqueFactorizationMonoid.normalizedFactors lengthScale).count P.val.val.val%6)
      u (residualLabelVia E l) W X
      (nonzeroDualDilation (sourceDivisor q m R F B l 1) (sourceDivisor q m R F B l 2)
        (sourceDivisor_ne_zero q m R F B l 1) (sourceDivisor_ne_zero q m R F B l 2) x)

end CanonicalRowCompletion.ActualFiber

end

end OAI
