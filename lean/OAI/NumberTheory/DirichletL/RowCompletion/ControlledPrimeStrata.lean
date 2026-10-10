import OAI.NumberTheory.DirichletL.Eisenstein.ReflectionFibers

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

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

def freePrimaryPrime (I Q:Ideal Eis) (P:FreePrimeIndex I Q) : Eis := primaryPrime P.val.val

lemma freePrimaryPrime_ne_zero (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    freePrimaryPrime I Q P≠0 :=
  primaryPrime_ne_zero P.val.val
    (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

lemma freePrimaryPrime_span (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    Ideal.span {freePrimaryPrime I Q P}=P.val.val :=
  (primaryPrime_spec P.val.val (freePrimaryPrime_ne_zero I Q hI P)).2.2.1

lemma freePrimaryPrime_primary (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    lambda^2∣freePrimaryPrime I Q P-1 :=
  (primaryPrime_spec P.val.val (freePrimaryPrime_ne_zero I Q hI P)).2.2.2

lemma freePrimaryPrime_maximal (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal := by
  rw [freePrimaryPrime_span I Q hI P]
  infer_instance

lemma freePrimaryPrime_good (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    lambda∉(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_span I Q hI P]
  exact (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1

lemma freePrimaryPrime_odd (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    ringChar (Eis⧸Ideal.span {freePrimaryPrime I Q P})≠2 := by
  rw [freePrimaryPrime_span I Q hI P]
  exact (supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.2

lemma freePrimaryPrime_injective (I Q:Ideal Eis) (hI:Supported I) :
    Function.Injective (freePrimaryPrime I Q) := by
  intro P R he
  have hh:=congrArg (fun x:Eis=>(Ideal.span {x}:Ideal Eis)) he
  rw [freePrimaryPrime_span I Q hI P,freePrimaryPrime_span I Q hI R] at hh
  exact Subtype.ext (Subtype.ext hh)

lemma freePrimaryPrime_coprime (I Q:Ideal Eis) (hI:Supported I) :
    Pairwise (fun P R:FreePrimeIndex I Q =>
      IsCoprime (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) (Ideal.span {freePrimaryPrime I Q R})) := by
  intro P R hPR
  rw [freePrimaryPrime_span I Q hI P,freePrimaryPrime_span I Q hI R]
  exact freePrimeIndex_pairwise_coprime I Q hPR

lemma freePrimaryPrime_coprime_fixed (I Q:Ideal Eis) (hI:Supported I) (P:FreePrimeIndex I Q) :
    IsCoprime Q (Ideal.span {freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_span I Q hI P]
  exact freePrimeIndex_coprime I Q P

lemma freePrimaryPrime_product_span (I Q:Ideal Eis) (hI:Supported I) :
    Ideal.span {∏P:FreePrimeIndex I Q,freePrimaryPrime I Q P}=
      ∏P:FreePrimeIndex I Q,P.val.val := by
  rw [FiniteGaussPhase.span_finset_prod]
  apply Finset.prod_congr rfl
  intro P _
  exact freePrimaryPrime_span I Q hI P

lemma freePrimaryPrime_product_coprime_fixed (I Q:Ideal Eis) (hI:Supported I) :
    IsCoprime Q (Ideal.span {∏P:FreePrimeIndex I Q,freePrimaryPrime I Q P}:Ideal Eis) := by
  rw [freePrimaryPrime_product_span I Q hI]
  exact freePrimeProduct_coprime I Q

lemma actualSextic_power_transport (P R:Ideal Eis) [P.IsMaximal] [R.IsMaximal]
    (hP:lambda∉P) (hR:lambda∉R) (he:P=R) (j:ℕ) (n:Eis) :
    (actualSextic P hP^j) (Ideal.Quotient.mk P n)=
      (actualSextic R hR^j) (Ideal.Quotient.mk R n) := by
  subst R
  rfl

theorem freePrimeRow_eq_primary_family (I Q:Ideal Eis) (hI:Supported I) (n:Eis) :
    letI : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
      freePrimaryPrime_maximal I Q hI
    freePrimeRow I hI Q n=
      finiteSexticRow (fun P:FreePrimeIndex I Q=>Ideal.span {freePrimaryPrime I Q P})
        (freePrimaryPrime_good I Q hI)
        (fun P=>(normalizedFactors I).count P.val.val%6) n := by
  let : ∀P:FreePrimeIndex I Q,(Ideal.span {freePrimaryPrime I Q P}:Ideal Eis).IsMaximal:=
    freePrimaryPrime_maximal I Q hI
  unfold freePrimeRow finiteSexticRow
  apply Finset.prod_congr rfl
  intro P _
  exact actualSextic_power_transport _ _ _ _ (freePrimaryPrime_span I Q hI P).symm _ n

end CanonicalRowCompletion

namespace FixedRayActiveSet

theorem fourier_inversion_by_active_set {ι:Type*} [Fintype ι]
    (F:ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (ψ:∀i,AddChar (F i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (φ:∀i,F i→ℂ) (x:∀i,F i) :
    (∏i,φ i (x i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0)*
        (∑v:∀i:A,(F i.val)ˣ,
          (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
            (∏i:A,ψ i.val ((v i:F i.val)*x i.val))) := by
  let f:=fun i (a:F i)=>CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) a*ψ i (a*x i)
  have he: (∑h:∀i,F i,∏i,f i (h i))=∏i,φ i (x i):=by
    rw [←Fintype.prod_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact CubicEisenstein.finiteAdditiveFourier_inversion (ψ i) (hψ i) (φ i) (x i)
  rw [←he,sum_by_active_strata]
  apply Finset.sum_congr rfl
  intro A hA
  rw [sum_active_stratum]
  have hz:(∏i∈(Finset.univ:Finset ι)\A,f i 0)=
      ∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0:=by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [f,zero_mul,AddChar.map_zero_eq_one,mul_one]
  rw [hz,mul_comm]
  congr 1
  rw [show (∑v:∀i:A,(F i.val)ˣ,
      (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
        (∏i:A,ψ i.val ((v i:F i.val)*x i.val)))=
      ∑v:∀i:A,(F i.val)ˣ,∏i:A,f i.val (v i) by
    apply Finset.sum_congr rfl
    intro v hv
    exact (Finset.prod_mul_distrib).symm]
  calc
    _=∏i:A,∑u:(F i.val)ˣ,f i.val (u:F i.val):=
      (Finset.prod_coe_sort A (fun i=>∑u:(F i)ˣ,f i (u:F i))).symm
    _=_:=Fintype.prod_sum (fun (i:A) (u:(F i.val)ˣ)=>f i.val (u:F i.val))

end FixedRayActiveSet

open scoped BigOperators Classical ContDiff

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem completedBesselProfile_of_finite_cusp_multiplier
    (Ψ:Eis→*ℂ) (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    {ι:Type*} [Fintype ι] (d:ι→SourceCuspDatum) (w:ι→ℂ)
    (hmult:∀n:Eis,(∑i,w i*ShortDraftTrace.breveE (-cuspFrequency n*(d i).point))=fixedThetaTwist Ψ n)
    (v:ℝ) (hv:0<v) :
    completedBesselProfile Ψ thetaBesselScale v=
      thetaDerivativeScalar⁻¹*∑i,w i*cuspBarProfile cubicSourceConjugateFunction (d i).point v := by
  have hf:=finiteConjugateSource_wirtingerBar (fun i=>(d i).point) w v hv 0
  simp only [hmult] at hf
  have hcseries:=traceTwistedConjugateSource_wirtingerBar c hc (fixedThetaQuotient Ψ c) v hv 0
  simp only [fixedThetaQuotient_mk Ψ Q hperiod c hcQ] at hcseries
  have he:(∑i,w i*cuspBarProfile cubicSourceConjugateFunction (d i).point v)=
      thetaDerivativeScalar*completedBesselProfile Ψ thetaBesselScale v:=by
    rw [←finiteConjugateSource_wirtingerBar_sum (fun i=>(d i).point) w v hv]
    calc
      _=horizontalWirtingerBar (traceTwistedConjugateSource c hc (fixedThetaQuotient Ψ c) v hv) 0:=
        hf.trans hcseries.symm
      _=_:=thetaTwistedSource_wirtingerBar_eq_completedBesselProfile Ψ Q hperiod c hc hcQ v hv
  rw [he,←mul_assoc,inv_mul_cancel₀ thetaDerivativeScalar_ne_zero,one_mul]

theorem completedT_of_finite_cusp_multiplier
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    {ι:Type*} [Fintype ι] (d:ι→SourceCuspDatum) (w:ι→ℂ)
    (hmult:∀n:Eis,(∑i,w i*ShortDraftTrace.breveE (-cuspFrequency n*(d i).point))=fixedThetaTwist Ψ n)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*∑i,w i*(d i).smoothedKernel W X := by
  have hFG (v:ℝ) (hv:0<v) : completedBesselProfile Ψ thetaBesselScale v=
      ∑i,(thetaDerivativeScalar⁻¹*w i)*cuspBarProfile cubicSourceConjugateFunction (d i).point v:=by
    rw [completedBesselProfile_of_finite_cusp_multiplier Ψ Q hperiod c hc hcQ d w hmult v hv,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [completedT_of_finite_cusp_profiles Ψ hΨ Q hperiod c hc hcQ d
    (fun i=>thetaDerivativeScalar⁻¹*w i) hFG W lo hi hlo hsupp hW X hX,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end

open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma theta_lifted_phase (c:Eis) (hc:c≠0) (lift n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(eisLam^2*eisEmbedding lift/eisEmbedding c))=
      quotientTrace c hc (Ideal.Quotient.mk _ lift*Ideal.Quotient.mk _ n) := by
  rw [←map_mul]
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency
  rw [map_mul]
  have hc0:=eisEmbedding_ne_zero hc
  have hl:=eisLam_ne_zero
  field_simp
  linear_combination -(eisEmbedding n*eisEmbedding lift)*TraceLambdaPhase.eisLam_sq

lemma breveE_finset_sum {ι:Type*} (s:Finset ι) (z:ι→ℂ) :
    ShortDraftTrace.breveE (∑i∈s,z i)=∏i∈s,ShortDraftTrace.breveE (z i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,AddChar.map_zero_eq_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]

lemma ControlledStratumArithmetic.datum_fourier_phase {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
    (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(D.datum hN hr hbase s hp hc0 v).point)=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        ∏i,quotientTrace (p i) (hp i) ((v i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ n) := by
  rw [D.datum_point]
  have he:-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i))=
      -cuspFrequency n*(eisEmbedding a0/eisEmbedding c0)+
        ∑i,-cuspFrequency n*(eisLam^2*eisEmbedding (D.lift v i)/eisEmbedding (p i)):=by
    simp only [Finset.mul_sum,neg_mul,mul_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,AddChar.map_add_eq_mul,breveE_finset_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [theta_lifted_phase,D.lift_residue]

end CubicEisenstein

open scoped BigOperators Classical ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def unextractedCuspCoefficient {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  σ m*η m I J*reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J)/
    ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ)

lemma unextractedCuspCoefficient_norm {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (hρ:0<ρ) (hq:1≤q)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (hη:∀m I J,‖η m I J‖≤1) (hσ:∀m,‖σ m‖≤1)
    (m:ℕ) (I J:NonzeroDualIdeal) :
    ‖unextractedCuspCoefficient P hg j e ρ q η σ m I.val J.val‖≤
      (Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
        Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
        Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ))/ρ := by
  let C:ℝ:=Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)
  have hC:0≤C:=by dsimp only [C];positivity
  have hr:0<ramifiedScale ρ q m:=ramifiedScale_pos ρ q hρ (lt_of_lt_of_le zero_lt_one hq) m
  have hn:1≤(Ideal.absNorm I.val:ℝ):=norm_at_least_one I.val I.property
  have hb:1≤(Ideal.absNorm J.val:ℝ):=norm_at_least_one J.val J.property
  have hs:1≤Real.sqrt (Ideal.absNorm I.val:ℝ):=by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    simpa using hn
  have hd:ρ≤ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ) := by
    calc
      ρ≤ramifiedScale ρ q m:=le_mul_of_one_le_right hρ.le (one_le_pow₀ hq)
      _≤ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I.val:ℝ):=le_mul_of_one_le_right hr.le hs
      _≤_:=le_mul_of_one_le_right (by positivity) hb
  have hp:‖σ m‖*‖η m I.val J.val‖≤1:=(mul_le_of_le_one_left (norm_nonneg _)
    (hσ m)).trans (hη m I.val J.val)
  have hh:‖σ m‖*‖η m I.val J.val‖*
      ‖reflectedBranch P hg j e (primaryGenerator I.val) (primaryGenerator J.val)‖≤C := by
    have ht:=mul_le_mul hp (reflectedBranch_norm_bound P hg j e (primaryGenerator I.val) (primaryGenerator J.val))
      (norm_nonneg _) zero_le_one
    simpa only [one_mul] using ht
  rw [unextractedCuspCoefficient,norm_div,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  exact (div_le_div_of_nonneg_right hh (by positivity)).trans
    (div_le_div_of_nonneg_left hC hρ hd)

theorem unextractedCuspCoefficient_summable {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (hρ:0<ρ) (hq:1<q)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (hη:∀m I J,‖η m I J‖≤1) (hσ:∀m,‖σ m‖≤1)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (scale:ℝ) (hscale:0<scale) :
    Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ‖rawDualKernelTerm (Vstar W) scale ρ q (unextractedCuspCoefficient P hg j e ρ q η σ) x‖) := by
  apply rawDualKernelTerm_summable_norm (Vstar W) a b ha (Vstar_support W a b hsupp)
    (Vstar_contDiff W a b ha hsupp hW) scale ρ q
    ((Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ))/ρ)
    hscale hρ hq (by positivity)
  exact unextractedCuspCoefficient_norm P hg j e ρ q hρ hq.le η σ hη hσ

end CompletedGauss

namespace CubicEisenstein

section
open ActualEisensteinCubic CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

def stratumBranchTerm (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ)
    (u:Eisˣ) (e:ι→Fin 3) (W:ℝ→ℂ) (X:ℝ)
    (x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal) : ℂ :=
  rawDualKernelTerm (Vstar W) (X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))
    1 completedRamifiedStep
    (unextractedCuspCoefficient (fun i=>Ideal.span {p i}) hg j e 1 completedRamifiedStep
      (G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u)
      (D.modelRowPhase G.shape hp hg j u)) x

theorem stratumBranchTerm_summable (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (u:Eisˣ) (e:ι→Fin 3) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hsupp:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>‖G.stratumBranchTerm D hp hg j u e W X x‖) := by
  have hn:0<(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz=>
      (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
        (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hlevel:=G.levelScale_pos
  apply unextractedCuspCoefficient_summable (fun i=>Ideal.span {p i}) hg j e 1 completedRamifiedStep
    (by norm_num) completedRamifiedStep_gt_one _ _ (G.array_norm_le_one _ u)
    (fun m=>(D.modelRowPhase_norm hN hr G.primary G.shape hp hg hchar j hj u m).le)
    W a b ha hsupp hW _ (by positivity)

theorem stratumBranchTerm_fubini (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑'t:CuspIdealIndex,∑e:ι→Fin 3,G.stratumBranchTerm D hp hg j t.1 e W X t.2)=
      ∑'u:Eisˣ,∑e:ι→Fin 3,∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        G.stratumBranchTerm D hp hg j u e W X x := by
  let:Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  have hs:=G.stratumBranchTerm_summable D hN hr hp hg hchar j hj
    (W:=W) (a:=a) (b:=b) (ha:=ha) (hsupp:=hsupp) (hW:=hW) (X:=X) (hX:=hX)
  have hu (u:Eisˣ):Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ‖∑e:ι→Fin 3,G.stratumBranchTerm D hp hg j u e W X x‖) := by
    have hb:Summable (fun x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal=>
      ∑e:ι→Fin 3,‖G.stratumBranchTerm D hp hg j u e W X x‖) :=
      (hasSum_sum (fun e _=>(hs u e).hasSum)).summable
    exact hb.of_nonneg_of_le (fun _=>norm_nonneg _) (fun _=>norm_sum_le _ _)
  have hall:Summable (fun t:CuspIdealIndex=>
      ‖∑e:ι→Fin 3,G.stratumBranchTerm D hp hg j t.1 e W X t.2‖) :=
    (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr ⟨hu,Summable.of_finite⟩
  rw [hall.of_norm.tsum_prod]
  apply tsum_congr
  intro u
  exact Summable.tsum_finsetSum (fun e _=>(hs u e).of_norm)

end FixedFourierGeometry
end

open ActualEisensteinCubic CompletedGauss CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O
namespace FixedFourierGeometry
variable {c:Eis} {h:Eis⧸Ideal.span {c}} (G:FixedFourierGeometry c h)
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N:Eis}

theorem reflectedValue_eq_branch_sums (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.reflectedValue G.shape hp G.denominator_ne_zero hg j W X=
      fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:ι→Fin 3,∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
          G.stratumBranchTerm D hp hg j u e W X x := by
  rw [G.reflectedValue_eq_model_series]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  rw [←G.stratumBranchTerm_fubini D hN hr hp hg hchar j hj W a b ha hsupp hW X hX]
  let v:G.PhaseResidue:=Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)
  let weight:CuspIdealIndex→ℂ:=fun t=>
    D.modelRowPhase G.shape hp hg j t.1 t.2.1*
      (∑e:ι→Fin 3,reflectedBranch (fun i=>Ideal.span {p i}) hg j e
        (primaryGenerator t.2.2.1.val) (primaryGenerator t.2.2.2.val)) /
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ)*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((X/(G.levelScale*(Ideal.absNorm (Ideal.span {∏i,p i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep t.2.1)^3*
          (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ)^3)
  calc
    _=∑'t:ThetaFullIndex,G.array v t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      weight (thetaFullToIdealIndex t) := by
        apply tsum_congr
        intro t
        dsimp only [weight,thetaFullToIdealIndex,primaryCubePairToMellinIndex]
        rw [←Finset.mul_sum]
        ring
    _=∑'t:CuspIdealIndex,G.array v t.1 t.2.1 t.2.2.1.val t.2.2.2.val*weight t :=
      (fixedCuspArrayWithPhase_tsum_full_index (fun _=>G.shape.index) (G.staticPhase v) weight).symm
    _=_ := by
      apply tsum_congr
      intro t
      dsimp only [weight,stratumBranchTerm,rawDualKernelTerm,unextractedCuspCoefficient]
      simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      dsimp only [v,ramifiedScale]
      ring

theorem stratumBranchTerm_tsum_extract (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hp:∀i,p i≠0) (hg:∀i,lambda∉Ideal.span {p i})
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (j:ι→ℕ) (e:ι→Fin 3) (u:Eisˣ) (W:ℝ→ℂ) (X:ℝ) :
    let A:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1
    let B:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2
    let hA:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 1
    let hB:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 2
    (∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,G.stratumBranchTerm D hp hg j u e W X x)=
      ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
        G.stratumBranchTerm D hp hg j u e W X (nonzeroDualDilation A B hA hB x) := by
  dsimp only
  apply tsum_nonzeroDualDilation
  intro x hx
  dsimp only [stratumBranchTerm,rawDualKernelTerm,unextractedCuspCoefficient] at hx
  have hnum:= (div_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).1).1
  have hpair:G.array (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u x.1 x.2.1.val x.2.2.val*
      reflectedBranch (fun i=>Ideal.span {p i}) hg j e
        (primaryGenerator x.2.1.val) (primaryGenerator x.2.2.val)≠0 :=
    mul_ne_zero (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnum).1).2 (mul_ne_zero_iff.mp hnum).2
  have hs:=fixedCuspBranchNumerator_support (fun i=>Ideal.span {p i}) hg hcop j e
    G.shape.index u (G.staticPhase (Ideal.Quotient.mk _ (-(D.matrix (fun _=>1) 1 1)*D.U)) u)
    x.1 x.2.1.val x.2.2.val hpair
  exact ⟨hs.1,hs.2.1⟩

theorem smoothedValue_eq_extracted_branch_sums
    (D:ControlledStratumArithmetic p N G.a0 G.c0 G.mode)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hN:(9:Eis)*G.c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hp:∀i,p i≠0)
    (hcop:Pairwise (fun i k=>IsCoprime (Ideal.span {p i}) (Ideal.span {p k})))
    (hg:∀i,lambda∉Ideal.span {p i})
    (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hN hr G.primary G.shape hp G.denominator_ne_zero hg j W X=
      fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*
        ∑'u:Eisˣ,∑e:ι→Fin 3,
          let A:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 1
          let B:=reflectionExtractedDivisor (fun i=>Ideal.span {p i}) j e 2
          let hA:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 1
          let hB:=reflectionExtractedDivisor_ne_zero (fun i=>Ideal.span {p i}) (fun _i=>NeZero.ne _) j e 2
          ∑'x:ℕ×NonzeroDualIdeal×NonzeroDualIdeal,
            G.stratumBranchTerm D hp hg j u e W X (nonzeroDualDilation A B hA hB x) := by
  rw [D.smoothed_eq_reflected hN hr G.primary G.shape hp G.denominator_ne_zero hcop hg hchar
    j hj W a b ha hsupp hW X hX,
    G.reflectedValue_eq_branch_sums D hN hr hp hg hchar j hj W a b ha hsupp hW X hX]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*G.shape.stratumShapeFactor (G.c0*∏i,p i)*z)
  apply tsum_congr
  intro u
  apply Finset.sum_congr rfl
  intro e he
  exact G.stratumBranchTerm_tsum_extract D hp hg hcop j e u W X

end FixedFourierGeometry
end CubicEisenstein

open scoped BigOperators Classical

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma freePrimaryPrime_coprime_completion (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (P:FreePrimeIndex I Q) : IsCoprime ((9:Eis)*c) (freePrimaryPrime I Q P) := by
  have h9:IsCoprime (9:Eis) (freePrimaryPrime I Q P):=
    (ShortDraftCRT.primary_coprime_nine _ (freePrimaryPrime_primary I Q hI P)).symm
  have h9ideal:IsCoprime (Ideal.span {(9:Eis)}:Ideal Eis)
      (Ideal.span {freePrimaryPrime I Q P}):=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr h9
  have hcideal:IsCoprime (Ideal.span {c}:Ideal Eis)
      (Ideal.span {freePrimaryPrime I Q P}):=by
    rw [hcQ]
    exact h9ideal.mul_left (freePrimaryPrime_coprime_fixed I Q hI P)
  exact h9.mul_left ((Ideal.isCoprime_span_singleton_iff _ _).mp hcideal)

theorem exists_freePrimary_controlled_stratum (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex I Q)) :
    Nonempty (ControlledStratumArithmetic
      (fun i:A=>freePrimaryPrime I Q i.val) ((9:Eis)*c) G.a0 G.c0 G.mode) := by
  let : ∀i:A,(Ideal.span {freePrimaryPrime I Q i.val}:Ideal Eis).IsMaximal:=
    fun i=>freePrimaryPrime_maximal I Q hI i.val
  apply exists_controlledStratumArithmetic
    (fun i:A=>freePrimaryPrime I Q i.val)
    (fun i=>freePrimaryPrime_ne_zero I Q hI i.val)
  · intro i j hij
    exact freePrimaryPrime_coprime I Q hI (fun he=>hij (Subtype.ext he))
  · exact fun i=>freePrimaryPrime_primary I Q hI i.val
  · exact G.denominator_ne_zero
  · exact mul_dvd_mul_left 9 G.denominator_dvd
  · exact G.primary
  · exact G.coprime
  · exact fun i=>freePrimaryPrime_coprime_completion I Q hI c hcQ i.val

noncomputable def freePrimaryControlledStratum (I Q:Ideal Eis) (hI:Supported I)
    (c:Eis) (hcQ:(Ideal.span {c}:Ideal Eis)=Ideal.span {(9:Eis)}*Q)
    (h:Eis⧸Ideal.span {c}) (G:FixedFourierGeometry c h)
    (A:Finset (FreePrimeIndex I Q)) :
    ControlledStratumArithmetic
      (fun i:A=>freePrimaryPrime I Q i.val) ((9:Eis)*c) G.a0 G.c0 G.mode :=
  Classical.choice (exists_freePrimary_controlled_stratum I Q hI c hcQ h G A)

end CanonicalRowCompletion

end

end OAI
