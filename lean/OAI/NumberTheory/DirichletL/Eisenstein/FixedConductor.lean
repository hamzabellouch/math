import OAI.NumberTheory.DirichletL.GaussSum.ReflectionPool

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

open scoped Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

lemma divisor_principal_norm_le (c0 c:Eis) (hc:c≠0) (hdiv:c0∣c) :
    (Ideal.absNorm (Ideal.span {c0}):ℝ)≤(Ideal.absNorm (Ideal.span {c}):ℝ) := by
  have hp:0<Ideal.absNorm (Ideal.span {c}):=Nat.pos_of_ne_zero (by
    intro hz
    exact hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hd:Ideal.absNorm (Ideal.span {c0})∣Ideal.absNorm (Ideal.span {c}) := by
    obtain ⟨d,hd⟩:=hdiv
    rw [hd,←Ideal.span_singleton_mul_span_singleton,map_mul]
    exact dvd_mul_right _ _
  exact_mod_cast Nat.le_of_dvd hp hd

def fixedCuspLevelBound (c:Eis) : ℝ :=
  243*(Ideal.absNorm (Ideal.span {c}):ℝ)^2

def fixedCuspLevelScale (j:Fin 3) (c0:Eis) : ℝ :=
  27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0}):ℝ)^2

lemma fixedCuspLevelBound_ge_one (c:Eis) (hc:c≠0) : 1≤fixedCuspLevelBound c := by
  have hp:1≤Ideal.absNorm (Ideal.span {c}):=Nat.one_le_iff_ne_zero.mpr (by
    intro hz
    exact hc (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hr:(1:ℝ)≤(Ideal.absNorm (Ideal.span {c}):ℝ):=by exact_mod_cast hp
  unfold fixedCuspLevelBound
  nlinarith

lemma fixedCuspLevelScale_pos (j:Fin 3) (c0:Eis) (hc0:c0≠0) : 0<fixedCuspLevelScale j c0 := by
  have hp:0<Ideal.absNorm (Ideal.span {c0}):=Nat.pos_of_ne_zero (by
    intro hz
    exact hc0 (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz)))
  have hr:(0:ℝ)<(Ideal.absNorm (Ideal.span {c0}):ℝ):=by exact_mod_cast hp
  have hs:=sourceCuspScale_pos j
  unfold fixedCuspLevelScale
  positivity

lemma fixedCuspLevelScale_le (j:Fin 3) (c0 c:Eis) (hc:c≠0) (hdiv:c0∣c) :
    fixedCuspLevelScale j c0≤fixedCuspLevelBound c := by
  have hd:=divisor_principal_norm_le c0 c hc hdiv
  have hs:(sourceCuspScale j)^2≤9:=by fin_cases j <;> norm_num [sourceCuspScale]
  unfold fixedCuspLevelScale fixedCuspLevelBound
  calc
    27*(sourceCuspScale j)^2*(Ideal.absNorm (Ideal.span {c0}):ℝ)^2≤
      27*9*(Ideal.absNorm (Ideal.span {c}):ℝ)^2:=by gcongr
    _=_:=by ring

end

section
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

lemma A4_traceLambda_pow_four : ramifiedTraceLambda^4=(9:Eis) := by
  apply eisEmbedding_injective
  rw [map_pow,map_ofNat,ramifiedEmbedding_traceLambda]
  calc
    _=(eisLam^2)^2:=by ring
    _=9:=by rw [TraceLambdaPhase.eisLam_sq];norm_num

structure PrincipalStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) (N a0 c0:Eis) where
  lift : (∀i,(Eis⧸Ideal.span {p i})ˣ)→ι→Eis
  lift_period : ∀v i,N^2∣lift v i
  lift_residue : ∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (lift v i)=(v i:Eis⧸Ideal.span {p i})
  U : Eis
  w : Eis
  bezout : U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1
  sigma : ∀i,(Eis⧸Ideal.span {p i})ˣ
  epsilon : ∀i,(Eis⧸Ideal.span {p i})ˣ
  sigma_value : ∀i,(sigma i:Eis⧸Ideal.span {p i})=
    Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)
  epsilon_value : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
    (sigma i:Eis⧸Ideal.span {p i})*(epsilon i:Eis⧸Ideal.span {p i})=-1
  gamma : (∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree
  numerator : ∀v,(gamma v:SL(2,Eis)) 0 0=finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  denominator : ∀v,(gamma v:SL(2,Eis)) 1 0=c0*∏i,p i
  numerator_fixed : ∀v,(9:Eis)*c0∣(gamma v:SL(2,Eis)) 0 0-(gamma (fun _=>1):SL(2,Eis)) 0 0
  inverse_fixed : ∀v,ramifiedTraceLambda^3*c0∣(gamma v:SL(2,Eis)) 1 1-(gamma (fun _=>1):SL(2,Eis)) 1 1

theorem exists_principalStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (N a0 c0:Eis) (hc0:c0≠0) (hc3:(3:Eis)∣c0)
    (hN:(9:Eis)*c0∣N) (ha0:lambda^2∣a0-1) (hac:IsCoprime a0 c0)
    (hNp:∀i,IsCoprime N (p i)) :
    Nonempty (PrincipalStratumArithmetic p N a0 c0) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have hcN:c0∣N:=(dvd_mul_left c0 9).trans hN
  have hD9:ramifiedTraceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [←A4_traceLambda_pow_four]
    ring
  have hDN:ramifiedTraceLambda^3*c0∣N:=hD9.trans hN
  have hl9:ramifiedTraceLambda∣(9:Eis) := by
    rw [←A4_traceLambda_pow_four]
    exact dvd_pow_self _ (by decide)
  have hlN:ramifiedTraceLambda∣N:=hl9.trans h9N
  have hstdN:lambda^2∣N:=lambda_sq_dvd_three.trans
    ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N)
  let r:Eis:=∏i,p i
  have hr:lambda^2∣r-1:=primary_finset_product Finset.univ p (fun i _=>hprimary i)
  have hNr:IsCoprime N r:=IsCoprime.prod_right (fun i _=>hNp i)
  have hrNc:IsCoprime r (N*c0):=hNr.symm.mul_right
    (hNr.symm.of_isCoprime_of_dvd_right hcN)
  obtain ⟨U,w,huw⟩:=hNr.symm.of_isCoprime_of_dvd_right hDN
  have hbez:U*r+(ramifiedTraceLambda^3*w)*c0=1 := by
    linear_combination huw
  obtain ⟨σ,ε,hσ,hε⟩:=exists_A4_local_units p hp hcop c0 U w hbez
  have hlf (v:∀i,(Eis⧸Ideal.span {p i})ˣ):=
    exists_strong_unit_frequency_lifts N p hNp v
  choose lift hlift hres hlcop using hlf
  let a:=fun v=>finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  have hap:∀v,lambda^2∣a v-1 := by
    intro v
    have hfixed:N∣a v-a0*r:=finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (lift v)
      (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (hlift v i))
    have hbase:=primary_mul a0 r ha0 hr
    convert dvd_add (hstdN.trans hfixed) hbase using 1 ; ring
  have hpairs:Pairwise (Function.onFun IsCoprime p):=by
    intro i k hik
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hik)
  have hacop:∀v,IsCoprime (a v) (c0*r) := by
    intro v
    exact finiteCrossNumerator_coprime a0 c0 ramifiedTraceLambda p (lift v) hac hpairs
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hcN)
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hlN) (hlcop v)
  obtain ⟨b,d,C,hdet,hb,hd,hmat⟩:=exists_primary_numerator_sector_completions
    N c0 hc0 h9N (fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) a (fun _=>r)
    hap (fun _=>hr) hacop (fun _=>hrNc)
    (fun v z _=>finiteCrossNumerator_fixed_sector N a0 c0 ramifiedTraceLambda p (lift v)
      p (lift z) hcN (hlift v) (hlift z) (by simp))
    (fun _ _ _=>by simp)
  let mat:=fun v=>controlledCompletionMatrix (a v) (b v) (c0*r) (d v) (hdet v)
  have hm:∀v,mat v∈levelThree:=by
    intro v
    apply A3_principal_mem_levelThree (mat v)
    · exact three_dvd_primary_sub_one (a v) (hap v)
    · exact (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans (hb v)
    · exact dvd_mul_of_dvd_left hc3 r
    · exact hd v
  let gamma:=fun v=>(⟨mat v,hm v⟩:levelThree)
  have hentry (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i j:Fin 2):
      N∣(mat v) i j-(mat (fun _=>1)) i j := by
    have he:=congrArg (fun T:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {N})=>T i j)
      ((hmat v).trans (hmat (fun _=>1)).symm)
    change Ideal.Quotient.mk (Ideal.span {N}) ((mat v) i j)=
      Ideal.Quotient.mk (Ideal.span {N}) ((mat (fun _=>1)) i j) at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  exact ⟨{
    lift := lift
    lift_period := hlift
    lift_residue := hres
    U := U
    w := w
    bezout := hbez
    sigma := σ
    epsilon := ε
    sigma_value := hσ
    epsilon_value := hε
    gamma := gamma
    numerator := fun _=>rfl
    denominator := fun _=>rfl
    numerator_fixed := fun v=>hN.trans (hentry v 0 0)
    inverse_fixed := fun v=>hDN.trans (hentry v 1 1)
  }⟩

lemma PrincipalStratumArithmetic.frequency_congruence {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} (D:PrincipalStratumArithmetic p N a0 c0)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) ((D.gamma v:SL(2,Eis)) 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,finiteCrossNumerator_local,D.sigma_value,D.lift_residue]

end

open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic
open CubicKubota CubicJacobiGlobal ShortDraftCusp LocalReflectionBrackets FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace PrincipalStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis}

noncomputable def datum (D:PrincipalStratumArithmetic p N a0 c0)
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : SourceCuspDatum :=
  principalCuspDatum (D.gamma v) (by
    rw [D.denominator];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

lemma datum_point (D:PrincipalStratumArithmetic p N a0 c0)
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.datum hp hc0 v).point=eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i) := by
  rw [SourceCuspDatum.point,datum,principalCuspDatum_matrix,
    integralComplexMatrix_apply,integralComplexMatrix_apply,D.numerator,D.denominator]
  simpa only [ramifiedEmbedding_traceLambda] using
    ShortDraftCRT.finiteCrossNumerator_fraction a0 c0 ramifiedTraceLambda p (D.lift v) hc0 hp

noncomputable def smoothedValue (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  exact ∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
    (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i))*
    (D.datum hp hc0 v).smoothedKernel W X

noncomputable def reflectedValue (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hg:∀i,lambda∉Ideal.span {p i}) (j:ι→ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ := by
  letI (i:ι):Field (Eis⧸Ideal.span {p i}):=Ideal.Quotient.field _
  letI (i:ι):Fintype (Eis⧸Ideal.span {p i}):=Fintype.ofFinite _
  let c:=c0*∏i,p i
  let Q:ℝ:=‖eisEmbedding c‖^2
  exact fixedRadialCoefficientScalar*∑'t:ThetaFullIndex,
    ((fixedConjugateCuspArray 0 t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
      sourceFrequencyAngle (thetaFullFrequency t))/
      ((ramifiedScale 1 completedRamifiedStep t.2.1*
        Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
    CubicReflectionKernel.paperKernel (Vstar W)
      (X*sourceCuspRadialLength (thetaFullFrequency t)/(27*Q^2))*
    (-(Q:ℂ)/(eisEmbedding c)^2*
      ((star (eisEmbedding (symbol c0 ((D.gamma (fun _=>1):SL(2,Eis)) 0 0)))*
        A4BadPhase c0 hc0 ((D.gamma (fun _=>1):SL(2,Eis)) 1 1) D.U (ramifiedTraceLambda*thetaFullFrequency t))*
      ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
        phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)*
        bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
          (Ideal.Quotient.mk _ (ramifiedTraceLambda*thetaFullFrequency t))))

theorem smoothed_eq_reflected (D:PrincipalStratumArithmetic p N a0 c0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0) (hc0:c0≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hr:lambda^2∣(∏i,p i)-1) (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    D.smoothedValue hp hc0 hg j W X=D.reflectedValue hp hc0 hg j W X := by
  simpa only [smoothedValue,reflectedValue,datum] using
    principal_stratum_smoothed p hp hcop hg hchar c0 D.U D.w hc0 hr D.bezout
      D.gamma D.denominator D.numerator_fixed D.inverse_fixed D.sigma D.epsilon
      D.frequency_congruence D.epsilon_value j hj W lo hi hlo hsupp hW X hX

end PrincipalStratumArithmetic

theorem exists_constructed_principal_reflection {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (N a0 c0:Eis) (hc0:c0≠0) (hc3:(3:Eis)∣c0)
    (hN:(9:Eis)*c0∣N) (ha0:lambda^2∣a0-1) (hac:IsCoprime a0 c0)
    (hNp:∀i,IsCoprime N (p i)) :
    ∃D:PrincipalStratumArithmetic p N a0 c0,
      ∀j:ι→ℕ,(∀i,j i<6)→∀(W:ℝ→ℂ)(lo hi:ℝ),0<lo→
        Function.support W⊆Set.Icc lo hi→ContDiff ℝ ∞ W→∀X:ℝ,0<X→
        D.smoothedValue hp hc0 hg j W X=D.reflectedValue hp hc0 hg j W X := by
  obtain ⟨D⟩:=exists_principalStratumArithmetic p hp hcop hprimary N a0 c0 hc0 hc3 hN ha0 hac hNp
  refine ⟨D,?_⟩
  intro j hj W lo hi hlo hsupp hW X hX
  exact D.smoothed_eq_reflected hp hc0 hcop hg hchar
    (primary_finset_product Finset.univ p (fun i _=>hprimary i)) j hj W lo hi hlo hsupp hW X hX

end CubicEisenstein

open scoped BigOperators Classical

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

abbrev BasePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I // Q≤P.val}
abbrev FreePrimeIndex (I Q:Ideal Eis) := {P:PrimeIndex I // ¬Q≤P.val}

def basePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:BasePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

def freePrimeRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) : Eis→*ℂ where
  toFun n:=∏P:FreePrimeIndex I Q,
    (actualSextic P.val.val ((supported_factors_good I hI P.val.val
      (Multiset.mem_toFinset.mp P.val.property)).2.1)^((normalizedFactors I).count P.val.val%6))
        (Ideal.Quotient.mk P.val.val n)
  map_one' := by simp only [map_one,Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul,Finset.prod_mul_distrib]

lemma basePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖basePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:BasePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma freePrimeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    ‖freePrimeRow I hI Q n‖≤1 := by
  change ‖∏P:FreePrimeIndex I Q,_‖≤1
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro P hP;exact norm_nonneg _
  · intro P hP;exact FiniteRayExpansion.norm_char_le_one _ _

lemma basePrimeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) :
    CanonicalCoefficientClass.FactorsModulo Q (basePrimeRow I hI Q) := by
  intro x y hxy
  change (∏P:BasePrimeIndex I Q,_)=∏P:BasePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  have he:Ideal.Quotient.mk P.val.val x=Ideal.Quotient.mk P.val.val y:=
    Ideal.Quotient.eq.mpr (P.property hxy)
  rw [he]

lemma idealRowHom_fixed_conductor_split (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    idealRowHom n I=basePrimeRow I hI Q n*freePrimeRow I hI Q n := by
  rw [idealRowHom_eq_prime_count_product I hI n]
  exact (Fintype.prod_subtype_mul_prod_subtype (fun P:PrimeIndex I=>Q≤P.val)
    (fun P:PrimeIndex I=>(actualSextic P.val ((supported_factors_good I hI P.val
      (Multiset.mem_toFinset.mp P.property)).2.1)^((normalizedFactors I).count P.val%6))
      (Ideal.Quotient.mk P.val n))).symm

lemma freePrimeIndex_pairwise_coprime (I Q:Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (fun P:FreePrimeIndex I Q=>P.val.val)) := by
  intro P R hPR
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPR (Subtype.ext (Subtype.ext he)))

lemma freePrimeIndex_coprime (I Q:Ideal Eis) (P:FreePrimeIndex I Q) :
    IsCoprime Q P.val.val := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra ht
  have he:P.val.val=Q⊔P.val.val:=
    (show P.val.val.IsMaximal from inferInstance).eq_of_le ht le_sup_right
  exact P.property (le_sup_left.trans he.symm.le)

lemma freePrimeProduct_coprime (I Q:Ideal Eis) :
    IsCoprime Q (∏P:FreePrimeIndex I Q,P.val.val) :=
  IsCoprime.prod_right (fun P _=>freePrimeIndex_coprime I Q P)

lemma freePrimeRow_eq_principalSexticRow (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) (n:Eis) :
    freePrimeRow I hI Q n=
      principalSexticRow (fun P:FreePrimeIndex I Q=>P.val.val) (freePrimeIndex_pairwise_coprime I Q)
        (fun P=>(supported_factors_good I hI P.val.val (Multiset.mem_toFinset.mp P.val.property)).2.1)
        (fun P=>(normalizedFactors I).count P.val.val%6)
        (finitePrimeModulus (fun P:FreePrimeIndex I Q=>P.val.val))
        (span_finitePrimeModulus _) (Ideal.Quotient.mk _ n) := by
  rw [principalSexticRow_mk]
  rfl

theorem fixed_conductor_absorb_shared_primes (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (hφn:∀n,‖φ n‖≤1) :
    CanonicalCoefficientClass.FactorsModulo Q (φ*basePrimeRow I hI Q) ∧
    (∀n,‖(φ*basePrimeRow I hI Q) n‖≤1) ∧
    IsCoprime Q (∏P:FreePrimeIndex I Q,P.val.val) ∧
    (∀n,φ n*idealRowHom n I=(φ*basePrimeRow I hI Q) n*freePrimeRow I hI Q n) := by
  refine ⟨?_,?_,freePrimeProduct_coprime I Q,?_⟩
  · intro x y hxy
    change φ x*basePrimeRow I hI Q x=φ y*basePrimeRow I hI Q y
    rw [hφ x y hxy,basePrimeRow_periodic I hI Q x y hxy]
  · intro n
    change ‖φ n*basePrimeRow I hI Q n‖≤1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφn n)).trans (basePrimeRow_norm I hI Q n)
  · intro n
    rw [idealRowHom_fixed_conductor_split I hI Q n]
    exact (mul_assoc _ _ _).symm

end
section

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

lemma freePrimeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis) :
    CanonicalCoefficientClass.FactorsModulo (∏P:FreePrimeIndex I Q,P.val.val) (freePrimeRow I hI Q) := by
  intro x y hxy
  change (∏P:FreePrimeIndex I Q,_)=∏P:FreePrimeIndex I Q,_
  apply Finset.prod_congr rfl
  intro P hP
  have hm:x-y∈P.val.val:=
    (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ P))) hxy
  rw [Ideal.Quotient.eq.mpr hm]

lemma fixedFreeRow_periodic (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) :
    CanonicalCoefficientClass.FactorsModulo (Q*(∏P:FreePrimeIndex I Q,P.val.val))
      (φ*freePrimeRow I hI Q) := by
  intro x y hxy
  change φ x*freePrimeRow I hI Q x=φ y*freePrimeRow I hI Q y
  rw [hφ x y (Ideal.mul_le_left hxy),freePrimeRow_periodic I hI Q x y (Ideal.mul_le_right hxy)]

lemma fixedFreeRow_norm (I:Ideal Eis) (hI:Supported I) (Q:Ideal Eis)
    (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (n:Eis) : ‖(φ*freePrimeRow I hI Q) n‖≤1 := by
  change ‖φ n*freePrimeRow I hI Q n‖≤1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hφ n)).trans (freePrimeRow_norm I hI Q n)

theorem exists_actual_coprime_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=φ n*freePrimeRow I hI (Q*Ideal.span {(72:Eis)}) n) := by
  obtain ⟨I,hI,φ,hφ,hφn,hrow⟩:=exists_fixed_twist_principal_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  obtain ⟨hperiod,hnorm,hcop,hprod⟩:=fixed_conductor_absorb_shared_primes I hI _ φ hφ hφn
  refine ⟨I,hI,φ*basePrimeRow I hI _,hperiod,hnorm,hcop,?_⟩
  intro n hpn
  rw [hrow n hpn,←idealRowHom_eq_principalSexticRow I hI n,hprod n]

theorem exists_actual_coprime_completed_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hQ:Q≠0) (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      IsCoprime (Q*Ideal.span {(72:Eis)})
        (∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val) ∧
      (Q*Ideal.span {(72:Eis)}*(∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val))≠0 ∧
      CanonicalCoefficientClass.FactorsModulo
        (Q*Ideal.span {(72:Eis)}*(∏P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)}),P.val.val))
        (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) ∧
      (∀n,‖(φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) n‖≤1) ∧
      (∀W X,completedT (rowTwist Ψ m f z) W X=
        completedT (φ*freePrimeRow I hI (Q*Ideal.span {(72:Eis)})) W X) := by
  obtain ⟨I,hI,φ,hφ,hφn,hcop,hrow⟩:=exists_actual_coprime_row Ψ Q hΨ hΨnorm m f z hm hf hz hmLam hm2
  refine ⟨I,hI,φ,hφ,hφn,hcop,?_,fixedFreeRow_periodic I hI _ φ hφ,
    fixedFreeRow_norm I hI _ φ hφn,?_⟩
  · apply mul_ne_zero
    · apply mul_ne_zero hQ
      simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
      norm_num
    · exact finite_prime_product_ne_bot (fun P:FreePrimeIndex I (Q*Ideal.span {(72:Eis)})=>P.val.val)
  · intro W X
    exact completedT_congr_primary _ _ hrow W X

def fixedQuotientValue (Q:Ideal Eis) (φ:Eis→*ℂ) (x:Eis⧸Q) : ℂ := φ (Quotient.out x)

lemma fixedQuotientValue_mk (Q:Ideal Eis) (φ:Eis→*ℂ)
    (hφ:CanonicalCoefficientClass.FactorsModulo Q φ) (n:Eis) :
    fixedQuotientValue Q φ (Ideal.Quotient.mk Q n)=φ n :=
  hφ _ _ (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out _))

lemma fixedQuotientValue_norm (Q:Ideal Eis) (φ:Eis→*ℂ) (hφ:∀n,‖φ n‖≤1) (x:Eis⧸Q) :
    ‖fixedQuotientValue Q φ x‖≤1 := hφ _

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
open ConcretePrimeRowBridge
local notation "Eis" => ActualEisensteinCubic.O

def goodMaskMovingIdeal (g r:Eis) : Ideal Eis := (Ideal.span {g})^6*Ideal.span {r}

lemma goodMaskMovingIdeal_supported (g r:Eis)
    (hg:Supported (Ideal.span {g})) (hr:Supported (Ideal.span {r})) :
    Supported (goodMaskMovingIdeal g r) := by
  exact (supported_mul_iff _ _).mpr ⟨supported_pow hg 6,hr⟩

lemma good_odd_prime_two_not_mem (P:Ideal Eis) [P.IsMaximal]
    (hodd:ringChar (Eis⧸P)≠2) : (2:Eis)∉P := by
  intro ht
  have he:=maximal_ideal_eq_span_of_mem P inferInstance (2:Eis) twoIdeal_maximal ht
  exact hodd (he ▸ twoIdeal_characteristic)

lemma count_span_eq_zero_of_not_mem (P:Ideal Eis) (x:Eis) (hx:x∉P) :
    (normalizedFactors (Ideal.span {x})).count P=0 := by
  apply Multiset.count_eq_zero.mpr
  intro hm
  have h0:(Ideal.span {x}:Ideal Eis)≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mpr
    intro he
    exact hx (he ▸ P.zero_mem)
  exact hx (Ideal.dvd_span_singleton.mp
    ((UniqueFactorizationMonoid.mem_normalizedFactors_iff h0).mp hm).2)

lemma good_factor_count (P:Ideal Eis) [P.IsMaximal]
    (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    (normalizedFactors (Ideal.span {u.val*lambda^a*(2:Eis)^b*r})).count P=
      (normalizedFactors (Ideal.span {r})).count P := by
  have hl:(Ideal.span {lambda}:Ideal Eis)≠0:=
    Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
  have ht:(Ideal.span {(2:Eis)}:Ideal Eis)≠0:=Ideal.span_singleton_eq_bot.not.mpr (by norm_num)
  have hcl:=count_span_eq_zero_of_not_mem P lambda hgood
  have hct:=count_span_eq_zero_of_not_mem P 2 (good_odd_prime_two_not_mem P hodd)
  rw [show u.val*lambda^a*(2:Eis)^b*r=u.val*(lambda^a*(2:Eis)^b*r) by ring,
    Ideal.span_singleton_mul_left_unit u.isUnit,
    ←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
    ←Ideal.span_singleton_pow,←Ideal.span_singleton_pow,
    normalizedFactors_mul (mul_ne_zero (pow_ne_zero _ hl) (pow_ne_zero _ ht)) hr.1,
    normalizedFactors_mul (pow_ne_zero _ hl) (pow_ne_zero _ ht)]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,hcl,hct,mul_zero,zero_add]

theorem goodMaskMovingIdeal_count (I F:Ideal Eis) (hI:I≠0) (hF:F≠0)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P=
      6*(normalizedFactors (Ideal.span {m})).count P+
        4*(normalizedFactors F).count P+(normalizedFactors I).count P := by
  have hmc:(normalizedFactors (Ideal.span {m})).count P=(normalizedFactors (Ideal.span {g})).count P:=by
    rw [hm]
    exact good_factor_count P hgood hodd um am bm g hg
  have hrc:(normalizedFactors (Ideal.span {r})).count P=
      4*(normalizedFactors F).count P+(normalizedFactors I).count P:=by
    have hh:=good_factor_count P hgood hodd u a b r hr
    rw [←hx,←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_pow,hf,hz,
      normalizedFactors_mul (pow_ne_zero 4 hF) hI] at hh
    simpa only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul] using hh.symm
  rw [goodMaskMovingIdeal,normalizedFactors_mul (pow_ne_zero 6 hg.1) hr.1]
  simp only [Multiset.count_add,normalizedFactors_pow,Multiset.count_nsmul,←hmc,hrc]
  omega

lemma squarefree_prime_count_indicator (F P:Ideal Eis) (hF:Squarefree F) (hP:Prime P) :
    (normalizedFactors F).count P=if P∣F then 1 else 0 := by
  have hle:=Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hF.ne_zero).mp hF) P
  by_cases hPF:P∣F
  · rw [ite_eq_left hPF]
    have hp:=Multiset.count_pos.mpr
      ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mpr ⟨hP,hPF⟩)
    omega
  · rw [ite_eq_right hPF]
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hPF ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hF.ne_zero).mp hm).2

theorem goodMaskMovingIdeal_exponent (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m f z:Eis) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P%6=completedLocalExponent I F P := by
  rw [goodMaskMovingIdeal_count I F hI hF.ne_zero m f z hf hz um am bm g hg hm u a b r hr hx P hgood hodd,
    squarefree_prime_count_indicator F P hF (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance)]
  unfold completedLocalExponent
  omega

theorem goodMaskMovingIdeal_generator_exponent (I F:Ideal Eis) (hI:I≠0) (hF:Squarefree F)
    (m:Eis) (v:Eisˣ)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:(idealGenerator F)^4*(v.val*idealGenerator I)=u.val*lambda^a*(2:Eis)^b*r)
    (P:Ideal Eis) [P.IsMaximal] (hgood:lambda∉P) (hodd:ringChar (Eis⧸P)≠2) :
    (normalizedFactors (goodMaskMovingIdeal g r)).count P%6=completedLocalExponent I F P := by
  exact goodMaskMovingIdeal_exponent I F hI hF m (idealGenerator F) (v.val*idealGenerator I)
    (span_idealGenerator F) (by rw [Ideal.span_singleton_mul_left_unit v.isUnit,span_idealGenerator])
    um am bm g hg hm u a b r hr hx P hgood hodd

end CanonicalRowCompletion

end

end OAI
