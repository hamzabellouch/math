import OAI.NumberTheory.DirichletL.RowCompletion.FixedCuspBranches

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

section
open scoped BigOperators Classical MatrixGroups

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A4PhaseFromResidue_norm (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}) (x:Eis) :
    ‖A4PhaseFromResidue c0 hc0 v x‖=1 := by
  let:Finite (Eis⧸Ideal.span {ramifiedTraceLambda^3*c0}):=
    finite_quotient_span (A4_bad_modulus_ne_zero c0 hc0)
  unfold A4PhaseFromResidue
  exact AddChar.norm_apply _ _
end ShortDraftCusp

namespace CubicEisenstein
open ActualEisensteinCubic CompletedGauss ShortDraftCusp ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceFrequencyAngle_norm_le_one (h:Eis) : ‖sourceFrequencyAngle h‖≤1 := by
  by_cases hh:h=0
  · simp only [hh,sourceFrequencyAngle,map_zero,norm_zero,Complex.ofReal_zero,div_zero]
    norm_num
  · exact (sourceFrequencyAngle_norm h hh).le

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H)

def reflectionStaticPhase (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) : ℂ :=
  sourceFrequencyAngle (fixedCuspArrayIndex u m I J)*
    ShortDraftTrace.breveE (-cuspFrequency (fixedCuspArrayIndex u m I J)*
      eisEmbedding (s.upper 0 0*s.upper 0 1)/(sourceCuspScale s.index:ℂ))*
    A4PhaseFromResidue c0 hc0 v (dualNumerator m I J)

lemma reflectionStaticPhase_norm_le_one (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) : ‖s.reflectionStaticPhase c0 hc0 v dualNumerator u m I J‖≤1 := by
  simp only [reflectionStaticPhase,norm_mul,breveE_norm,A4PhaseFromResidue_norm,mul_one]
  exact sourceFrequencyAngle_norm_le_one _

lemma fixedCuspArrayWithPhase_reflectionStaticPhase (c0:Eis) (hc0:c0≠0)
    (v:Eis⧸Ideal.span {ramifiedTraceLambda^3*c0})
    (dualNumerator:ℕ→Ideal Eis→Ideal Eis→Eis) (u:Eisˣ)
    (m:ℕ) (I J:Ideal Eis) :
    fixedCuspArrayWithPhase s.index u (s.reflectionStaticPhase c0 hc0 v dualNumerator u) m I J=
      s.amplitude u m I J*A4PhaseFromResidue c0 hc0 v (dualNumerator m I J) := by
  unfold fixedCuspArrayWithPhase reflectionStaticPhase amplitude
  ring

end FixedCuspShape
end CubicEisenstein
end

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalCoefficientClass
local notation "Eis" => ActualEisensteinCubic.O

def reflectionConductor (q:ℕ) : Eis := (2592*q:ℕ)

def reflectionExcludedPrimes (q:ℕ) : Finset (Ideal Eis) :=
  gcdMaskPrimes (Ideal.span {reflectionConductor q})

lemma reflectionConductor_ne_zero (q:ℕ) (hq:q≠0) : reflectionConductor q≠0 := by
  unfold reflectionConductor
  exact_mod_cast Nat.mul_ne_zero (by decide : 2592≠0) hq

lemma reflectionConductor_ideal (q:ℕ) :
    Ideal.span {reflectionConductor q}=
      Ideal.span {(9:Eis)}*(fixedBaseConductor q*Ideal.span {(72:Eis)}) := by
  rw [fixedBaseConductor_principal,Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton]
  congr 1
  unfold reflectionConductor
  push_cast
  ring_nf

lemma reflectionExcludedPrimes_bad (q:ℕ) :
    fixedBadPrimes⊆reflectionExcludedPrimes q := Finset.subset_union_left

lemma reflectionExcludedPrimes_prime (q:ℕ) (P:Ideal Eis)
    (hP:P∈reflectionExcludedPrimes q) : Prime P := by
  let:P.IsMaximal:=gcdMaskPrimes_maximal _ ⟨P,hP⟩
  exact Ideal.prime_of_isPrime (NeZero.ne P) inferInstance

lemma reflectionConductor_prime_mem (q:ℕ) (hq:q≠0) (P:Ideal Eis)
    (hP:Prime P) (hd:P∣Ideal.span {reflectionConductor q}) :
    P∈reflectionExcludedPrimes q := by
  apply Finset.mem_union_right
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr
    (reflectionConductor_ne_zero q hq))).mpr
  exact ⟨Ideal.isPrime_of_prime hP,Ideal.dvd_iff_le.mp hd⟩

lemma reflectionExcludedGenerator_ne_zero (q:ℕ) :
    excludedGenerator (reflectionExcludedPrimes q)≠0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  exact Finset.prod_ne_zero_iff.mpr (fun P hP=>(reflectionExcludedPrimes_prime q P hP).ne_zero)

lemma reflectionExcludedGenerator_bad (q:ℕ) :
    lambda∣excludedGenerator (reflectionExcludedPrimes q) ∧
      (2:Eis)∣excludedGenerator (reflectionExcludedPrimes q) := by
  constructor
  · apply Ideal.mem_span_singleton.mp
    exact excludedGenerator_mem _ (reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes]))
  · apply Ideal.mem_span_singleton.mp
    exact excludedGenerator_mem _ (reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes]))

lemma reflectionConductor_coprime_of_not_excluded (q:ℕ) (hq:q≠0)
    (P:Ideal Eis) [P.IsMaximal] (hP:P∉reflectionExcludedPrimes q) :
    IsCoprime (Ideal.span {reflectionConductor q}) P := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra ht
  have he:P=Ideal.span {reflectionConductor q}⊔P:=
    (show P.IsMaximal from inferInstance).eq_of_le ht le_sup_right
  exact hP (reflectionConductor_prime_mem q hq P
    (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance)
    (Ideal.dvd_iff_le.mpr (le_sup_left.trans he.symm.le)))

lemma reflectionConductor_coprime_primary (q:ℕ) (hq:q≠0)
    (p:Eis) [(Ideal.span {p}).IsMaximal]
    (hp:Ideal.span {p}∉reflectionExcludedPrimes q) :
    IsCoprime (reflectionConductor q) p :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp
    (reflectionConductor_coprime_of_not_excluded q hq _ hp)

lemma reflectionLevelBound_ge_one (q:ℕ) (hq:q≠0) :
    1≤CubicEisenstein.fixedCuspLevelBound (reflectionConductor q) :=
  CubicEisenstein.fixedCuspLevelBound_ge_one _ (reflectionConductor_ne_zero q hq)

end CanonicalRowCompletion

open scoped BigOperators Classical

namespace CompletedGauss
open ActualEisensteinCubic UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma prime_dvd_rowResidualPart_iff (I Q P:Ideal Eis) (hP:Prime P) :
    P∣rowResidualPart I Q ↔ P∈normalizedFactors (rowSimplePart I) ∧ ¬P∣Q := by
  have hm:=UniqueFactorizationMonoid.mem_normalizedFactors_iff
    (squarefreeResidualPart_ne_zero (rowSimplePart I) Q) (p:=P)
  simp only [hP,true_and] at hm
  change P∣squarefreeResidualPart (rowSimplePart I) Q ↔ _
  rw [←hm]
  simp only [normalizedFactors_squarefreeResidualPart,Multiset.mem_filter]

lemma rowResidualPart_prime_fixed_mask (I Q Q0 P:Ideal Eis)
    (hP:Prime P) (hfree:¬Q0≤P) :
    P∣rowResidualPart I (Q0*Q) ↔ P∣rowResidualPart I Q := by
  have hnd:¬P∣Q0:=by simpa only [Ideal.dvd_iff_le] using hfree
  rw [prime_dvd_rowResidualPart_iff I (Q0*Q) P hP,
    prime_dvd_rowResidualPart_iff I Q P hP,hP.dvd_mul]
  simp only [hnd,false_or]

theorem completedReflectionPool_fixed_mask_filter (I Q Q0:Ideal Eis)
    (hI:I≠0) (hQ:Q≠0) (hQ0:Q0≠0) :
    (completedReflectionPool I (Q0*Q)).filter (fun P=>¬Q0≤P)=
      (completedReflectionPool I Q).filter (fun P=>¬Q0≤P) := by
  ext P
  simp only [Finset.mem_filter,mem_completedReflectionPool I (Q0*Q) P hI (mul_ne_zero hQ0 hQ),
    mem_completedReflectionPool I Q P hI hQ]
  by_cases hP:Prime P
  · by_cases hfree:¬Q0≤P
    · have hnd:¬P∣Q0:=by simpa only [Ideal.dvd_iff_le] using hfree
      have hdiv:P∣I*(Q0*Q) ↔ P∣I*Q:=by
        rw [hP.dvd_mul,hP.dvd_mul,hP.dvd_mul]
        simp only [hnd,false_or]
      rw [hdiv,rowResidualPart_prime_fixed_mask I Q Q0 P hP hfree]
    · simp only [hfree,and_false]
  · simp only [hP,false_and]

end CompletedGauss

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

theorem goodMaskNonresidualPool_full_mask (I F Q0:Ideal Eis)
    (hI:I≠0) (hF:F≠0) (hQ0:Q0≠0)
    (m f z:Eis) (hm0:m≠0) (hf:Ideal.span {f}=F) (hz:Ideal.span {z}=I)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) :
    (goodMaskNonresidualPool I F m g r).filter (fun P=>¬Q0≤P)=
      (completedReflectionPool I (Q0*(Ideal.span {m}*F))).filter (fun P=>¬Q0≤P) := by
  rw [completedReflectionPool_fixed_mask_filter I (Ideal.span {m}*F) Q0 hI
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm0) hF) hQ0]
  exact goodMaskNonresidualPool_free_eq I F Q0 hI hF m f z hm0 hf hz
    um am bm g hg hm u a b r hr hx

end CanonicalRowCompletion

open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_ramified_character_of_relative_level (M:SL(2,Eis)) (u q r:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree)
    (ha:lambda^2∣M 0 0-1) (hr:lambda^2∣r-1) (hC:M 1 0=(u*q)*r) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩=
      eisEmbedding (symbol (-u) (M 0 0-u*M 0 1)*symbol q (M 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  have hdet:M 0 0*M 1 1-M 0 1*(u*(q*r))=1 := by
    have hd:=M.property
    simp only [Matrix.det_fin_two,hC] at hd
    linear_combination hd
  rw [A3_ramified_literal_character,hC,show (u*q)*r=u*(q*r) by ring,
    A3_ramified_global_factor _ _ _ _ _ _ hdet ha hA hr,map_mul]

theorem A3_unramified_character_of_relative_level (M:SL(2,Eis)) (u c0 r:Eis)
    (hG:M*(A3WeylCusp u)⁻¹∈levelThree)
    (hc:lambda^2∣M 1 0-1) (h9:(9:Eis)∣M 0 0*M 1 1) (hC:M 1 0=c0*r) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hG⟩=
      eisEmbedding (symbol (M 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  have hb:=levelThree_primary ⟨M*(A3WeylCusp u)⁻¹,hG⟩
  change lambda^2∣(((M*(A3WeylCusp u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hb
  rw [A3_unramified_relative_matrix] at hb
  have hdet:M 0 0*M 1 1-M 0 1*(c0*r)=1 := by
    simpa only [Matrix.det_fin_two,hC] using M.property
  rw [hC] at hc
  rw [A3_unramified_literal_character,A3_unramified_global_factor _ _ _ _ _ hdet hb hc h9,map_mul]

end

section
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss CubicKubota CubicJacobiGlobal LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance stratumMultiplierField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance stratumMultiplierFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem stratum_multiplier_of_cubic_factor {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (c0 U w x d0:Eis) (hc0:c0≠0)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (a b d:(∀i,(Eis⧸Ideal.span {p i})ˣ)→Eis)
    (κ:(∀i,(Eis⧸Ideal.span {p i})ˣ)→ℂ) (κ0:ℂ)
    (hκ:∀v,κ v=κ0*eisEmbedding (symbol (a v) (∏i,p i)))
    (hdet:∀v,a v*d v-b v*(c0*∏i,p i)=1)
    (hD:∀v,ramifiedTraceLambda^3*c0∣d v-d0)
    (σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ)
    (hfreq:∀v i,Ideal.Quotient.mk (Ideal.span {p i}) (a v)=
      (σ i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}))
    (hε:∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (j:ι→ℕ) (hj:∀i,j i<6) :
    (∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
        (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i))*
      star (κ v)*ShortDraftTrace.breveE (-(eisEmbedding (d v)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))) =
    (star κ0*A4BadPhase c0 hc0 d0 U x)*
    ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (σ i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (ε i)*
      bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  let C:=star κ0*A4BadPhase c0 hc0 d0 U x
  let f:=fun i (v:(Eis⧸Ideal.span {p i})ˣ)=>frequencyRow
    (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i)
    (σ i) (ε i) (Ideal.Quotient.mk _ x) v
  have hpoint (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
      star (κ v)*ShortDraftTrace.breveE (-(eisEmbedding (d v)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))=
      C*∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (v i) := by
    have hbad:A4BadPhase c0 hc0 (d v) U x=A4BadPhase c0 hc0 d0 U x := by
      apply A4BadPhase_eq_of_residue
      convert dvd_mul_of_dvd_left (hD v) U using 1 ; ring
    have hlocal:=A3_A4_frequency_product p hp hcop hg (a v) (b v) c0 (d v)
      U w x hc0 (hdet v) hbez σ ε (fun i=>(v i:Eis⧸Ideal.span {p i})) (hfreq v) hε
    rw [hκ,star_mul]
    calc
      _=star κ0*(star (eisEmbedding (symbol (a v) (∏i,p i)))*
        ShortDraftTrace.breveE (-(eisEmbedding (d v)*(eisEmbedding x/eisLam^4))/
          (eisEmbedding c0*eisEmbedding (∏i,p i)))) := by ring
      _=_ := by rw [hlocal,hbad];dsimp only [C];ring
  calc
    _=C*∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,∏i,f i (v i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [mul_assoc,hpoint]
      simp only [f,frequencyRow,Finset.prod_mul_distrib]
      ring
    _=C*∏i,∑v:(Eis⧸Ideal.span {p i})ˣ,f i v := by rw [Fintype.prod_sum]
    _=_ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact canonical_frequencyRow_units (Ideal.span {p i}) (hg i) (hchar i)
        (quotientTrace (p i) (hp i))
        (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) (j i) (hj i) (σ i) (ε i) _

end

open ActualEisensteinCubic CubicEisenstein CubicKubota CubicJacobiGlobal ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma A3_ramified_relative_primary (M:SL(2,Eis)) (u:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree) :
    lambda^2∣(M 0 0-u*M 0 1)-1 := by
  have hA:=levelThree_primary ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩
  change lambda^2∣(((M*(lowerCuspMatrix u)⁻¹:SL(2,Eis)):Matrix (Fin 2) (Fin 2) Eis) 0 0)-1 at hA
  rw [A3_ramified_relative_matrix] at hA
  exact hA

theorem A3_ramified_fixed_sector_character (M M0:SL(2,Eis)) (N u q r:Eis)
    (hG:M*(lowerCuspMatrix u)⁻¹∈levelThree)
    (hG0:M0*(lowerCuspMatrix u)⁻¹∈levelThree)
    (ha:lambda^2∣M 0 0-1) (ha0:lambda^2∣M0 0 0-1)
    (hr:lambda^2∣r-1) (hC:M 1 0=(u*q)*r)
    (h9N:(9:Eis)∣N) (hqN:q∣N) (huN:u∣N)
    (hA:N∣M 0 0-M0 0 0) (hB:N∣M 0 1-M0 0 1) :
    complexCharacter ⟨M*(lowerCuspMatrix u)⁻¹,hG⟩=
      eisEmbedding (symbol (-u) (M0 0 0-u*M0 0 1)*symbol q (M0 0 0))*
        eisEmbedding (symbol (M 0 0) r) := by
  rw [A3_ramified_character_of_relative_level M u q r hG ha hr hC]
  rw [A3_ramified_fixed_factor_congr N q u (M 0 0) (M0 0 0) (M 0 1) (M0 0 1)
    h9N hqN huN ha ha0 (A3_ramified_relative_primary M u hG)
    (A3_ramified_relative_primary M0 u hG0) hA hB]

theorem A3_unramified_fixed_sector_character (M M0:SL(2,Eis)) (u c0 r:Eis)
    (hG:M*(A3WeylCusp u)⁻¹∈levelThree)
    (hc:lambda^2∣M 1 0-1) (h9:(9:Eis)∣M 0 0*M 1 1) (hC:M 1 0=c0*r)
    (hA:c0∣M 0 0-M0 0 0) :
    complexCharacter ⟨M*(A3WeylCusp u)⁻¹,hG⟩=
      eisEmbedding (symbol (M0 0 0) c0)*eisEmbedding (symbol (M 0 0) r) := by
  rw [A3_unramified_character_of_relative_level M u c0 r hG hc h9 hC,
    symbol_congr hA]

end ShortDraftCusp

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O

structure ControlledStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) (N a0 c0:Eis) (numeratorMode:Bool) where
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
  matrix : (∀i,(Eis⧸Ideal.span {p i})ˣ)→SL(2,Eis)
  numerator : ∀v,matrix v 0 0=finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  denominator : ∀v,matrix v 1 0=c0*∏i,p i
  matrix_fixed : ∀v i j,N∣matrix v i j-matrix (fun _=>1) i j
  conditions : ∀v,if numeratorMode then
    (9:Eis)∣matrix v 0 1 ∧ (3:Eis)∣matrix v 1 1-1
    else (3:Eis)∣matrix v 0 1+1 ∧ (9:Eis)∣matrix v 1 1

theorem exists_controlledStratumArithmetic {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hprimary:∀i,lambda^2∣p i-1)
    (N a0 c0:Eis) (hc0:c0≠0) (hN:(9:Eis)*c0∣N)
    (mode:Bool) (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (hac:IsCoprime a0 c0) (hNp:∀i,IsCoprime N (p i)) :
    Nonempty (ControlledStratumArithmetic p N a0 c0 mode) := by
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
  have hbez:U*r+(ramifiedTraceLambda^3*w)*c0=1 := by linear_combination huw
  obtain ⟨σ,ε,hσ,hε⟩:=exists_A4_local_units p hp hcop c0 U w hbez
  have hlf (v:∀i,(Eis⧸Ideal.span {p i})ˣ):=exists_strong_unit_frequency_lifts N p hNp v
  choose lift hlift hres hlcop using hlf
  let a:=fun v=>finiteCrossNumerator a0 c0 ramifiedTraceLambda p (lift v)
  have hap (ha0:lambda^2∣a0-1):∀v,lambda^2∣a v-1 := by
    intro v
    have hfixed:N∣a v-a0*r:=finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (lift v)
      (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (hlift v i))
    have hbas:=primary_mul a0 r ha0 hr
    convert dvd_add (hstdN.trans hfixed) hbas using 1 ; ring
  have hpairs:Pairwise (Function.onFun IsCoprime p):=by
    intro i k hik
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hcop hik)
  have hacop:∀v,IsCoprime (a v) (c0*r) := by
    intro v
    exact finiteCrossNumerator_coprime a0 c0 ramifiedTraceLambda p (lift v) hac hpairs
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hcN)
      (fun i=>(hNp i).of_isCoprime_of_dvd_left hlN) (hlcop v)
  have hfixed:∀v z,(fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) v=()→N*c0∣a v-a z := by
    intro v z _
    exact finiteCrossNumerator_fixed_sector N a0 c0 ramifiedTraceLambda p (lift v)
      p (lift z) hcN (hlift v) (hlift z) (by simp)
  have hcompletes:∃(b d:(∀i,(Eis⧸Ideal.span {p i})ˣ)→Eis)
      (C:Matrix (Fin 2) (Fin 2) (Eis⧸Ideal.span {N})),
      (∀v,a v*d v-b v*(c0*r)=1) ∧
      (∀v,if mode then (9:Eis)∣b v ∧ (3:Eis)∣d v-1 else (3:Eis)∣b v+1 ∧ (9:Eis)∣d v) ∧
      ∀v,(!![a v,b v;c0*r,d v]:Matrix (Fin 2) (Fin 2) Eis).map (Ideal.Quotient.mk (Ideal.span {N}))=C := by
    cases mode
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩:=exists_primary_denominator_sector_completions N c0 h9N hbase
        (fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) a (fun _=>r)
        (fun _=>hr) hacop (fun _=>hrNc) (fun v z _=>hfixed v z rfl) (fun _ _ _=>by simp)
      exact ⟨b,d,C (),hd,fun v=>⟨hb v,hz v⟩,hm⟩
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩:=exists_primary_numerator_sector_completions N c0 hc0 h9N
        (fun (_:∀i,(Eis⧸Ideal.span {p i})ˣ)=>()) a (fun _=>r)
        (hap hbase) (fun _=>hr) hacop (fun _=>hrNc)
        (fun v z _=>hfixed v z rfl) (fun _ _ _=>by simp)
      exact ⟨b,d,C (),hd,fun v=>⟨hb v,hz v⟩,hm⟩
  obtain ⟨b,d,C,hdet,hconditions,hmat⟩:=hcompletes
  let mat:=fun v=>controlledCompletionMatrix (a v) (b v) (c0*r) (d v) (hdet v)
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
    matrix := mat
    numerator := fun _=>rfl
    denominator := fun _=>rfl
    matrix_fixed := hentry
    conditions := hconditions
  }⟩

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma frequency_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (i:ι) :
    Ideal.Quotient.mk (Ideal.span {p i}) (D.matrix v 0 0)=
      (D.sigma i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}) := by
  rw [D.numerator,finiteCrossNumerator_local,D.sigma_value,D.lift_residue]

lemma numerator_congruence (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    N∣D.matrix v 0 0-a0*∏i,p i := by
  rw [D.numerator]
  exact finiteCrossNumerator_fixed N a0 c0 ramifiedTraceLambda p (D.lift v)
    (fun i=>(dvd_pow_self N (by decide : (2:ℕ)≠0)).trans (D.lift_period v i))

lemma numerator_mod_three (D:ControlledStratumArithmetic p N a0 c0 mode)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : (3:Eis)∣D.matrix v 0 0-a0 := by
  have hprod:=three_dvd_primary_sub_one (∏i,p i) hr
  convert dvd_add (h3N.trans (D.numerator_congruence v))
    (dvd_mul_of_dvd_right hprod a0) using 1 ; ring

lemma numerator_primary (D:ControlledStratumArithmetic p N a0 c0 mode)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : lambda^2∣D.matrix v 0 0-1 := by
  convert dvd_add (lambda_sq_dvd_three.trans (D.numerator_mod_three h3N hr v)) ha using 1 ; ring

lemma denominator_primary (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) : lambda^2∣D.matrix v 1 0-1 := by
  rw [D.denominator]
  exact primary_mul c0 (∏i,p i) hc hr

lemma ramified_relative (D:ControlledStratumArithmetic p N a0 c0 true)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (u:Eis) (hcu:(3:Eis)∣c0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(lowerCuspMatrix u)⁻¹∈levelThree := by
  have hcond := D.conditions v
  simp only [ ↓reduceIte] at hcond
  apply A3_ramified_mem_levelThree
  · exact three_dvd_primary_sub_one _ (D.numerator_primary h3N hr ha v)
  · exact (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hcond.1
  · rw [D.denominator]
    have hprod:=three_dvd_primary_sub_one (∏i,p i) hr
    convert dvd_add (dvd_mul_of_dvd_right hprod c0) hcu using 1 ; ring
  · exact hcond.2

lemma unramified_relative (D:ControlledStratumArithmetic p N a0 c0 false)
    (h3N:(3:Eis)∣N) (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (u:Eis) (hau:(3:Eis)∣a0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v*(A3WeylCusp u)⁻¹∈levelThree := by
  have hcond := D.conditions v
  simp only [Bool.false_eq_true, ↓reduceIte] at hcond
  apply A3_unramified_mem_levelThree
  · convert dvd_add (D.numerator_mod_three h3N hr v) hau using 1 ; ring
  · exact hcond.1
  · exact three_dvd_primary_sub_one _ (D.denominator_primary hr hc v)
  · exact (show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans hcond.2

lemma inverse_fixed (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    ramifiedTraceLambda^3*c0∣D.matrix v 1 1-D.matrix (fun _=>1) 1 1 := by
  have hD9:ramifiedTraceLambda^3*c0∣(9:Eis)*c0 := by
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [←A4_traceLambda_pow_four]
    ring
  exact (hD9.trans hN).trans (D.matrix_fixed v 1 1)

lemma determinant (D:ControlledStratumArithmetic p N a0 c0 mode)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    D.matrix v 0 0*D.matrix v 1 1-D.matrix v 0 1*(c0*∏i,p i)=1 := by
  simpa only [Matrix.det_fin_two,D.denominator] using (D.matrix v).property

def ramifiedFixedFactor (D:ControlledStratumArithmetic p N a0 c0 true) (u q:Eis) : ℂ :=
  eisEmbedding (symbol (-u) (D.matrix (fun _=>1) 0 0-u*D.matrix (fun _=>1) 0 1)*
    symbol q (D.matrix (fun _=>1) 0 0))

def unramifiedFixedFactor (D:ControlledStratumArithmetic p N a0 c0 false) : ℂ :=
  eisEmbedding (symbol (D.matrix (fun _=>1) 0 0) c0)

theorem ramified_character (D:ControlledStratumArithmetic p N a0 c0 true)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1) (ha:lambda^2∣a0-1)
    (u q:Eis) (hc0:c0=u*q) (hcu:(3:Eis)∣c0-u)
    (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter ⟨D.matrix v*(lowerCuspMatrix u)⁻¹,
      D.ramified_relative ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
        ((dvd_mul_right 9 c0).trans hN)) hr ha u hcu v⟩=
      D.ramifiedFixedFactor u q*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N
  have hcN:c0∣N:=(dvd_mul_left c0 9).trans hN
  exact A3_ramified_fixed_sector_character (D.matrix v) (D.matrix (fun _=>1)) N u q (∏i,p i)
    (D.ramified_relative h3N hr ha u hcu v) (D.ramified_relative h3N hr ha u hcu (fun _=>1))
    (D.numerator_primary h3N hr ha v) (D.numerator_primary h3N hr ha (fun _=>1)) hr
    (by rw [D.denominator,hc0]) h9N
    ((hc0 ▸ dvd_mul_left q u).trans hcN) ((hc0 ▸ dvd_mul_right u q).trans hcN)
    (D.matrix_fixed v 0 0) (D.matrix_fixed v 0 1)

theorem unramified_character (D:ControlledStratumArithmetic p N a0 c0 false)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1) (hc:lambda^2∣c0-1)
    (u:Eis) (hau:(3:Eis)∣a0-u) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    complexCharacter ⟨D.matrix v*(A3WeylCusp u)⁻¹,
      D.unramified_relative ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans
        ((dvd_mul_right 9 c0).trans hN)) hr hc u hau v⟩=
      D.unramifiedFixedFactor*eisEmbedding (symbol (D.matrix v 0 0) (∏i,p i)) := by
  have h9N:(9:Eis)∣N:=(dvd_mul_right 9 c0).trans hN
  have h3N:(3:Eis)∣N:=(show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9N
  have hcond:=D.conditions v
  simp only [Bool.false_eq_true, ↓reduceIte] at hcond
  exact A3_unramified_fixed_sector_character (D.matrix v) (D.matrix (fun _=>1)) u c0 (∏i,p i)
    (D.unramified_relative h3N hr hc u hau v) (D.denominator_primary hr hc v)
    (dvd_mul_of_dvd_right hcond.2 _) (D.denominator v)
    (((dvd_mul_left c0 9).trans hN).trans (D.matrix_fixed v 0 0))

end ControlledStratumArithmetic
end CubicEisenstein

end

end OAI
