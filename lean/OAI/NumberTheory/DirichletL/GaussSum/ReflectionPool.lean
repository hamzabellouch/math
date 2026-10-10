import OAI.NumberTheory.DirichletL.RowCompletion.PeriodicRows

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

namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance poolMaximalCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q P
noncomputable local instance poolFieldCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Field (Eis⧸P.val) :=
  Ideal.Quotient.field P.val
noncomputable local instance poolFintypeCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Fintype (Eis⧸P.val) :=
  Fintype.ofFinite _

lemma reflectionSixInactiveWeight_support (I F Q:Ideal Eis)
    (e:completedReflectionPool I Q→Fin 6) (hne:reflectionSixInactiveWeight I F Q e≠0)
    (P:completedReflectionPool I Q) (hj:completedLocalExponent I F P.val≠0) :
    reflectionSixActive (e P) := by
  have he:reflectionSixValid e:=by
    by_contra he
    exact hne (by simp [reflectionSixInactiveWeight,he])
  have hprod:reflectionInactiveStratumWeight I F Q (reflectionSixSupport e)≠0:=by
    simpa only [reflectionSixInactiveWeight,ite_eq_left he] using hne
  by_contra hP
  have hm:P∈(Finset.univ:Finset (completedReflectionPool I Q))\reflectionSixSupport e:=by
    simp [reflectionSixSupport,hP]
  have hp:zeroFourierCoefficient (actualSextic P.val (completedReflectionPool_good I Q P))
      (completedLocalExponent I F P.val)≠0:=
    (Finset.prod_ne_zero_iff.mp hprod) P hm
  have hz:=canonical_zeroFourierCoefficient P.val (completedReflectionPool_good I Q P)
    (completedReflectionPool_odd I Q P) (completedLocalExponent I F P.val)
    (Nat.mod_lt _ (by decide : 0<6))
  apply hp
  simpa only [actualSextic,ite_eq_right hj] using hz

lemma sixReflectionIndex_card (rays:ℕ) (I Q:Ideal Eis) :
    Fintype.card (SixReflectionIndex rays I Q)=rays*6^(completedReflectionPool I Q).card := by
  simp [SixReflectionIndex]

theorem completedReflectionPool_count_small_power (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀I Q:Ideal Eis,I≠0→Q≠0→
      (6:ℝ)^(2*(completedReflectionPool I Q).card)≤
        C*((Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ))^ε := by
  obtain ⟨C,hC,hbound⟩:=completed_branch_count_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro I Q hI hQ
  have h:=hbound (I*Q) (mul_ne_zero hI hQ)
    (fun P:completedReflectionPool I Q=>P.val) Subtype.val_injective
    (completedReflectionPool_divides I Q hI hQ)
  simpa only [Fintype.card_coe,map_mul,Nat.cast_mul] using h

end CompletedGauss

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma actualSextic_sixth_one (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) :
    actualSextic P hg^6=1 := by
  apply MulChar.ext
  intro t
  obtain ⟨n,hn⟩:=Ideal.Quotient.mk_surjective (t:Eis⧸P)
  have hnot:n∉P:=by
    intro hm
    have ht:(t:Eis⧸P)=0:=by rw [←hn];exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
    exact t.ne_zero ht
  have h:=canonicalSextic_sixth_power_mask P hg n
  change actualSextic P hg (Ideal.Quotient.mk P (n^6))=_ at h
  rw [map_pow,map_pow,ite_eq_right hnot] at h
  rw [MulChar.pow_apply_coe,MulChar.one_apply_coe,←hn]
  exact h

lemma actualSextic_power_mod_six (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P)
    (k:ℕ) (hk:k≠0) (n:Eis) :
    actualSextic P hg (Ideal.Quotient.mk P n)^k=
      (actualSextic P hg^(k%6)) (Ideal.Quotient.mk P n) := by
  rw [←MulChar.pow_apply' _ hk,pow_eq_pow_mod _ (actualSextic_sixth_one P hg)]

lemma idealRowHom_eq_prime_count_product (I:Ideal Eis) (hI:Supported I) (n:Eis) :
    idealRowHom n I=∏P:PrimeIndex I,
      (actualSextic P.val ((supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1) ^
        ((normalizedFactors I).count P.val%6)) (Ideal.Quotient.mk P.val n) := by
  have he:I=∏P:PrimeIndex I,P.val^((normalizedFactors I).count P.val):=by
    change I=∏P:(normalizedFactors I).toFinset,P.val^((normalizedFactors I).count P.val)
    exact ((Ideal.prod_normalizedFactors_eq_self hI.1).symm.trans (Finset.prod_multiset_count _)).trans
      (Finset.prod_coe_sort (normalizedFactors I).toFinset (fun P=>P^((normalizedFactors I).count P))).symm
  calc
    idealRowHom n I = idealRowHom n (∏P:PrimeIndex I,P.val^((normalizedFactors I).count P.val)) :=
      congrArg (idealRowHom n) he
    _ = ∏P:PrimeIndex I,idealRowHom n P.val ^ ((normalizedFactors I).count P.val) := by
      simp only [map_prod,map_pow]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [idealRowHom_prime n P.val
        ((supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1)]
      exact actualSextic_power_mod_six P.val _ _
        (Nat.ne_of_gt (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property))) n

lemma primeIndex_pairwise_coprime (I:Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (fun P:PrimeIndex I=>P.val)) := by
  intro P Q hPQ
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPQ (Subtype.ext he))

theorem idealRowHom_eq_principalSexticRow (I:Ideal Eis) (hI:Supported I) (n:Eis) :
    idealRowHom n I=
      principalSexticRow (fun P:PrimeIndex I=>P.val) (primeIndex_pairwise_coprime I)
        (fun P=>(supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1)
        (fun P=>(normalizedFactors I).count P.val%6)
        (finitePrimeModulus (fun P:PrimeIndex I=>P.val))
        (span_finitePrimeModulus _)
        (Ideal.Quotient.mk _ n) := by
  rw [principalSexticRow_mk]
  exact idealRowHom_eq_prime_count_product I hI n

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma coprimalityMask_good_part (u:Eisˣ) (a b:ℕ) (r n:Eis)
    (hn:Supported (Ideal.span {n})) :
    coprimalityMask (u.val*lambda^a*(2:Eis)^b*r) n=coprimalityMask r n := by
  have hl:IsCoprime lambda n:=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr ((supported_span_iff n).mp hn).1
  have hneg2:IsCoprime (-2:Eis) n:=negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have h2:IsCoprime (2:Eis) n:=hneg2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  have hu:IsCoprime u.val n:=⟨(u⁻¹).val,0,by simp⟩
  have hla:IsCoprime (lambda^a) n:=hl.pow_left
  have h2b:IsCoprime ((2:Eis)^b) n:=h2.pow_left
  change (if IsCoprime (u.val*lambda^a*(2:Eis)^b*r) n then (1:ℂ) else 0)=_
  rw [IsCoprime.mul_left_iff,IsCoprime.mul_left_iff,IsCoprime.mul_left_iff]
  simp only [hu,hla,h2b,true_and]
  rfl

lemma idealRowHom_sixth_denominator_mask (r n:Eis) (hr:Supported (Ideal.span {r})) :
    idealRowHom n ((Ideal.span {r})^6)=coprimalityMask r n := by
  rw [map_pow,←idealRowHom_argument_pow n 6 _ hr,idealRowHom_sixth_eq_mask n r hr]
  change (if IsCoprime n r then (1:ℂ) else 0)=(if IsCoprime r n then 1 else 0)
  rw [isCoprime_comm]

lemma mask_times_good_row (m:Eis) (um:Eisˣ) (am bm:ℕ) (g r n:Eis)
    (hg:Supported (Ideal.span {g})) (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (hn:Supported (Ideal.span {n})) :
    coprimalityMask m n*idealRowHom n (Ideal.span {r})=
      idealRowHom n ((Ideal.span {g})^6*Ideal.span {r}) := by
  rw [hm,coprimalityMask_good_part um am bm g n hn,map_mul,
    idealRowHom_sixth_denominator_mask g n hg]

theorem rowTwist_eq_fixed_times_good_row_primary
    (Ψ:Eis→*ℂ) (m f z:Eis) (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hpr:lambda^2∣r-1) (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=(Ψ*numeratorBadTwist u a b r hr) n *
      idealRowHom n ((Ideal.span {g})^6*Ideal.span {r}) := by
  rw [rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx n hpn]
  by_cases hn:Supported (Ideal.span {n})
  · change ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*idealRowHom n (Ideal.span {r})=
      (Ψ n*numeratorBadTwist u a b r hr n)*_
    rw [show ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*idealRowHom n (Ideal.span {r})=
      (Ψ n*numeratorBadTwist u a b r hr n)*(coprimalityMask m n*idealRowHom n (Ideal.span {r})) by ring,
      mask_times_good_row m um am bm g r n hg hm hn]
  · change ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*_=
      (Ψ n*numeratorBadTwist u a b r hr n)*_
    rw [numeratorBadTwist_zero_of_not_supported u a b r hr n hn]
    simp only [mul_zero,zero_mul]

lemma fixedNumeratorTwist_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)})
      (Ψ*numeratorBadTwist u a b r hr) := by
  intro x y hxy
  change Ψ x*numeratorBadTwist u a b r hr x=Ψ y*numeratorBadTwist u a b r hr y
  rw [hΨ x y (Ideal.mul_le_left hxy),numeratorBadTwist_periodic u a b r hr x y (Ideal.mul_le_right hxy)]

theorem exists_fixed_twist_principal_row (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ) (hΨnorm:∀n,‖Ψ n‖≤1)
    (m f z:Eis) (hm:m≠0) (hf:f≠0) (hz:z≠0) (hmLam:lambda∣m) (hm2:(2:Eis)∣m) :
    ∃(I:Ideal Eis)(hI:Supported I)(φ:Eis→*ℂ),
      CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)}) φ ∧
      (∀n,‖φ n‖≤1) ∧
      (∀n,lambda^2∣n-1 → rowTwist Ψ m f z n=φ n *
        principalSexticRow (fun P:PrimeIndex I=>P.val) (primeIndex_pairwise_coprime I)
          (fun P=>(supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1)
          (fun P=>(UniqueFactorizationMonoid.normalizedFactors I).count P.val%6)
          (finitePrimeModulus (fun P:PrimeIndex I=>P.val)) (span_finitePrimeModulus _)
          (Ideal.Quotient.mk _ n)) := by
  obtain ⟨um,am,bm,g,hg,hpg,hmf⟩:=exists_supported_numerator_factorization m hm
  obtain ⟨u,a,b,r,hr,hpr,hxf⟩:=exists_supported_numerator_factorization (f^4*z)
    (mul_ne_zero (pow_ne_zero _ hf) hz)
  let I:Ideal Eis:=(Ideal.span {g})^6*Ideal.span {r}
  have hI:Supported I:=by
    change Supported ((Ideal.span {g})^6*Ideal.span {r})
    rw [supported_mul_iff]
    exact ⟨supported_pow hg 6,hr⟩
  refine ⟨I,hI,Ψ*numeratorBadTwist u a b r hr,
    fixedNumeratorTwist_periodic Ψ Q hΨ u a b r hr,?_,?_⟩
  · intro n
    change ‖Ψ n*numeratorBadTwist u a b r hr n‖≤1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (hΨnorm n)).trans (numeratorBadTwist_norm u a b r hr n)
  · intro n hpn
    rw [←idealRowHom_eq_principalSexticRow I hI n]
    exact rowTwist_eq_fixed_times_good_row_primary Ψ m f z hmLam hm2 um am bm g hg hmf
      u a b r hr hpr hxf n hpn

theorem rowTwist_completedT_eq_periodic (Ψ:Eis→*ℂ) (m f z:Eis)
    (hmLam:lambda∣m) (hm2:(2:Eis)∣m) (u:Eisˣ) (a b:ℕ) (r:Eis)
    (hr:Supported (Ideal.span {r})) (hpr:lambda^2∣r-1)
    (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r) (W:ℝ→ℂ) (X:ℝ) :
    completedT (rowTwist Ψ m f z) W X=completedT (actualPeriodicRow Ψ m u a b r hr) W X :=
  completedT_congr_primary _ _
    (rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx) W X

end CanonicalRowCompletion

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance A4unitsField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

theorem exists_A4_local_units {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (c0 U w:Eis) (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1) :
    ∃σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∀i,(σ i:Eis⧸Ideal.span {p i})=
        Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)) ∧
      ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
        (σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1 := by
  have hone (i:ι) : ∃σ ε:(Eis⧸Ideal.span {p i})ˣ,
      (σ:Eis⧸Ideal.span {p i})=Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i) ∧
      Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
        (σ:Eis⧸Ideal.span {p i})*(ε:Eis⧸Ideal.span {p i})=-1 := by
    let q:=Ideal.Quotient.mk (Ideal.span {p i})
    have hz:q (∏k,p k)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
    have hb:q (ramifiedTraceLambda^3*c0)*q w=1 := by
      have he:=congrArg q hbez
      simp only [map_add,map_mul,map_pow,map_one,hz,mul_zero,zero_add] at he
      simpa only [map_mul,map_pow,mul_assoc,mul_comm,mul_left_comm] using he
    have hb0:q (ramifiedTraceLambda^3*c0)≠0 := by
      intro he
      rw [he,zero_mul] at hb
      exact zero_ne_one hb
    have hc0:q (cofactor p i)≠0 := by
      intro he
      have hi:=productTraceShift_inverse p hp hcop i
      change q (cofactor p i)*_=1 at hi
      rw [he,zero_mul] at hi
      exact zero_ne_one hi
    have hB:q (ramifiedTraceLambda^3*c0*cofactor p i)≠0 := by
      rw [map_mul]
      exact mul_ne_zero hb0 hc0
    have hS:q (ramifiedTraceLambda^2*c0*cofactor p i)≠0 := by
      intro he
      apply hB
      calc
        _=q ramifiedTraceLambda*q (ramifiedTraceLambda^2*c0*cofactor p i) := by
          simp only [map_mul,map_pow]
          ring
        _=0:=by rw [he,mul_zero]
    let σ:(Eis⧸Ideal.span {p i})ˣ:=Units.mk0 _ hS
    let B:(Eis⧸Ideal.span {p i})ˣ:=Units.mk0 _ hB
    refine ⟨σ,-(B*σ)⁻¹,rfl,?_⟩
    have hcancel:=congrArg (fun u:(Eis⧸Ideal.span {p i})ˣ=>(u:Eis⧸Ideal.span {p i}))
      (mul_inv_cancel (B*σ))
    simpa only [B,Units.val_mk0,Units.val_mul,Units.val_one,Units.val_neg,mul_neg] using congrArg Neg.neg hcancel
  choose σ ε hσ hε using hone
  exact ⟨σ,ε,hσ,hε⟩

end ShortDraftCusp

section
open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss CubicKubota CubicJacobiGlobal LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance principalStratumField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance principalStratumFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem principal_stratum_multiplier {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (c0 U w x:Eis) (hc0:c0≠0) (hr:lambda^2∣(∏i,p i)-1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (g:(∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree)
    (hC:∀v,(g v:SL(2,Eis)) 1 0=c0*∏i,p i)
    (hA:∀v,(9:Eis)*c0∣(g v:SL(2,Eis)) 0 0-(g (fun _=>1):SL(2,Eis)) 0 0)
    (hD:∀v,ramifiedTraceLambda^3*c0∣(g v:SL(2,Eis)) 1 1-(g (fun _=>1):SL(2,Eis)) 1 1)
    (σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ)
    (hfreq:∀v i,Ideal.Quotient.mk (Ideal.span {p i}) ((g v:SL(2,Eis)) 0 0)=
      (σ i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}))
    (hε:∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (j:ι→ℕ) (hj:∀i,j i<6) :
    (∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
        (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i))*
      star (complexCharacter (g v))*
      ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))) =
    (star (eisEmbedding (symbol c0 ((g (fun _=>1):SL(2,Eis)) 0 0)))*
      A4BadPhase c0 hc0 ((g (fun _=>1):SL(2,Eis)) 1 1) U x)*
    ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (σ i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (ε i)*
      bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i) (Ideal.Quotient.mk _ x) := by
  let a0:=(g (fun _=>1):SL(2,Eis)) 0 0
  let d0:=(g (fun _=>1):SL(2,Eis)) 1 1
  let C:=star (eisEmbedding (symbol c0 a0))*A4BadPhase c0 hc0 d0 U x
  let f:=fun i (v:(Eis⧸Ideal.span {p i})ˣ)=>frequencyRow
    (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i)
    (σ i) (ε i) (Ideal.Quotient.mk _ x) v
  have hpoint (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
      star (complexCharacter (g v))*
      ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i)))=
      C*∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (v i) := by
    have hbad:A4BadPhase c0 hc0 ((g v:SL(2,Eis)) 1 1) U x=A4BadPhase c0 hc0 d0 U x := by
      apply A4BadPhase_eq_of_residue
      convert dvd_mul_of_dvd_left (hD v) U using 1 ; ring
    have hfixed:symbol c0 ((g v:SL(2,Eis)) 0 0)=symbol c0 a0 :=
      A3_fixed_factor_congr 9 c0 _ _ (dvd_refl _) (levelThree_primary (g v))
        (levelThree_primary (g (fun _=>1))) (hA v)
    have hdet:(g v:SL(2,Eis)) 0 0*(g v:SL(2,Eis)) 1 1-
        (g v:SL(2,Eis)) 0 1*(c0*∏i,p i)=1 := by
      rw [←hC v]
      simpa only [Matrix.det_fin_two] using (g v:SL(2,Eis)).property
    have hlocal:=A3_A4_frequency_product p hp hcop hg
      ((g v:SL(2,Eis)) 0 0) ((g v:SL(2,Eis)) 0 1) c0 ((g v:SL(2,Eis)) 1 1)
      U w x hc0 hdet hbez σ ε (fun i=>(v i:Eis⧸Ideal.span {p i})) (hfreq v) hε
    rw [A3_principal_character (g v) (g v).property c0 (∏i,p i) (hC v) hr,hfixed,star_mul]
    calc
      _=star (eisEmbedding (symbol c0 a0))*
          (star (eisEmbedding (symbol ((g v:SL(2,Eis)) 0 0) (∏i,p i)))*
            ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
              (eisEmbedding c0*eisEmbedding (∏i,p i)))) := by ring
      _=_ := by rw [hlocal,hbad];dsimp only [C];ring
  calc
    _=C*∑v:∀i,(Eis⧸Ideal.span {p i})ˣ,∏i,f i (v i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [mul_assoc, hpoint]
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

end ShortDraftCusp

namespace CubicEisenstein
open ActualEisensteinCubic CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma cuspRepresentative_zero_eq_one : cuspRepresentative 0=(1:SL(2,Eis)) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspRepresentative,cuspParameter,lowerCuspMatrix]

def principalCuspDatum (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) : SourceCuspDatum where
  gamma:=sourceLevelInclusion g
  index:=0
  lower_ne_zero:=by
    change (integralComplexMatrix (g:SL(2,Eis))*integralComplexMatrix (cuspRepresentative 0)) 1 0≠0
    rw [cuspRepresentative_zero_eq_one,map_one,mul_one,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hc

lemma principalCuspDatum_matrix (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).matrix=integralComplexMatrix (g:SL(2,Eis)) := by
  change integralComplexMatrix (g:SL(2,Eis))*integralComplexMatrix (cuspRepresentative 0)=_
  rw [cuspRepresentative_zero_eq_one,map_one,mul_one]

lemma principalCuspDatum_height (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).heightScale=‖eisEmbedding ((g:SL(2,Eis)) 1 0)‖^2 := by
  rw [SourceCuspDatum.heightScale,principalCuspDatum_matrix,integralComplexMatrix_apply]

lemma principalCuspDatum_dual (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).dualPoint=
      -eisEmbedding ((g:SL(2,Eis)) 1 1)/eisEmbedding ((g:SL(2,Eis)) 1 0) := by
  rw [SourceCuspDatum.dualPoint,principalCuspDatum_matrix]
  rfl

lemma principalCuspDatum_multiplier (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) :
    (principalCuspDatum g hc).multiplier=
      -star (complexCharacter g)/(eisEmbedding ((g:SL(2,Eis)) 1 0))^2 := by
  rw [SourceCuspDatum.multiplier,principalCuspDatum_matrix,integralComplexMatrix_apply]
  change -star (levelTwoComplexCharacter (sourceLevelInclusion g))/_=_
  rw [sourceLevelInclusion_character]

lemma infinity_phaseNumerator_embedding (h:Eis) :
    eisEmbedding (ramifiedTraceLambda*h)=-eisLam^4*cuspFrequency h := by
  rw [map_mul,ramifiedEmbedding_traceLambda,cuspFrequency]
  field_simp [eisLam_ne_zero]
  linear_combination eisEmbedding h*TraceLambdaPhase.eisLam_sq

lemma principalCuspDatum_phase (g:levelThree) (hc:(g:SL(2,Eis)) 1 0≠0) (h:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency h*(principalCuspDatum g hc).dualPoint)=
      ShortDraftTrace.breveE (-(eisEmbedding ((g:SL(2,Eis)) 1 1)*
        (eisEmbedding (ramifiedTraceLambda*h)/eisLam^4))/eisEmbedding ((g:SL(2,Eis)) 1 0)) := by
  rw [principalCuspDatum_dual,infinity_phaseNumerator_embedding]
  congr 1
  field_simp [eisLam_ne_zero,eisEmbedding_ne_zero hc]

end CubicEisenstein
end

namespace CubicEisenstein
open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic
open CubicKubota CubicJacobiGlobal ShortDraftCusp LocalReflectionBrackets FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance smoothingField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance smoothingFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem principal_stratum_smoothed {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i}) (hchar:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (c0 U w:Eis) (hc0:c0≠0) (hr:lambda^2∣(∏i,p i)-1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (g:(∀i,(Eis⧸Ideal.span {p i})ˣ)→levelThree)
    (hC:∀v,(g v:SL(2,Eis)) 1 0=c0*∏i,p i)
    (hA:∀v,(9:Eis)*c0∣(g v:SL(2,Eis)) 0 0-(g (fun _=>1):SL(2,Eis)) 0 0)
    (hD:∀v,ramifiedTraceLambda^3*c0∣(g v:SL(2,Eis)) 1 1-(g (fun _=>1):SL(2,Eis)) 1 1)
    (σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ)
    (hfreq:∀v i,Ideal.Quotient.mk (Ideal.span {p i}) ((g v:SL(2,Eis)) 0 0)=
      (σ i:Eis⧸Ideal.span {p i})*(v i:Eis⧸Ideal.span {p i}))
    (hε:∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1)
    (j:ι→ℕ) (hj:∀i,j i<6)
    (W:ℝ→ℂ) (lo hi:ℝ) (hlo:0<lo) (hsupp:Function.support W⊆Set.Icc lo hi)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    let c:=c0*∏i,p i
    let Q:ℝ:=‖eisEmbedding c‖^2
    let hc:∀v,(g v:SL(2,Eis)) 1 0≠0:=fun v=>by
      rw [hC v];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
    let weight:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>
      ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
        (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i)
    (∑v,weight v*(principalCuspDatum (g v) (hc v)).smoothedKernel W X)=
    fixedRadialCoefficientScalar*∑'t:ThetaFullIndex,
      ((fixedConjugateCuspArray 0 t.1 t.2.1 t.2.2.1.val t.2.2.2.val*
        sourceFrequencyAngle (thetaFullFrequency t))/
        ((ramifiedScale 1 completedRamifiedStep t.2.1*
          Real.sqrt (Ideal.absNorm t.2.2.1.val:ℝ)*(Ideal.absNorm t.2.2.2.val:ℝ):ℝ):ℂ))*
      CubicReflectionKernel.paperKernel (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency t)/(27*Q^2))*
      (-(Q:ℂ)/(eisEmbedding c)^2*
        ((star (eisEmbedding (symbol c0 ((g (fun _=>1):SL(2,Eis)) 0 0)))*
          A4BadPhase c0 hc0 ((g (fun _=>1):SL(2,Eis)) 1 1) U (ramifiedTraceLambda*thetaFullFrequency t))*
        ∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (σ i)*
          phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (ε i)*
          bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
            (Ideal.Quotient.mk _ (ramifiedTraceLambda*thetaFullFrequency t)))) := by
  dsimp only
  let c:=c0*∏i,p i
  let Q:ℝ:=‖eisEmbedding c‖^2
  have hc:∀v,(g v:SL(2,Eis)) 1 0≠0:=fun v=>by
    rw [hC v];exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  let d:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>principalCuspDatum (g v) (hc v)
  let weight:=fun v:∀i,(Eis⧸Ideal.span {p i})ˣ=>
    ∏i,finiteAdditiveFourierCoeff (quotientTrace (p i) (hp i))
      (fun t=>(actualSextic (Ideal.span {p i}) (hg i)^j i) t) (v i)
  have hheight:∀v,(d v).heightScale=Q:=by
    intro v
    rw [principalCuspDatum_height,hC v]
  have hcol:=sum_smoothedKernel_common_cusp d weight 0 Q (fun _=>rfl) hheight
    W lo hi hlo hsupp hW X hX
  change (∑v,weight v*(d v).smoothedKernel W X)=_
  rw [hcol]
  congr 1
  apply tsum_congr
  intro t
  simp only [sourceCuspScale,Matrix.cons_val_zero,Complex.ofReal_one,div_one,one_pow,mul_one]
  congr 1
  let x:=ramifiedTraceLambda*thetaFullFrequency t
  have hlocal:=principal_stratum_multiplier p hp hcop hg hchar c0 U w x hc0 hr hbez
    g hC hA hD σ ε hfreq hε j hj
  calc
    _=(-(Q:ℂ)/(eisEmbedding c)^2)*
        ∑v,weight v*star (complexCharacter (g v))*
          ShortDraftTrace.breveE (-(eisEmbedding ((g v:SL(2,Eis)) 1 1)*(eisEmbedding x/eisLam^4))/
            (eisEmbedding c0*eisEmbedding (∏i,p i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      change weight v*((principalCuspDatum (g v) (hc v)).multiplier*(Q:ℂ))*
        ShortDraftTrace.breveE (-cuspFrequency (thetaFullFrequency t)*(principalCuspDatum (g v) (hc v)).dualPoint)=_
      rw [principalCuspDatum_multiplier,principalCuspDatum_phase,hC v,map_mul]
      dsimp only [c,x]
      rw [map_mul]
      ring
    _=_:=by rw [hlocal]

end CubicEisenstein

open scoped Classical BigOperators MatrixGroups

namespace ShortDraftCRT
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT PrimaryIdealUnitReindex
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_primary_unit_multiple (x:Eis) (hx:¬lambda∣x) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:primaryGenerator (Ideal.span {x})≠0:=primaryGenerator_span_ne_zero_iff x |>.mpr hx
  have hspec:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  rw [mul_comm,hu]
  exact hspec.2

lemma normalize_coprime_pair (a c:Eis) (hcop:IsCoprime a c) :
    ∃u:Eisˣ,IsCoprime (u.val*a) (u.val*c) ∧
      (lambda∣u.val*c→lambda^2∣u.val*a-1) ∧
      (¬lambda∣u.val*c→lambda^2∣u.val*c-1) := by
  have hunit (u:Eisˣ):IsCoprime (u.val*a) (u.val*c) := by
    obtain ⟨r,s,hrs⟩:=hcop
    refine ⟨r*(↑u⁻¹:Eis),s*(↑u⁻¹:Eis),?_⟩
    calc
      _=((↑u⁻¹:Eis)*u.val)*(r*a+s*c):=by ring
      _=1:=by rw [Units.inv_mul,hrs,mul_one]
  have hd (u:Eisˣ):lambda∣u.val*c↔lambda∣c := by
    constructor
    · intro h
      have hh:=dvd_mul_of_dvd_right h (↑u⁻¹:Eis)
      simpa only [←mul_assoc,Units.inv_mul,one_mul] using hh
    · intro h
      exact dvd_mul_of_dvd_right h u.val
  by_cases hc:lambda∣c
  · have ha:¬lambda∣a:=fun h=>lambda_prime_actual.not_isUnit (hcop.isUnit_of_dvd' h hc)
    obtain ⟨u,hu⟩:=exists_primary_unit_multiple a ha
    exact ⟨u,hunit u,fun _=>hu,fun hn=>False.elim (hn ((hd u).mpr hc))⟩
  · obtain ⟨u,hu⟩:=exists_primary_unit_multiple c hc
    exact ⟨u,hunit u,fun h=>False.elim (hc ((hd u).mp h)),fun _=>hu⟩

theorem exists_normalized_rational_cusp (a c:Eis) (hc:c≠0) :
    ∃a0 c0:Eis,c0≠0 ∧ c0∣c ∧ IsCoprime a0 c0 ∧
      eisEmbedding a0/eisEmbedding c0=eisEmbedding a/eisEmbedding c ∧
      (lambda∣c0→lambda^2∣a0-1) ∧ (¬lambda∣c0→lambda^2∣c0-1) := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by intro hz; exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by intro hz; exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨r,s,hrs⟩:=IsBezout.gcd_eq_sum a c
  have hred:IsCoprime a' c':=by
    refine ⟨r,s,?_⟩
    apply mul_left_cancel₀ hd
    change d*(r*a'+s*c')=d*1
    calc
      _=r*a+s*c:=by rw [ha,hc'];ring
      _=d:=hrs
      _=_:=by ring
  obtain ⟨u,hu,hua,huc⟩:=normalize_coprime_pair a' c' hred
  refine ⟨u.val*a',u.val*c',mul_ne_zero u.ne_zero hcp,?_,hu,?_,hua,huc⟩
  · refine ⟨d*(↑u⁻¹:Eis),?_⟩
    rw [hc']
    calc
      d*c'=((u.val*(↑u⁻¹:Eis))*d)*c':=by rw [Units.mul_inv,one_mul]
      _=_:=by ring
  · rw [ha,hc',map_mul,map_mul,map_mul,map_mul]
    have he:=eisEmbedding_ne_zero hd
    have hf:=eisEmbedding_ne_zero hcp
    have hu0:=eisEmbedding_ne_zero u.ne_zero
    field_simp

end ShortDraftCRT

end

end OAI
