import OAI.NumberTheory.DirichletL.Eisenstein.PrimeGaussFactors

namespace OAI

noncomputable section

namespace CubicEisenstein

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma primaryGenerator_squarefree_support (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) : primaryGenerator I=∏P∈primeSupport I,primaryPrime P := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hn: (UniqueFactorizationMonoid.normalizedFactors I).Nodup:=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  have hv:(primeSupport I).val=UniqueFactorizationMonoid.normalizedFactors I:=by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  unfold primaryGenerator
  rw [ite_eq_right hI0]
  change _=((primeSupport I).val.map primaryPrime).prod
  rw [hv]

lemma primaryPrime_isPrime_of_mem (I P:Ideal Eis) (hI:primaryGenerator I≠0)
    (hP:P∈primeSupport I) : Prime (primaryPrime P) := by
  have hp0:=primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP)
  have hs:=primaryPrime_spec P hp0
  let:P.IsMaximal:=hs.1
  apply (Ideal.span_singleton_prime hp0).mp
  rw [hs.2.2.1]
  infer_instance

lemma primaryPrime_support_coprime (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (P:Ideal Eis) (hP:P∈primeSupport I) (Q:Ideal Eis) (hQ:Q∈primeSupport I) (hne:P≠Q) :
    IsCoprime (primaryPrime P) (primaryPrime Q) := by
  have hp:=primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))
  have hq:=primaryPrime_spec Q (primaryPrime_factor_ne_zero I Q hI (Multiset.mem_toFinset.mp hQ))
  let:P.IsMaximal:=hp.1
  let:Q.IsMaximal:=hq.1
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [hp.2.2.1,hq.2.2.1]
  exact Ideal.isCoprime_of_isMaximal hne

def infinityCoefficientScalar : ℂ := star (sourceResidualFourierCoefficient 1)

theorem infinityCoefficient_squarefree (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) :
    star (sourceResidualFourierCoefficient (primaryGenerator I))=
      infinityCoefficientScalar*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  have hpr:∀P∈primeSupport I,lambda^2∣primaryPrime P-1:=by
    intro P hP
    exact (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  have he:=sourceResidualFourierCoefficient_primary_product (primeSupport I) primaryPrime
    (fun P hP=>primaryPrime_isPrime_of_mem I P hI hP) hpr
    (primaryPrime_support_coprime I hI)
  rw [←primaryGenerator_squarefree_support I hI hsq,normalizedCubicUnitGauss_eq_gaussTwo I hI hsq] at he
  exact he

theorem infinityCoefficient_squarefree_cube (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I) :
    star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))=
      infinityCoefficientScalar*(‖eisEmbedding (primaryGenerator J)‖:ℂ)*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  rw [sourceResidualFourierCoefficient_primary_cube _ hJ (primaryGenerator_spec J hJ).2 _ hI,
    star_mul,infinityCoefficient_squarefree I hI hsq]
  simp only [Complex.star_def,Complex.conj_ofReal]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceArithmeticResidue_valuation_ne_two (I P:Ideal Eis)
    (hI:primaryGenerator I≠0) (hP:P∈normalizedFactors I)
    (hS:sourceArithmeticResidue (primaryGenerator I)≠0) :
    (normalizedFactors I).count P%3≠2 := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hprime:=prime_of_normalized_factor P hP
  let p:=primaryPrime P
  have hp0:p≠0:=primaryPrime_factor_ne_zero I P hI hP
  have hps:=primaryPrime_spec P hp0
  have hp:Prime p:=primaryPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
  obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hgen:primaryGenerator I=p^(multiplicity P I)*primaryGenerator J:=by
    calc
      _=primaryGenerator (P^(multiplicity P I)*J):=congrArg primaryGenerator hJ
      _=p^(multiplicity P I)*primaryGenerator J:=by
        rw [primaryGenerator_mul,primaryGenerator_pow]
        have he:primaryGenerator P=p:=by
          rw [←hps.2.2.1,primaryGenerator_span p hp0 hps.2.2.2]
        rw [he]
  have hgJ:primaryGenerator J≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,mul_zero])
  have hpd:¬p∣primaryGenerator J:=by
    intro hd
    apply hnot
    rw [Ideal.dvd_iff_le,←hps.2.2.1,←(primaryGenerator_spec J hgJ).1,
      Ideal.span_singleton_le_span_singleton]
    exact hd
  have hcount:=multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm:(multiplicity P I)%3=2:=by rwa [hcount]
  apply hS
  rw [hgen,mul_comm,sourceArithmeticResidue_prime_power_table p hp hps.2.2.2 _ hpd,
    hm]
  norm_num

def thetaSquarefreePart (I:Ideal Eis) : Ideal Eis :=
  ∏P∈(primeSupport I).filter (fun P=>(normalizedFactors I).count P%3=1),P

def thetaCubePart (I:Ideal Eis) : Ideal Eis :=
  ∏P∈primeSupport I,P^((normalizedFactors I).count P/3)

lemma thetaSquarefreePart_squarefree (I:Ideal Eis) : Squarefree (thetaSquarefreePart I) := by
  apply IdealMobiusDivisorSum.squarefree_support_product
  exact Finset.filter_subset _ _

lemma thetaParts_mul_cube (I:Ideal Eis) (hI:I≠0)
    (he:∀P∈normalizedFactors I,(normalizedFactors I).count P%3≠2) :
    thetaSquarefreePart I*thetaCubePart I^3=I := by
  rw [thetaSquarefreePart,Finset.prod_filter,thetaCubePart,←Finset.prod_pow,←Finset.prod_mul_distrib]
  calc
    _=∏P∈primeSupport I,P^((normalizedFactors I).count P):=by
      apply Finset.prod_congr rfl
      intro P hP
      have hp:=he P (Multiset.mem_toFinset.mp hP)
      have hm:(normalizedFactors I).count P%3=0 ∨ (normalizedFactors I).count P%3=1:=by omega
      rcases hm with hm|hm
      · rw [ite_eq_right (by omega),one_mul,←pow_mul]
        congr 1
        omega
      · rw [ite_eq_left hm,←pow_mul,←pow_succ']
        congr 1
        omega
    _=(normalizedFactors I).prod:=(Finset.prod_multiset_count (normalizedFactors I)).symm
    _=I:=Ideal.prod_normalizedFactors_eq_self hI

theorem sourceArithmeticResidue_squarefree_cube_support (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hS:sourceArithmeticResidue (primaryGenerator I)≠0) :
    Squarefree (thetaSquarefreePart I) ∧
    primaryGenerator (thetaSquarefreePart I)≠0 ∧
    primaryGenerator (thetaCubePart I)≠0 ∧
    thetaSquarefreePart I*thetaCubePart I^3=I := by
  have he:=thetaParts_mul_cube I (primaryGenerator_ne_zero_ideal I hI)
    (fun P hP=>sourceArithmeticResidue_valuation_ne_two I P hI hP hS)
  have hgen:primaryGenerator I=
      primaryGenerator (thetaSquarefreePart I)*(primaryGenerator (thetaCubePart I))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart I*thetaCubePart I^3):=congrArg primaryGenerator he.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart I)≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,zero_mul])
  have hB:primaryGenerator (thetaCubePart I)≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  exact ⟨thetaSquarefreePart_squarefree I,hA,hB,he⟩

theorem sourceFourier_squarefree_cube_support (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hS:sourceResidualFourierCoefficient (primaryGenerator I)≠0) :
    ∃A B:Ideal Eis,Squarefree A ∧ primaryGenerator A≠0 ∧ primaryGenerator B≠0 ∧ A*B^3=I := by
  have hs:sourceArithmeticResidue (primaryGenerator I)≠0:=by
    intro hz
    exact hS (by rw [sourceResidualFourierCoefficient,hz,mul_zero])
  exact ⟨thetaSquarefreePart I,thetaCubePart I,
    sourceArithmeticResidue_squarefree_cube_support I hI hs⟩

theorem sourceFourier_primary_zero_of_base_zero (hC:infinityCoefficientScalar=0)
    (n:Eis) (hprimary:lambda^2∣n-1) : sourceResidualFourierCoefficient n=0 := by
  have hn:n≠0:=primary_ne_zero n hprimary
  let I:Ideal Eis:=Ideal.span {n}
  have hgen:primaryGenerator I=n:=primaryGenerator_span n hn hprimary
  have hI:primaryGenerator I≠0:=by rwa [hgen]
  by_contra hT
  have hTI:sourceResidualFourierCoefficient (primaryGenerator I)≠0:=by rwa [hgen]
  obtain ⟨A,B,hA,hAg,hBg,hAB⟩:=sourceFourier_squarefree_cube_support I hI hTI
  have harg:primaryGenerator A*(primaryGenerator B)^3=n:=by
    have he:=congrArg primaryGenerator hAB
    simpa only [primaryGenerator_mul,primaryGenerator_pow,hgen] using he
  have he:=infinityCoefficient_squarefree_cube A B hAg hBg hA
  rw [harg,hC,zero_mul,zero_mul,zero_mul] at he
  exact hT (star_eq_zero.mp he)

end

section
open Filter
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma unramifiedGaussResidue_eq_of_initial_eq (h k:Eis)
    (he:∀s:ℂ,4<s.re→0<s.im→
      unramifiedCubicGaussSeries s h=unramifiedCubicGaussSeries s k) :
    unramifiedGaussResidue h=unramifiedGaussResidue k := by
  have hh:=unramifiedGaussResidue_of_initial_relation h k 0 (fun _=>1) (fun _=>0)
    (fun _ _=>analyticAt_const) (fun _ _=>analyticAt_const)
    continuousAt_const continuousAt_const (fun s hs hi=>by simpa using he s hs hi)
  simpa only [one_mul,zero_mul,add_zero] using hh

theorem unramifiedGaussResidue_neg (h:Eis) :
    unramifiedGaussResidue (-h)=unramifiedGaussResidue h :=
  unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>unramifiedCubicGaussSeries_neg s h)

theorem unramifiedGaussResidue_lambda_pow (h:Eis) (n:ℕ) :
    unramifiedGaussResidue (h*lambda^n)=
      unramifiedGaussResidue (h*lambda^(n%3)) :=
  unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>unramifiedCubicGaussSeries_lambda_pow s h n)

theorem unramifiedGaussResidue_lambda_cube (h:Eis) :
    unramifiedGaussResidue (h*lambda^3)=unramifiedGaussResidue h := by
  simpa using unramifiedGaussResidue_lambda_pow h 3

theorem unramifiedGaussResidue_nine_family (h:Eis) (u:Eisˣ) (n:ℕ) :
    ∃j k:Fin 3,unramifiedGaussResidue (h*(9*((u:Eis)*lambda^n)))=
      unramifiedGaussResidue (h*omega^j.val*lambda^k.val) := by
  obtain ⟨j,k,hjk⟩:=unramifiedCubicGaussSeries_nine_family h u n
  exact ⟨j,k,unramifiedGaussResidue_eq_of_initial_eq _ _ (fun s _ _=>hjk s)⟩

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedResidueFamilyMass (h:Eis) : ℝ :=
  ∑a:Fin 3×Fin 3,‖unramifiedGaussResidue (h*omega^a.1.val*lambda^a.2.val)‖

lemma ramifiedResidueFamilyMass_nonneg (h:Eis) : 0≤ramifiedResidueFamilyMass h :=
  Finset.sum_nonneg (fun _ _=>norm_nonneg _)

lemma unramifiedGaussResidue_family_norm_le (h:Eis) (j k:Fin 3) :
    ‖unramifiedGaussResidue (h*omega^j.val*lambda^k.val)‖≤ramifiedResidueFamilyMass h := by
  unfold ramifiedResidueFamilyMass
  exact Finset.single_le_sum (a:=(j,k)) (s:=Finset.univ)
    (f:=fun a:Fin 3×Fin 3=>‖unramifiedGaussResidue (h*omega^a.1.val*lambda^a.2.val)‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ (j,k))

lemma unramifiedGaussResidue_nine_norm_le (h:Eis) (u:Eisˣ) (n:ℕ) :
    ‖unramifiedGaussResidue (h*(9*((u:Eis)*lambda^n)))‖≤ramifiedResidueFamilyMass h := by
  obtain ⟨j,k,hjk⟩:=unramifiedGaussResidue_nine_family h u n
  rw [hjk]
  exact unramifiedGaussResidue_family_norm_le h j k

theorem unramifiedGaussResidue_unit_lambda_family (u:Eisˣ) (n:ℕ) :
    ∃j k:Fin 3,unramifiedGaussResidue ((u:Eis)*lambda^n)=
      unramifiedGaussResidue (omega^j.val*lambda^k.val) := by
  obtain ⟨j,hj⟩:=unit_eq_sign_omega u
  refine ⟨j,⟨n%3,Nat.mod_lt _ (by decide)⟩,?_⟩
  rcases hj with hj|hj
  · rw [hj,unramifiedGaussResidue_lambda_pow]
  · rw [hj,neg_mul,unramifiedGaussResidue_neg,unramifiedGaussResidue_lambda_pow]

lemma unramifiedGaussResidue_unit_lambda_norm_le (u:Eisˣ) (n:ℕ) :
    ‖unramifiedGaussResidue ((u:Eis)*lambda^n)‖≤ramifiedResidueFamilyMass 1 := by
  obtain ⟨j,k,hjk⟩:=unramifiedGaussResidue_unit_lambda_family u n
  rw [hjk]
  simpa only [one_mul] using unramifiedGaussResidue_family_norm_le 1 j k

lemma ramifiedResidueFamilyMass_unit_lambda_le (u:Eisˣ) (n:ℕ) :
    ramifiedResidueFamilyMass ((u:Eis)*lambda^n)≤9*ramifiedResidueFamilyMass 1 := by
  calc
    _≤∑a:Fin 3×Fin 3,ramifiedResidueFamilyMass 1:=by
      apply Finset.sum_le_sum
      intro a ha
      let v:Eisˣ:=u*ramifiedOmegaUnit^a.1.val
      have he:((u:Eis)*lambda^n)*omega^a.1.val*lambda^a.2.val=
          (v:Eis)*lambda^(n+a.2.val):=by
        simp only [v,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,pow_add]
        ring
      rw [he]
      exact unramifiedGaussResidue_unit_lambda_norm_le v _
    _=_:=by simp

theorem sourceArithmeticResidue_family_bound (h:Eis) (hh:h≠0) :
    ‖sourceArithmeticResidue h‖≤
      ((∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)+3)*
        ramifiedResidueFamilyMass h/(4*(9*Real.sqrt 3/2)) := by
  have hM:=ramifiedResidueFamilyMass_nonneg h
  have hden:0<4*(9*Real.sqrt 3/2):=by positivity
  rw [sourceArithmeticResidue_eq_ramified_table h hh]
  split_ifs with hphase
  · rw [norm_div,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (show 0<(9*Real.sqrt 3/2:ℝ) by positivity)]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      _≤‖∑i:PrincipalRamifiedIndex h,principalRamifiedWeight h i (4/3)*
          unramifiedGaussResidue (principalRamifiedIndex h i)‖+
          ‖(3:ℂ)*unramifiedGaussResidue (9*h)‖:=norm_add_le _ _
      _≤(∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)*
          ramifiedResidueFamilyMass h+3*ramifiedResidueFamilyMass h:=by
        apply add_le_add
        · calc
            _≤∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)*
                unramifiedGaussResidue (principalRamifiedIndex h i)‖:=norm_sum_le _ _
            _≤∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖*
                ramifiedResidueFamilyMass h:=by
              apply Finset.sum_le_sum
              intro i hi
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left
                (unramifiedGaussResidue_nine_norm_le h i.1 (i.2.val+2)) (norm_nonneg _)
            _=_:=by rw [Finset.sum_mul]
        · rw [norm_mul,Complex.norm_ofNat]
          have hb:=unramifiedGaussResidue_nine_norm_le h (1:Eisˣ) 0
          simp only [Units.val_one,pow_zero,mul_one] at hb
          simpa only [mul_comm 9 h] using mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤3)
      _=_:=by ring
  · rw [norm_zero]
    positivity

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedDecayRatio : ℝ := (3:ℝ)^(-(1/3:ℝ))

lemma ramifiedDecayRatio_pos : 0<ramifiedDecayRatio :=
  Real.rpow_pos_of_pos (by norm_num) _

lemma ramifiedDecayRatio_lt_one : ramifiedDecayRatio<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma explicitRamifiedCoefficient_norm_le (h:Eis) (u:Eisˣ) (n:ℕ) :
    ‖explicitRamifiedCoefficient h u n‖≤(3^n:ℕ) := by
  unfold explicitRamifiedCoefficient
  split_ifs with hd
  · dsimp only
    split_ifs <;> simp [residueAdditive,breveE_norm]
  · simp

lemma ramifiedWeight_norm_scalar (n:ℕ) :
    ‖((3^n:ℕ):ℂ)^(-(4/3:ℂ))‖*(3^n:ℕ)=ramifiedDecayRatio^n := by
  have ha:0<(3:ℝ)^n:=pow_pos (by norm_num) _
  have hn:‖((3:ℂ)^n)^(-(4/3:ℂ))‖=((3:ℝ)^n)^(-(4/3:ℝ)):=by
    have he:=Complex.norm_cpow_eq_rpow_re_of_pos ha (-(4/3:ℂ))
    have hre:(-(4/3:ℂ)).re=-(4/3:ℝ):=by norm_num
    rw [hre] at he
    simpa only [Complex.ofReal_pow,Complex.ofReal_ofNat] using he
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [hn]
  calc
    ((3:ℝ)^n)^(-(4/3:ℝ))*(3:ℝ)^n=
        ((3:ℝ)^n)^(-(4/3:ℝ))*((3:ℝ)^n)^(1:ℝ):=by rw [Real.rpow_one]
    _=((3:ℝ)^n)^(-(1/3:ℝ)):=by
      rw [←Real.rpow_add ha]
      congr 1
      norm_num
    _=(3:ℝ)^((n:ℝ)*(-(1/3:ℝ))):=(Real.rpow_natCast_mul (by norm_num) n _).symm
    _=(3:ℝ)^((-(1/3:ℝ))*(n:ℝ)):=by rw [mul_comm]
    _=ramifiedDecayRatio^n:=by
      rw [Real.rpow_mul (by norm_num),Real.rpow_natCast]
      rfl

lemma principalRamifiedWeight_norm_le (h:Eis) (i:PrincipalRamifiedIndex h) :
    ‖principalRamifiedWeight h i (4/3)‖≤ramifiedDecayRatio^(i.2.val+2) := by
  unfold principalRamifiedWeight
  rw [norm_mul]
  calc
    _≤‖((3^(i.2.val+2):ℕ):ℂ)^(-(4/3:ℂ))‖*(3^(i.2.val+2):ℕ):=
      mul_le_mul_of_nonneg_left (explicitRamifiedCoefficient_norm_le h i.1 _) (norm_nonneg _)
    _=_:=ramifiedWeight_norm_scalar _

theorem principalRamifiedWeight_sum_norm_le (h:Eis) :
    (∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)≤
      6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio) := by
  have ht0:=ramifiedDecayRatio_pos.le
  have ht1:=ramifiedDecayRatio_lt_one
  have hfin:(∑n:Fin (ramifiedFrequencyBound h+1),ramifiedDecayRatio^(n.val+2))≤
      ramifiedDecayRatio^2/(1-ramifiedDecayRatio):=by
    rw [Fin.sum_univ_eq_sum_range (fun n:ℕ=>ramifiedDecayRatio^(n+2))]
    simp_rw [pow_add,mul_comm _ (ramifiedDecayRatio^2)]
    rw [←Finset.mul_sum]
    have hs: (∑n∈Finset.range (ramifiedFrequencyBound h+1),ramifiedDecayRatio^n)≤
        (1-ramifiedDecayRatio)⁻¹:=by
      rw [←tsum_geometric_of_lt_one ht0 ht1]
      exact (summable_geometric_of_lt_one ht0 ht1).sum_le_tsum _ (fun n _=>pow_nonneg ht0 n)
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hs (sq_nonneg ramifiedDecayRatio)
  calc
    _≤∑i:PrincipalRamifiedIndex h,ramifiedDecayRatio^(i.2.val+2):=
      Finset.sum_le_sum (fun i _=>principalRamifiedWeight_norm_le h i)
    _=(6:ℝ)*(∑n:Fin (ramifiedFrequencyBound h+1),ramifiedDecayRatio^(n.val+2)):=by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hc:Fintype.card Eisˣ=6:=by
        simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
      rw [hc]
      norm_num
    _≤6*(ramifiedDecayRatio^2/(1-ramifiedDecayRatio)):=mul_le_mul_of_nonneg_left hfin (by norm_num)
    _=_:=by ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def ramifiedSourceFamilyConstant : ℝ :=
  (6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3)/(4*(9*Real.sqrt 3/2))

lemma ramifiedSourceFamilyConstant_nonneg : 0≤ramifiedSourceFamilyConstant := by
  have ht:0<1-ramifiedDecayRatio:=sub_pos.mpr ramifiedDecayRatio_lt_one
  unfold ramifiedSourceFamilyConstant
  positivity

theorem sourceArithmeticResidue_nine_family_bound (h:Eis) (hh:h≠0) :
    ‖sourceArithmeticResidue h‖≤ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass h := by
  have hm:=ramifiedResidueFamilyMass_nonneg h
  refine (sourceArithmeticResidue_family_bound h hh).trans ?_
  have hw:(∑i:PrincipalRamifiedIndex h,‖principalRamifiedWeight h i (4/3)‖)+3≤
      6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3:=by
    linarith [principalRamifiedWeight_sum_norm_le h]
  calc
    _≤(6*ramifiedDecayRatio^2/(1-ramifiedDecayRatio)+3)*
        ramifiedResidueFamilyMass h/(4*(9*Real.sqrt 3/2)):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hw hm) (by positivity)
    _=ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass h:=by
      unfold ramifiedSourceFamilyConstant
      ring

theorem sourceArithmeticResidue_unit_lambda_bound (u:Eisˣ) (n:ℕ) :
    ‖sourceArithmeticResidue ((u:Eis)*lambda^n)‖≤
      9*ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass 1 := by
  refine (sourceArithmeticResidue_nine_family_bound _ (ramifiedElement_ne_zero u n)).trans ?_
  have he:=mul_le_mul_of_nonneg_left (ramifiedResidueFamilyMass_unit_lambda_le u n)
    ramifiedSourceFamilyConstant_nonneg
  convert he using 1 ; ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def extraPeriodWitness : levelThree := by
  let M:SL(2,Eis):=⟨!![1+3*omega,3*omega^2;-3,1-3*omega],by
    rw [Matrix.det_fin_two_of]
    ring⟩
  refine ⟨M,levelThree_of_entries M ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨omega,by change 1+3*omega-1=3*omega;ring⟩
  · exact ⟨omega^2,by change 3*omega^2-0=3*omega^2;ring⟩
  · exact ⟨-1,by change -3-(0:Eis)=3*(-1);ring⟩
  · exact ⟨-omega,by change 1-3*omega-1=3*(-omega);ring⟩

def rationalLowerMinusThree : SL(2,ℤ):=⟨!![1,0;-3,1],by simp [Matrix.det_fin_two]⟩

lemma extraPeriodWitness_factor :
    integralComplexMatrix (extraPeriodWitness:SL(2,Eis))=
      complexTranslation (-eisEmbedding omega)*
        integralComplexMatrix (rationalEmbedding rationalLowerMinusThree)*
        complexTranslation (eisEmbedding omega) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, integralComplexMatrix_apply,
    rationalEmbedding, Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    simp [extraPeriodWitness, rationalLowerMinusThree, complexTranslation, map_ofNat] <;> ring

lemma extraPeriodWitness_character : complexCharacter extraPeriodWitness=eisEmbedding omega := by
  change eisEmbedding (symbol (-3) (1+3*omega))=eisEmbedding omega
  apply congrArg eisEmbedding
  have hp:lambda^2∣(1+3*omega)-1:=lambda_sq_dvd_three.trans ⟨omega,by ring⟩
  rw [symbol_neg_numerator _ _ hp]
  have he:=ramified_symbol_at_omega (-(ramifiedOmegaUnit^2)) 2 2
    (Or.inr (by simp only [Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]))
  have hl:lambda^2=-3*omega:=by
    change (omega-1)^2=-3*omega
    linear_combination ramified_omega_relation
  have hnum:((-(ramifiedOmegaUnit^2):Eisˣ):Eis)*lambda^2=3:=by
    simp only [Units.val_neg,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
    rw [hl]
    calc
      _=3*omega^3:=by ring
      _=3:=by rw [omega_primitive.pow_eq_one];ring
  rw [hnum] at he
  have hw:omega^(2*2)=omega:=by
    norm_num only [Nat.reduceMul]
    calc
      omega^4=omega^3*omega:=by ring
      _=omega:=by rw [omega_primitive.pow_eq_one,one_mul]
  exact he.trans hw

lemma extraPeriodWitness_character_ne_one : complexCharacter extraPeriodWitness≠1 := by
  rw [extraPeriodWitness_character]
  intro he
  exact omega_primitive.ne_one (by decide) (eisEmbedding_injective (by simpa only [map_one] using he))

theorem cubicSource_not_eisenstein_periodic :
    ¬(∀a:Eis,∀w:HyperbolicSpace,
      cubicSourceResidualFunction (complexTranslation (eisEmbedding a) • w)=
        cubicSourceResidualFunction w) := by
  intro hperiod
  apply cubicSourceResidualFunction_ne_zero
  funext w
  have hneg (u:HyperbolicSpace):
      cubicSourceResidualFunction (complexTranslation (-eisEmbedding omega) • u)=
        cubicSourceResidualFunction u:=by
    simpa only [map_neg] using hperiod (-omega) u
  have hinv:cubicSourceResidualFunction
      (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=cubicSourceResidualFunction w:=by
    rw [extraPeriodWitness_factor,mul_smul,mul_smul,hneg,
      cubicSourceResidualFunction_rational_invariant,hperiod]
  have hchar:=cubicSourceResidualFunction_automorphy (sourceLevelInclusion extraPeriodWitness) w
  change cubicSourceResidualFunction (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=
    levelTwoComplexCharacter ⟨(extraPeriodWitness:SL(2,Eis)),levelThree_le_levelTwo extraPeriodWitness.property⟩*
      cubicSourceResidualFunction w at hchar
  rw [levelTwoComplexCharacter_restrict] at hchar
  change cubicSourceResidualFunction (integralComplexMatrix (extraPeriodWitness:SL(2,Eis)) • w)=
    complexCharacter extraPeriodWitness*cubicSourceResidualFunction w at hchar
  rw [hinv] at hchar
  have hz:(complexCharacter extraPeriodWitness-1)*cubicSourceResidualFunction w=0:=by
    linear_combination -hchar
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr extraPeriodWitness_character_ne_one)

end CubicEisenstein

end

end OAI
