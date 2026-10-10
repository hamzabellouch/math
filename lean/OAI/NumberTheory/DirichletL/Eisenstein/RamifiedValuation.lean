import OAI.NumberTheory.DirichletL.Eisenstein.EntireMellinProfile

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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedFunction_valuation_ne_two (F:Eis→ℂ)
    (hzero:∀(p:Eis),Prime p→lambda^2∣p-1→∀h:Eis,¬p∣h→∀k:ℕ,k%3=2→F (h*p^k)=0)
    (I P:Ideal Eis) (hI:primaryGenerator I≠0) (hP:P∈normalizedFactors I)
    (u:Eisˣ) (m:ℕ) (hF:F ((u.val*lambda^m)*primaryGenerator I)≠0) :
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
  have hbase:¬p∣(u.val*lambda^m)*primaryGenerator J:=by
    intro hd
    rcases hp.dvd_mul.mp hd with hd|hd
    · exact hp.not_isUnit (((ramified_primary_coprime u m p hps.2.2.2).of_mul_left_right).symm.isUnit_of_dvd hd)
    · exact hpd hd
  have hcount:=multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm:(multiplicity P I)%3=2:=by rwa [hcount]
  apply hF
  rw [hgen,show (u.val*lambda^m)*(p^(multiplicity P I)*primaryGenerator J)=
    ((u.val*lambda^m)*primaryGenerator J)*p^(multiplicity P I) by ring]
  exact hzero p hp hps.2.2.2 _ hbase _ hm

theorem ramifiedBesselValue_squarefree_cube_support (side:Bool) (h:Eis) (hh:h≠0)
    (hB:ramifiedBesselValue side h≠0) :
    ∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3 := by
  obtain ⟨n,u,m,hn,he⟩:=exists_primary_unit_lambda_factor h hh
  let T:Ideal Eis:=Ideal.span {n}
  have hT:primaryGenerator T=n:=primaryGenerator_span n (primary_ne_zero n hn) hn
  have hT0:primaryGenerator T≠0:=by rw [hT]; exact primary_ne_zero n hn
  have hFT:ramifiedBesselValue side ((u.val*lambda^m)*primaryGenerator T)≠0:=by
    rw [hT,mul_comm]
    rwa [←he]
  have hv:∀P∈normalizedFactors T,(normalizedFactors T).count P%3≠2:=by
    intro P hP
    exact ramifiedFunction_valuation_ne_two (ramifiedBesselValue side)
      (fun p hp hpp h hph k hk=>ramifiedBesselValue_prime_power_vanish side p hp hpp h hph k hk)
      T P hT0 hP u m hFT
  have hparts:=thetaParts_mul_cube T (primaryGenerator_ne_zero_ideal T hT0) hv
  have hgen:primaryGenerator T=primaryGenerator (thetaSquarefreePart T)*
      (primaryGenerator (thetaCubePart T))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart T*thetaCubePart T^3):=congrArg primaryGenerator hparts.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_mul])
  have hC:primaryGenerator (thetaCubePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  refine ⟨u,m,thetaSquarefreePart T,thetaCubePart T,thetaSquarefreePart_squarefree T,hA,hC,?_⟩
  rw [he,←hT,hgen]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma onceCuspScale_not_three_dvd (t:Eisˣ) : ¬(3:Eis)∣onceCuspScale t := by
  rintro ⟨z,hz⟩
  have hq:Ideal.absNorm (Ideal.span {onceCuspScale t})=3:=by
    simpa only [Fin.val_zero,pow_zero,mul_one] using onceCusp_q_absNorm t 0
  have he:=congrArg (fun x:Eis=>Ideal.absNorm (Ideal.span {x})) hz
  rw [hq,←Ideal.span_singleton_mul_span_singleton,map_mul,three_absNorm] at he
  omega

lemma onceCuspScale_lambda_dvd (t:Eisˣ) : lambda∣onceCuspScale t := by
  refine ⟨(t:Eis)*(traceRamifiedUnit:Eis),?_⟩
  rw [onceCuspScale,trace_eq_ramifiedUnit]
  ring

theorem ramifiedBesselValue_exact_lambda_valuation (side:Bool) (h:Eis)
    (hb:ramifiedBesselValue side h≠0) : lambda∣h ∧ ¬lambda^2∣h := by
  have hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit side):=by
    by_contra hnot
    exact hb (by simp only [ramifiedBesselValue,dite_eq_right hnot])
  have hl3:lambda∣(3:Eis):=
    (dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three
  constructor
  · have hd:=hl3.trans hf
    simpa only [sub_add_cancel] using dvd_add hd
      (onceCuspScale_lambda_dvd (ramifiedCuspScaleUnit side))
  · intro h2
    have h3:(3:Eis)∣h:=three_dvd_lambda_sq.trans h2
    have hq:(3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit side):=by
      convert dvd_sub h3 hf using 1 ; ring
    exact onceCuspScale_not_three_dvd _ hq

theorem ramifiedBesselValue_once_squarefree_cube_support (side:Bool) (h:Eis)
    (hb:ramifiedBesselValue side h≠0) :
    ∃(u:Eisˣ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda)*primaryGenerator I*(primaryGenerator J)^3 := by
  obtain ⟨hl,hnot⟩:=ramifiedBesselValue_exact_lambda_valuation side h hb
  have hh:h≠0:=by intro hz; exact hnot (hz▸dvd_zero _)
  obtain ⟨u,m,I,J,hsq,hI,hJ,hfactor⟩:=ramifiedBesselValue_squarefree_cube_support side h hh hb
  have hm2:¬2≤m:=by
    intro hm
    apply hnot
    rw [hfactor]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (pow_dvd_pow lambda hm) _) _) _
  have hm0:m≠0:=by
    intro hm
    subst m
    rw [pow_zero,mul_one] at hfactor
    have hu:IsCoprime lambda (u:Eis):=⟨0,(↑u⁻¹:Eis),by simp⟩
    have hni:IsCoprime lambda (primaryGenerator I):=coprime_of_dvd_sub_one lambda _
      ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec I hI).2)
    have hnj:IsCoprime lambda (primaryGenerator J):=coprime_of_dvd_sub_one lambda _
      ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans (primaryGenerator_spec J hJ).2)
    have hc:IsCoprime lambda h:=by rw [hfactor]; exact (hu.mul_right hni).mul_right hnj.pow_right
    exact residue_lambda_prime.not_isUnit (hc.isUnit_of_dvd hl)
  have hm:m=1:=by omega
  exact ⟨u,I,J,hsq,hI,hJ,by simpa only [hm,pow_one] using hfactor⟩

theorem ramifiedBesselValue_once_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(side:Bool) (I J:Ideal Eis),
      primaryGenerator I≠0→primaryGenerator J≠0→Squarefree I→∀u:Eisˣ,
      ‖ramifiedBesselValue side ((u.val*lambda)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*‖eisEmbedding (primaryGenerator J)‖ := by
  obtain ⟨C,hC,hbound⟩:=ramifiedBesselValue_squarefree_cube_bound
  refine ⟨C*(3:ℝ)^(1/6:ℝ),by positivity,?_⟩
  intro side I J hI hJ hsq u
  simpa only [pow_one,Nat.cast_one] using hbound side I J hI hJ hsq u 1

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_prime_norm (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    ‖sourceResidualFourierCoefficient (h*p)‖=‖sourceResidualFourierCoefficient h‖ := by
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hpp hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  rw [sourceResidualFourierCoefficient_prime_factor p hp hpp h hph,norm_mul,norm_div,
    primeCubicGauss_two_norm p hp hpp (9*h) hp9,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)),one_mul]

theorem sourceResidualFourierCoefficient_prime_product_norm {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j))
    (h:Eis) (hph:∀i∈s,¬p i∣h) :
    ‖sourceResidualFourierCoefficient (h*(∏i∈s,p i))‖=‖sourceResidualFourierCoefficient h‖ := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    have hpi:=hp i (Finset.mem_insert_self _ _)
    have hpri:=hprimary i (Finset.mem_insert_self _ _)
    have hps:∀j∈s,Prime (p j):=fun j hj=>hp j (Finset.mem_insert_of_mem hj)
    have hprs:∀j∈s,lambda^2∣p j-1:=fun j hj=>hprimary j (Finset.mem_insert_of_mem hj)
    have hcpi:IsCoprime (p i) (∏j∈s,p j):=IsCoprime.prod_right (fun j hj=>
      hpair i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) (by intro he;subst j;exact hi hj))
    have hpb:¬p i∣h*(∏j∈s,p j):=by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd|hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.not_isUnit (hcpi.isUnit_of_dvd hd)
    rw [Finset.prod_insert hi,show h*(p i*(∏j∈s,p j))=(h*(∏j∈s,p j))*p i by ring,
      sourceResidualFourierCoefficient_prime_norm (p i) hpi hpri _ hpb]
    exact ih hps hprs (fun j hj k hk hjk=>hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj=>hph j (Finset.mem_insert_of_mem hj))

lemma sourceResidualFourierCoefficient_ramified_bound (u:Eisˣ) (m:ℕ) :
    ‖sourceResidualFourierCoefficient (u.val*lambda^m)‖≤
      (‖cubicBesselNormalizer 1‖*(9*ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass 1))*
        (3:ℝ)^((m:ℝ)/6) := by
  have hc:‖cubicBesselNormalizer (u.val*lambda^m)‖=
      ‖cubicBesselNormalizer 1‖*(3:ℝ)^((m:ℝ)/6):=by
    simpa only [one_mul] using cubicBesselNormalizer_ramified_mul_norm 1 u m
  rw [sourceResidualFourierCoefficient,norm_mul,hc]
  exact (mul_le_mul_of_nonneg_left (sourceArithmeticResidue_unit_lambda_bound u m)
    (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (show (0:ℝ)≤3 by norm_num) ((m:ℝ)/6)))).trans_eq (by ring)

lemma sourceResidualFourierCoefficient_squarefree_cube_norm (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (hJ:primaryGenerator J≠0) (hsq:Squarefree I)
    (u:Eisˣ) (m:ℕ) :
    ‖sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖=
      ‖eisEmbedding (primaryGenerator J)‖*‖sourceResidualFourierCoefficient (u.val*lambda^m)‖ := by
  rw [sourceResidualFourierCoefficient_primary_cube _ hJ (primaryGenerator_spec J hJ).2 _
    (mul_ne_zero (ramifiedElement_ne_zero u m) hI),norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  congr 1
  rw [primaryGenerator_squarefree_support I hI hsq]
  apply sourceResidualFourierCoefficient_prime_product_norm
  · exact fun P hP=>primaryPrime_isPrime_of_mem I P hI hP
  · exact fun P hP=>(primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
  · exact primaryPrime_support_coprime I hI
  · intro P hP hd
    have hp:=primaryPrime_isPrime_of_mem I P hI hP
    have hpp:lambda^2∣primaryPrime P-1:=
      (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI (Multiset.mem_toFinset.mp hP))).2.2.2
    have hc:IsCoprime (u.val*lambda^m) (primaryPrime P):=
      (ramified_primary_coprime u m _ hpp).of_mul_left_right
    exact hp.not_isUnit (hc.symm.isUnit_of_dvd hd)

theorem sourceResidualFourierCoefficient_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→
      Squarefree I→∀(u:Eisˣ) (m:ℕ),
      ‖sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ := by
  let C:ℝ:=‖cubicBesselNormalizer 1‖*(9*ramifiedSourceFamilyConstant*ramifiedResidueFamilyMass 1)
  have hC:0≤C:=by dsimp only [C]; exact mul_nonneg (norm_nonneg _) (mul_nonneg
    (mul_nonneg (by norm_num) ramifiedSourceFamilyConstant_nonneg) (ramifiedResidueFamilyMass_nonneg _))
  refine ⟨1+C,by positivity,?_⟩
  intro I J hI hJ hsq u m
  rw [sourceResidualFourierCoefficient_squarefree_cube_norm I J hI hJ hsq u m]
  have he:=mul_le_mul_of_nonneg_left (sourceResidualFourierCoefficient_ramified_bound u m)
    (norm_nonneg (eisEmbedding (primaryGenerator J)))
  have hz:0≤(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖:=by positivity
  dsimp only [C] at *
  nlinarith

theorem three_cusp_coefficients_squarefree_cube_bound :
    ∃C:ℝ,0<C ∧ ∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→
      Squarefree I→∀(u:Eisˣ) (m:ℕ),
      ‖sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ ∧
      ∀side:Bool,‖ramifiedBesselValue side ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖ := by
  obtain ⟨Cs,hCs,hs⟩:=sourceResidualFourierCoefficient_squarefree_cube_bound
  obtain ⟨Cr,hCr,hr⟩:=ramifiedBesselValue_squarefree_cube_bound
  refine ⟨Cs+Cr,by positivity,?_⟩
  intro I J hI hJ hsq u m
  have hz:0≤(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖:=by positivity
  constructor
  · exact (hs I J hI hJ hsq u m).trans (by nlinarith)
  · intro side
    exact (hr side I J hI hJ hsq u m).trans (by nlinarith)

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_prime_power_vanish (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (k:ℕ) (hk:k%3=2) :
    sourceResidualFourierCoefficient (h*p^k)=0 := by
  rw [sourceResidualFourierCoefficient,sourceArithmeticResidue_prime_power_table p hp hpp h hph k,hk]
  norm_num

theorem sourceResidualFourierCoefficient_full_squarefree_cube_support (h:Eis) (hh:h≠0)
    (hB:sourceResidualFourierCoefficient h≠0) :
    ∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3 := by
  obtain ⟨n,u,m,hn,he⟩:=exists_primary_unit_lambda_factor h hh
  let T:Ideal Eis:=Ideal.span {n}
  have hT:primaryGenerator T=n:=primaryGenerator_span n (primary_ne_zero n hn) hn
  have hT0:primaryGenerator T≠0:=by rw [hT]; exact primary_ne_zero n hn
  have hFT:sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator T)≠0:=by
    rw [hT,mul_comm]
    rwa [←he]
  have hv:∀P∈normalizedFactors T,(normalizedFactors T).count P%3≠2:=by
    intro P hP
    exact ramifiedFunction_valuation_ne_two (sourceResidualFourierCoefficient)
      (fun p hp hpp h hph k hk=>sourceResidualFourierCoefficient_prime_power_vanish p hp hpp h hph k hk)
      T P hT0 hP u m hFT
  have hparts:=thetaParts_mul_cube T (primaryGenerator_ne_zero_ideal T hT0) hv
  have hgen:primaryGenerator T=primaryGenerator (thetaSquarefreePart T)*
      (primaryGenerator (thetaCubePart T))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart T*thetaCubePart T^3):=congrArg primaryGenerator hparts.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_mul])
  have hC:primaryGenerator (thetaCubePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  refine ⟨u,m,thetaSquarefreePart T,thetaCubePart T,thetaSquarefreePart_squarefree T,hA,hC,?_⟩
  rw [he,←hT,hgen]
  ring

end

section
open scoped Classical BigOperators

open ActualEisensteinCubic CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev ThetaPrimaryCubePair :=
  {I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
  {J:Ideal Eis // primaryGenerator J≠0}

def thetaPrimaryProduct (p : ThetaPrimaryCubePair) : GoodIdeal :=
  ⟨p.1.val*p.2.val^3,by
    rw [primaryGenerator_mul,primaryGenerator_pow]
    exact mul_ne_zero p.1.property.2 (pow_ne_zero 3 p.2.property)⟩

lemma thetaPrimaryProduct_injective : Function.Injective thetaPrimaryProduct := by
  intro p q he
  have hprod : p.1.val*p.2.val^3=q.1.val*q.2.val^3 := congrArg Subtype.val he
  have h := squarefree_cube_decomposition_unique
    (primaryGenerator_ne_zero_ideal _ p.2.property)
    (primaryGenerator_ne_zero_ideal _ q.2.property) p.1.property.1 q.1.property.1 hprod
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

abbrev ThetaFullIndex := Eisˣ × ℕ × ThetaPrimaryCubePair

def thetaFullFrequency (p : ThetaFullIndex) : Eis :=
  (p.1.val*lambda^p.2.1)*primaryGenerator p.2.2.1.val*
    (primaryGenerator p.2.2.2.val)^3

lemma thetaFullFrequency_product (p : ThetaFullIndex) :
    thetaFullFrequency p=p.1.val*(lambda^p.2.1*primaryGenerator (thetaPrimaryProduct p.2.2).val) := by
  simp only [thetaFullFrequency,thetaPrimaryProduct,primaryGenerator_mul,primaryGenerator_pow]
  ring

lemma thetaFullFrequency_ne_zero (p : ThetaFullIndex) : thetaFullFrequency p≠0 := by
  rw [thetaFullFrequency_product]
  exact mul_ne_zero p.1.ne_zero
    (mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
      (thetaPrimaryProduct p.2.2).property)

lemma thetaFullFrequency_span (p : ThetaFullIndex) :
    Ideal.span {thetaFullFrequency p}=ramifiedIdeal^p.2.1*(thetaPrimaryProduct p.2.2).val := by
  rw [thetaFullFrequency_product,Ideal.span_singleton_mul_left_unit p.1.isUnit,
    lambdaFactor_generator_span]

theorem thetaFullFrequency_injective : Function.Injective thetaFullFrequency := by
  rintro ⟨u,m,p⟩ ⟨v,n,q⟩ he
  have hs := congrArg (fun x:Eis=>Ideal.span {x}) he
  rw [thetaFullFrequency_span,thetaFullFrequency_span] at hs
  have hmap : lambdaFactorMap (m,thetaPrimaryProduct p)=lambdaFactorMap (n,thetaPrimaryProduct q) :=
    Subtype.ext hs
  have hij := lambdaFactorMap_bijective.1 hmap
  have hmn : m=n := congrArg Prod.fst hij
  have hpq : p=q := thetaPrimaryProduct_injective (congrArg Prod.snd hij)
  subst n
  subst q
  have huv : u=v := by
    apply Units.ext
    have hh : lambda^m*primaryGenerator (thetaPrimaryProduct p).val≠0 :=
      mul_ne_zero (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
        (thetaPrimaryProduct p).property
    apply mul_right_cancel₀ hh
    simpa only [thetaFullFrequency_product] using he
  subst v
  rfl

end

section
open scoped BigOperators Classical MatrixGroups
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

structure SourceCuspDatum where
  gamma : levelTwo
  index : Fin 3
  lower_ne_zero :
    (integralComplexMatrix (gamma:SL(2,Eis))*integralComplexMatrix (cuspRepresentative index)) 1 0≠0

namespace SourceCuspDatum

def matrix (d : SourceCuspDatum) : SL(2,ℂ) :=
  integralComplexMatrix (d.gamma:SL(2,Eis))*integralComplexMatrix (cuspRepresentative d.index)
def point (d : SourceCuspDatum) : ℂ := d.matrix 0 0/d.matrix 1 0
def dualPoint (d : SourceCuspDatum) : ℂ := -d.matrix 1 1/d.matrix 1 0
def heightScale (d : SourceCuspDatum) : ℝ := ‖d.matrix 1 0‖^2
def multiplier (d : SourceCuspDatum) : ℂ := -star (levelTwoComplexCharacter d.gamma)/(d.matrix 1 0)^2

lemma heightScale_pos (d : SourceCuspDatum) : 0<d.heightScale :=
  sq_pos_of_pos (norm_pos_iff.mpr d.lower_ne_zero)

lemma multiplier_norm (d : SourceCuspDatum) : ‖d.multiplier‖=d.heightScale⁻¹ := by
  rw [multiplier,norm_div,norm_neg,norm_star,norm_levelTwoComplexCharacter,norm_pow,one_div]
  rfl

lemma multiplier_ne_zero (d : SourceCuspDatum) : d.multiplier≠0 := by
  intro hz
  have h:=d.multiplier_norm
  rw [hz,norm_zero] at h
  exact (inv_pos.mpr d.heightScale_pos).ne' h.symm

end SourceCuspDatum

lemma exists_sourceCuspDatum (a c : Eis) (hc : c≠0) :
    ∃d:SourceCuspDatum,d.point=eisEmbedding a/eisEmbedding c := by
  obtain ⟨M,hMc,hratio⟩:=exists_integral_matrix_cusp_ratio a c hc
  obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
  let g:SL(2,ℂ):=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j)
  have he:integralComplexMatrix M=g*integralComplexMatrix T:=by
    rw [hM,map_mul,map_mul]
  have ht:integralComplexMatrix T 1 0=0:=by rw [integralComplexMatrix_apply,hT,map_zero]
  have hmc:(g*integralComplexMatrix T) 1 0≠0:=by
    rw [←he,integralComplexMatrix_apply]
    exact eisEmbedding_ne_zero hMc
  obtain ⟨hg,hr⟩:=upper_triangular_right_cusp_ratio g (integralComplexMatrix T) ht hmc
  refine ⟨⟨G,j,hg⟩,?_⟩
  change g 0 0/g 1 0=_
  rw [←hr,←he]
  exact hratio

def rationalSourceCusp (a c : Eis) (hc : c≠0) : SourceCuspDatum :=
  (exists_sourceCuspDatum a c hc).choose

lemma rationalSourceCusp_point (a c : Eis) (hc : c≠0) :
    (rationalSourceCusp a c hc).point=eisEmbedding a/eisEmbedding c :=
  (exists_sourceCuspDatum a c hc).choose_spec

def sourceCuspZFamily (j : Fin 3) (z : ℂ) : ℝ→ℂ :=
  cuspZProfile (fun w=>cubicSourceConjugateFunction (integralComplexMatrix (cuspRepresentative j) • w)) z

theorem SourceCuspDatum.reflection (d : SourceCuspDatum) (v : ℝ) (hv : 0<v) :
    cuspBarProfile cubicSourceConjugateFunction d.point v=
      d.multiplier/(v:ℂ)^2*sourceCuspZFamily d.index d.dualPoint ((d.heightScale*v)⁻¹) := by
  have he:=cuspBarProfile_conjugate_reflection_levelTwo d.gamma d.matrix
    (integralComplexMatrix (cuspRepresentative d.index)) rfl d.lower_ne_zero v hv
  rw [reflectedCuspProfile_eq_inv_square] at he
  exact he

def finiteTwistCusp (c : Eis) (hc : c≠0) (h : Eis⧸Ideal.span {c}) : SourceCuspDatum :=
  rationalSourceCusp (-3*Quotient.out h) c hc

lemma finiteTwistCusp_point (c : Eis) (hc : c≠0) (h : Eis⧸Ideal.span {c}) :
    (finiteTwistCusp c hc h).point=thetaFourierTranslation c h := by
  rw [finiteTwistCusp,rationalSourceCusp_point,thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
  simp only [map_mul,map_neg,map_ofNat]

theorem thetaTwistedCuspProfile_reflection_of_data (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (d : (Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd : ∀h,(d h).point=thetaFourierTranslation c h) (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
        ((d h).multiplier/(v:ℂ)^2*
          sourceCuspZFamily (d h).index (d h).dualPoint (((d h).heightScale*v)⁻¹)) := by
  unfold thetaTwistedCuspProfile
  apply Finset.sum_congr rfl
  intro h hh
  rw [←hd h,(d h).reflection v hv]

theorem thetaTwistedCuspProfile_reflection (Ψ : Eis→*ℂ) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (v : ℝ) (hv : 0<v) :
    thetaTwistedCuspProfile Ψ c hc v=
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
        ((finiteTwistCusp c hc h).multiplier/(v:ℂ)^2*
          sourceCuspZFamily (finiteTwistCusp c hc h).index (finiteTwistCusp c hc h).dualPoint
            (((finiteTwistCusp c hc h).heightScale*v)⁻¹)) := by
  exact thetaTwistedCuspProfile_reflection_of_data Ψ c hc (finiteTwistCusp c hc)
    (finiteTwistCusp_point c hc) v hv

theorem completedBesselProfile_finite_cusp_reflection
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (v : ℝ) (hv : 0<v) :
    thetaDerivativeScalar*CompletedGauss.completedBesselProfile Ψ thetaBesselScale v=
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
        ((finiteTwistCusp c hc h).multiplier/(v:ℂ)^2*
          sourceCuspZFamily (finiteTwistCusp c hc h).index (finiteTwistCusp c hc h).dualPoint
            (((finiteTwistCusp c hc h).heightScale*v)⁻¹)) := by
  rw [←thetaTwistedCuspProfile_eq_completedBesselProfile Ψ Q hΨ c hc hcQ v hv]
  exact thetaTwistedCuspProfile_reflection Ψ c hc v hv

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

local notation "Eis" => ActualEisensteinCubic.O

lemma horizontalPhaseMultiplier_scaled_bar (freq : ℂ) (r : ℝ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq (1/(r:ℂ))+
      Complex.I*horizontalPhaseMultiplier freq (Complex.I/(r:ℂ)))=
      2*Real.pi*Complex.I*star freq/(r:ℂ) := by
  simp only [horizontalPhaseMultiplier,star_mul,
    Complex.star_def,map_div₀,map_one,Complex.conj_ofReal,Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ; ring

namespace SubexponentialBesselCoefficients

lemma scaled_fullFunction_horizontal_hasDerivAt (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (r : ℝ) (hr : 0<r) (v : ℝ) (hv : 0<v) (z direction : ℂ) :
    HasDerivAt (fun t:ℝ=>coeff.fullFunction constant
      (upperPoint ((z+(t:ℂ)*direction)/(r:ℂ)) (v/r) (div_pos hv hr)))
      (∑'h:Eis,coeff.directionalTerm h (v/r) (z/(r:ℂ)) (direction/(r:ℂ))) 0 := by
  have h:=coeff.fullFunction_horizontal_hasDerivAt constant (v/r) (div_pos hv hr)
    (z/(r:ℂ)) (direction/(r:ℂ)) 0
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at h
  convert h using 1
  funext t
  congr 2
  ring

lemma scaled_fullFunction_wirtingerBar (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (r : ℝ) (hr : 0<r) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (fun w=>coeff.fullFunction constant
      (upperPoint (w/(r:ℂ)) (v/r) (div_pos hv hr))) z=
      ∑'h:Eis,(2*Real.pi*Complex.I*star (cuspFrequency h)/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ)) := by
  have h1:=(coeff.scaled_fullFunction_horizontal_hasDerivAt constant r hr v hv z 1).deriv
  have hI:=(coeff.scaled_fullFunction_horizontal_hasDerivAt constant r hr v hv z Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar,h1,hI]
  have hs1:=coeff.directionalTerm_summable (v/r) (div_pos hv hr) (z/(r:ℂ)) (1/(r:ℂ))
  have hsI:=(coeff.directionalTerm_summable (v/r) (div_pos hv hr) (z/(r:ℂ)) (Complex.I/(r:ℂ))).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_add hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold directionalTerm
  linear_combination coeff.term h (v/r,z/(r:ℂ))*horizontalPhaseMultiplier_scaled_bar (cuspFrequency h) r

def scaledConjugateZTerm (coeff : SubexponentialBesselCoefficients)
    (r v : ℝ) (z : ℂ) (h : Eis) : ℂ :=
  (-2*Real.pi*Complex.I*cuspFrequency h/(r:ℂ))*star (coeff.term h (v/r,z/(r:ℂ)))

theorem scaledConjugate_wirtingerZ (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (r : ℝ) (hr : 0<r) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerZ (fun w=>star (coeff.fullFunction constant
      (upperPoint (w/(r:ℂ)) (v/r) (div_pos hv hr)))) z=
      ∑'h:Eis,coeff.scaledConjugateZTerm r v z h := by
  rw [horizontalWirtingerZ_star,coeff.scaled_fullFunction_wirtingerBar constant r hr v hv z,tsum_star]
  apply tsum_congr
  intro h
  unfold scaledConjugateZTerm
  simp only [star_mul,Complex.star_def,map_div₀,map_mul,
    map_ofNat,Complex.conj_ofReal,Complex.conj_I,starRingEnd_self_apply]
  ring

theorem scaledConjugateZTerm_summable (coeff : SubexponentialBesselCoefficients)
    (r : ℝ) (hr : 0<r) (v : ℝ) (hv : 0<v) (z : ℂ) :
    Summable (coeff.scaledConjugateZTerm r v z) := by
  have hs1:=coeff.directionalTerm_summable (v/r) (div_pos hv hr) (z/(r:ℂ)) (1/(r:ℂ))
  have hsI:=(coeff.directionalTerm_summable (v/r) (div_pos hv hr) (z/(r:ℂ)) (Complex.I/(r:ℂ))).mul_left Complex.I
  apply (((hs1.add hsI).mul_left (1/2:ℂ)).star).congr
  intro h
  simp only [directionalTerm]
  change star ((1/2:ℂ)*(horizontalPhaseMultiplier (cuspFrequency h) (1/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ))+
    Complex.I*(horizontalPhaseMultiplier (cuspFrequency h) (Complex.I/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ)))))=_
  rw [show (1/2:ℂ)*(horizontalPhaseMultiplier (cuspFrequency h) (1/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ))+
    Complex.I*(horizontalPhaseMultiplier (cuspFrequency h) (Complex.I/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ))))=
      ((1/2:ℂ)*(horizontalPhaseMultiplier (cuspFrequency h) (1/(r:ℂ))+
        Complex.I*horizontalPhaseMultiplier (cuspFrequency h) (Complex.I/(r:ℂ))))*coeff.term h (v/r,z/(r:ℂ)) by ring,
    horizontalPhaseMultiplier_scaled_bar]
  unfold scaledConjugateZTerm
  simp only [star_mul,Complex.star_def,map_div₀,map_mul,
    map_ofNat,Complex.conj_ofReal,Complex.conj_I,starRingEnd_self_apply]
  ring

lemma scaledConjugateZTerm_zero (coeff : SubexponentialBesselCoefficients)
    (r v : ℝ) (z : ℂ) : coeff.scaledConjugateZTerm r v z 0=0 := by
  simp only [scaledConjugateZTerm,cuspFrequency,map_zero,zero_div,mul_zero,zero_mul]

lemma scaledConjugateZTerm_bessel (coeff : SubexponentialBesselCoefficients)
    (r : ℝ) (hr : 0<r) (v : ℝ) (hv : 0<v) (z : ℂ) (h : Eis) (hh : h≠0) :
    coeff.scaledConjugateZTerm r v z h=
      (-2*Real.pi*Complex.I*cuspFrequency h/(r:ℂ))*star (coeff.value h)*((v/r:ℝ):ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*(v/r))*
          ShortDraftTrace.breveE (-cuspFrequency h*(z/(r:ℂ))) := by
  rw [scaledConjugateZTerm,coeff.term_bessel h hh (v/r) (div_pos hv hr) (z/(r:ℂ))]
  have hx : 0<4*Real.pi*‖cuspFrequency h‖*(v/r) :=
    mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))) (div_pos hv hr)
  rw [schlafliBesselK_cubic_real _ hx]
  simp only [star_mul,breveE_star,Complex.star_def,Complex.conj_ofReal,neg_mul]
  ring

end SubexponentialBesselCoefficients

end CubicEisenstein

end

end OAI
