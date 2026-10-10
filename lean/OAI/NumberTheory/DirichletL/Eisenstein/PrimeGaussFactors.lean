import OAI.NumberTheory.DirichletL.Eisenstein.PrimeRecurrence

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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma unramifiedCubicGaussSeries_prime_two_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^2)=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 2
  have hg1:cubicUnitGaussSum (h*p^2) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero
      ((dvd_pow_self p (by decide : (2:ℕ)≠0)).trans (dvd_mul_left (p^2) h))]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^2) (p^2)=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ (p^2) (pow_ne_zero _ hp.ne_zero) (dvd_mul_left (p^2) h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^2) (p^3)= -(Ideal.absNorm (Ideal.span {p}):ℂ)^2:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 2 h
    rw [primeCubicGauss_trivial_nonzero p hp hprimary 3 (dvd_refl 3) h hph] at hh
    simpa only [mul_comm (p^2) h,mul_neg_one] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,mul_zero,zero_mul,add_zero] at he
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h hph 2
  rw [←unramifiedCubicGaussSeries_prime_two_power p hp hprimary s hs h hph] at he
  simpa only [show 2+3=5 from rfl,add_mul,one_mul] using he

theorem unramifiedGaussResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue (h*p^2) := by
  let A:ℂ→ℂ:=fun s=>1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  have hA (s:ℂ):AnalyticAt ℂ A s:=analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^5) (h*p^2) 0 A (fun _=>0)
    (fun s _=>hA s) (fun _ _=>analyticAt_const) (hA _).continuousAt continuousAt_const
    (fun s hs _=>by simpa only [A,zero_mul,add_zero] using
      unramifiedCubicGaussSeries_square_cube p hp hprimary s (by linarith) h hph)
  dsimp only [A] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [zero_mul,add_zero] using he

lemma principalResidueTerm_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (h*p^5) u n=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalResidueTerm (h*p^2) u n := by
  let c:=u.val*lambda^(n+2)
  have hA:=arithmeticResidueSum_frequency_cube (h*p^2) c p
    (ramifiedElement_ne_zero u (n+2)) (ramifiedElement_level u (n+2) (by omega)) hprimary
    (ramified_primary_coprime u (n+2) p hprimary).of_mul_left_right
  have hfreq:¬p∣h*(9*c):=ramified_prime_frequency_not_dvd h p hp hprimary hph u (n+2)
  rw [show (h*p^2)*p^3=h*p^5 by ring] at hA
  change _*arithmeticResidueSum (h*p^5) c*unramifiedGaussResidue ((h*p^5)*(9*c))=_
  rw [hA,show (h*p^5)*(9*c)=(h*(9*c))*p^5 by ring,
    unramifiedGaussResidue_square_cube p hp hprimary (h*(9*c)) hfreq]
  change _=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum (h*p^2) c*
      unramifiedGaussResidue ((h*p^2)*(9*c)))
  rw [show (h*p^2)*(9*c)=(h*(9*c))*p^2 by ring]
  ring

lemma principalArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    principalArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalArithmeticResidue (h*p^2) := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  let N:=max (ramifiedFrequencyBound (h*p^5)+1) (ramifiedFrequencyBound (h*p^2)+1)
  rw [principalArithmeticResidue_eq_sum (h*p^5) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum (h*p^2) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_right _ _)]
  simp_rw [principalResidueTerm_square_cube p hp hprimary h hph,←Finset.mul_sum]
  ring

theorem sourceArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*sourceArithmeticResidue (h*p^2) := by
  have hm:ShortDraftTrace.breveE (cuspFrequency (h*p^5))=
      ShortDraftTrace.breveE (cuspFrequency (h*p^2)):=by
    rw [show h*p^5=(((h*p^2)*p)*p)*p by ring]
    rw [sourceRayPhase_mul_primary _ p hprimary,sourceRayPhase_mul_primary _ p hprimary,
      sourceRayPhase_mul_primary _ p hprimary]
  have hp9:¬p∣9*h:=by
    have hh:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using hh
  simp only [sourceArithmeticResidue,hm]
  split_ifs
  · rw [principalArithmeticResidue_square_cube p hp hprimary h hph,
      show 9*(h*p^5)=(9*h)*p^5 by ring,
      unramifiedGaussResidue_square_cube p hp hprimary (9*h) hp9,
      show 9*(h*p^2)=(9*h)*p^2 by ring]
    ring
  · ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceArithmeticResidue_prime_pow_mod (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hh:h≠0) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=sourceArithmeticResidue (h*p^(n%3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n<3
    · rw [Nat.mod_eq_of_lt hn]
    · have hn3:3≤n:=by omega
      have he:h*p^n=(h*p^(n-3))*p^3:=by rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn3]
      rw [he,sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)),
        ih (n-3) (by omega)]
      have hm:(n-3)%3=n%3:=by omega
      rw [hm]

theorem sourceArithmeticResidue_prime_square (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^2)=0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have he:=sourceArithmeticResidue_square_cube p hp hprimary h hph
  rw [show h*p^5=(h*p^2)*p^3 by ring,
    sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero))] at he
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hz:(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceArithmeticResidue (h*p^2)=0:=by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)

theorem sourceArithmeticResidue_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
        primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have hrec:=sourceArithmeticResidue_prime_recurrence p hp hprimary h hph
  rw [sourceArithmeticResidue_prime_cube p hp hprimary h hh] at hrec
  have hrel:(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*
      primeCubicGauss p hp hprimary 1 (9*h)*sourceArithmeticResidue (h*p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceArithmeticResidue h:=by
    linear_combination hrec
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  have hG:=primeCubicGauss_one_mul_two p hp hprimary (9*h) hp9
  let q:ℂ:=(Ideal.absNorm (Ideal.span {p}):ℂ)
  have hq:q≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hpower:q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2=1:=by
    rw [←Complex.cpow_add _ _ hq,←Complex.cpow_natCast q 2,
      ←Complex.cpow_add _ _ hq]
    norm_num
  calc
    sourceArithmeticResidue (h*p)=
        (q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q^2)*sourceArithmeticResidue (h*p):=by rw [hpower,one_mul]
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*
        (q^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 (9*h)*sourceArithmeticResidue (h*p)):=by
      calc
        _=q^(-(2/3:ℂ))*q^(-(4/3:ℂ))*q*
          (primeCubicGauss p hp hprimary 1 (9*h)*primeCubicGauss p hp hprimary 2 (9*h))*
          sourceArithmeticResidue (h*p):=by rw [hG];ring
        _=_:=by ring
    _=q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*(q⁻¹*sourceArithmeticResidue h):=by rw [hrel]
    _=_:=by
      change q^(-(2/3:ℂ))*q*primeCubicGauss p hp hprimary 2 (9*h)*(q⁻¹*sourceArithmeticResidue h)=
        q^(-(2/3:ℂ))*primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h
      field_simp [hq]

theorem sourceArithmeticResidue_prime_power_table (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=
      if n%3=0 then sourceArithmeticResidue h
      else if n%3=1 then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
          primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h
      else 0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  rw [sourceArithmeticResidue_prime_pow_mod p hp hprimary h hh n]
  split_ifs with h0 h1
  · simp only [h0,pow_zero,mul_one]
  · simp only [h1,pow_one]
    exact sourceArithmeticResidue_prime_factor p hp hprimary h hph
  · have hn:n%3=2:=by omega
    rw [hn,sourceArithmeticResidue_prime_square p hp hprimary h hph]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicMulChar_inverse (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    (primeCubicMulChar p hp hprimary)⁻¹=primeCubicMulChar p hp hprimary^2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [←pow_succ'] using primeCubicMulChar_cube p hp hprimary

lemma primeCubicGauss_two_eq_star (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (h:Eis) :
    primeCubicGauss p hp hprimary 2 h=star (primeCubicGauss p hp hprimary 1 h) := by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  rw [primeCubicGauss_eq_gaussSum,primeCubicGauss_eq_gaussSum,pow_one,star_gaussSum_eq,
    primeCubicMulChar_inverse]
  have he:=mul_gaussSum_inv_eq_gaussSum
    (primeCubicMulChar p hp hprimary^2) ((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h))
  have hm:(primeCubicMulChar p hp hprimary^2) (-1 : Eis⧸Ideal.span {p})=1:=by
    rw [MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),←map_pow]
    norm_num
  rw [hm,one_mul] at he
  exact he.symm

lemma primeCubicGauss_one_normalized (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    [(Ideal.span {p}:Ideal Eis).IsMaximal] (hg:lambda∉(Ideal.span {p}:Ideal Eis)) :
    primeCubicGauss p hp hprimary 1 1/(‖eisEmbedding p‖:ℂ)=
      breveGamma2 (Ideal.span {p}) hg p rfl hp.ne_zero := by
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  unfold breveGamma2
  rw [primeCubicGauss_eq_gaussSum,pow_one,canonicalSextic_pow_two]
  simp only [map_one,AddChar.mulShift_one]
  congr 2
  apply DFunLike.ext
  intro x
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  simp only [primeCubicMulChar_mk,MulChar.ringHomComp_apply,
    symbol_prime p hp hprimary,primeValue_eq _ hg]

lemma primeCubicGauss_two_twist (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h) :
    primeCubicGauss p hp hprimary 2 h=eisEmbedding (symbol h p)*primeCubicGauss p hp hprimary 2 1 := by
  have hcop:IsCoprime p h:=hp.coprime_iff_not_dvd.mpr hph
  have he:=cubicUnitGaussSum_frequency_twist (1:Eis) p h hp.ne_zero hprimary hcop
  simp only [one_mul,←primeCubicGauss_one_eq p hp hprimary] at he
  have hs:(eisEmbedding (symbol h p))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime h p hprimary hcop.symm,map_one]
  have hstar:star (eisEmbedding (symbol h p))*eisEmbedding (symbol h p)=1:=by
    have hn:‖eisEmbedding (symbol h p)‖=1:=by
      have hn:=congrArg norm hs
      simp only [norm_pow,norm_one] at hn
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp (by simpa using hn)
    rw [mul_comm]
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using Complex.mul_conj (eisEmbedding (symbol h p))
  have hconj:=congrArg star he
  simp only [star_mul,←primeCubicGauss_two_eq_star] at hconj
  calc
    _=(star (eisEmbedding (symbol h p))*eisEmbedding (symbol h p))*primeCubicGauss p hp hprimary 2 h:=by rw [hstar,one_mul]
    _=eisEmbedding (symbol h p)*(star (eisEmbedding (symbol h p))*primeCubicGauss p hp hprimary 2 h):=by ring
    _=_:=by rw [mul_comm (star (eisEmbedding (symbol h p))),hconj]

lemma cubicBesselNormalizer_mul (h p:Eis) :
    cubicBesselNormalizer (h*p)=(‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*cubicBesselNormalizer h := by
  have hfreq:‖cuspFrequency (h*p)‖=‖cuspFrequency h‖*‖eisEmbedding p‖:=by
    rw [cuspFrequency_mul_right,norm_mul]
  have he:(2*Real.pi*‖cuspFrequency (h*p)‖:ℂ)=
      (‖eisEmbedding p‖:ℂ)*((2*Real.pi*‖cuspFrequency h‖:ℝ):ℂ):=by rw [hfreq];push_cast;ring
  unfold cubicBesselNormalizer
  rw [he,Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (by positivity)]
  push_cast
  ring

lemma prime_normalizer_powers (p:Eis) (hp:p≠0) :
    (‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))=
      (‖eisEmbedding p‖:ℂ)⁻¹ := by
  have hr:(‖eisEmbedding p‖:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  rw [←Complex.ofReal_natCast,←eisEmbedding_norm_sq_eq_absNorm_span,pow_two,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
    ←mul_assoc,←Complex.cpow_add _ _ hr,←Complex.cpow_add _ _ hr]
  convert Complex.cpow_neg_one (‖eisEmbedding p‖:ℂ) using 1 ; congr 1 ; norm_num

theorem sourceResidualFourierCoefficient_prime_factor (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      (primeCubicGauss p hp hprimary 2 (9*h)/(‖eisEmbedding p‖:ℂ))*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,cubicBesselNormalizer_mul,
    sourceArithmeticResidue_prime_factor p hp hprimary h hph,sourceResidualFourierCoefficient]
  calc
    _=((‖eisEmbedding p‖:ℂ)^(1/3:ℂ)*(Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ)))*
      primeCubicGauss p hp hprimary 2 (9*h)*(cubicBesselNormalizer h*sourceArithmeticResidue h):=by ring
    _=_:=by rw [prime_normalizer_powers p hp.ne_zero];ring

theorem sourceResidualFourierCoefficient_prime_gamma (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) [(Ideal.span {p}:Ideal Eis).IsMaximal]
    (hg:lambda∉(Ideal.span {p}:Ideal Eis)) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      eisEmbedding (symbol (9*h) p)*star (breveGamma2 (Ideal.span {p}) hg p rfl hp.ne_zero)*
        sourceResidualFourierCoefficient h := by
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  rw [sourceResidualFourierCoefficient_prime_factor p hp hprimary h hph,
    primeCubicGauss_two_twist p hp hprimary (9*h) hp9,primeCubicGauss_two_eq_star,
    ←primeCubicGauss_one_normalized p hp hprimary hg,star_div₀,Complex.star_def,Complex.conj_ofReal]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def normalizedCubicUnitGauss (n:Eis) : ℂ :=
  cubicUnitGaussSum 1 n/(‖eisEmbedding n‖:ℂ)

@[simp] lemma normalizedCubicUnitGauss_one : normalizedCubicUnitGauss 1=1 := by
  simp [normalizedCubicUnitGauss]

lemma cubicSymbol_star_mul (a b:Eis) (hb:lambda^2∣b-1) (hab:IsCoprime a b) :
    star (eisEmbedding (symbol a b))*eisEmbedding (symbol a b)=1 := by
  have hc:(eisEmbedding (symbol a b))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime a b hb hab,map_one]
  have hn:‖eisEmbedding (symbol a b)‖=1:=by
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one (by decide : (3:ℕ)≠0)).mp
    simpa only [norm_pow,norm_one,one_pow] using congrArg norm hc
  rw [mul_comm]
  simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using
    Complex.mul_conj (eisEmbedding (symbol a b))

lemma normalizedCubicUnitGauss_coprime_product (a b:Eis) (ha:a≠0) (hb:b≠0)
    (hap:lambda^2∣a-1) (hbp:lambda^2∣b-1) (hab:IsCoprime a b) :
    star (normalizedCubicUnitGauss (a*b))=
      eisEmbedding (symbol a b)*star (normalizedCubicUnitGauss a)*star (normalizedCubicUnitGauss b) := by
  have hG:=cubicUnitGaussSum_coprime_product 1 a b ha hb hap hbp hab
  simp only [one_mul] at hG
  have ht:=cubicUnitGaussSum_frequency_twist 1 b a hb hbp hab.symm
  simp only [one_mul] at ht
  have hN:eisEmbedding (symbol a b)*normalizedCubicUnitGauss (a*b)=
      normalizedCubicUnitGauss a*normalizedCubicUnitGauss b:=by
    unfold normalizedCubicUnitGauss
    rw [hG,map_mul,norm_mul,Complex.ofReal_mul]
    calc
      _=cubicUnitGaussSum 1 a*(eisEmbedding (symbol a b)*cubicUnitGaussSum a b)/
        ((‖eisEmbedding a‖:ℂ)*(‖eisEmbedding b‖:ℂ)):=by ring
      _=_:=by rw [ht];ring
  have hs:=congrArg star hN
  simp only [star_mul] at hs
  have hc:=cubicSymbol_star_mul a b hbp hab
  calc
    _=(star (eisEmbedding (symbol a b))*eisEmbedding (symbol a b))*
        star (normalizedCubicUnitGauss (a*b)):=by rw [hc,one_mul]
    _=eisEmbedding (symbol a b)*(star (normalizedCubicUnitGauss (a*b))*
        star (eisEmbedding (symbol a b))):=by ring
    _=_:=by rw [hs];ring

lemma sourceResidualFourierCoefficient_prime_normalized (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceResidualFourierCoefficient (h*p)=
      eisEmbedding (symbol (9*h) p)*star (normalizedCubicUnitGauss p)*sourceResidualFourierCoefficient h := by
  have hp9:¬p∣9*h:=by
    have ht:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using ht
  rw [sourceResidualFourierCoefficient_prime_factor p hp hprimary h hph,
    primeCubicGauss_two_twist p hp hprimary (9*h) hp9,primeCubicGauss_two_eq_star,
    normalizedCubicUnitGauss,←primeCubicGauss_one_eq p hp hprimary,
    star_div₀,Complex.star_def,Complex.conj_ofReal]
  ring

lemma primary_finset_product {ι:Type*} (s:Finset ι) (p:ι→Eis)
    (hp:∀i∈s,lambda^2∣p i-1) : lambda^2∣(∏i∈s,p i)-1 := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi ih=>
    rw [Finset.prod_insert hi]
    exact primary_mul _ _ (hp i (Finset.mem_insert_self _ _))
      (ih (fun j hj=>hp j (Finset.mem_insert_of_mem hj)))

theorem sourceResidualFourierCoefficient_prime_product {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j))
    (h:Eis) (hph:∀i∈s,¬p i∣h) :
    sourceResidualFourierCoefficient (h*(∏i∈s,p i))=
      eisEmbedding (symbol (9*h) (∏i∈s,p i))*
        star (normalizedCubicUnitGauss (∏i∈s,p i))*sourceResidualFourierCoefficient h := by
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
    have hbs:(∏j∈s,p j)≠0:=Finset.prod_ne_zero_iff.mpr (fun j hj=>(hps j hj).ne_zero)
    have hpb:¬p i∣h*(∏j∈s,p j):=by
      intro hd
      rcases hpi.dvd_mul.mp hd with hd|hd
      · exact hph i (Finset.mem_insert_self _ _) hd
      · exact hpi.not_isUnit (hcpi.isUnit_of_dvd hd)
    have hih:=ih hps hprs (fun j hj k hk hjk=>hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
      (fun j hj=>hph j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi,show h*(p i*(∏j∈s,p j))=(h*(∏j∈s,p j))*p i by ring,
      sourceResidualFourierCoefficient_prime_normalized (p i) hpi hpri _ hpb,hih]
    rw [mul_comm (p i) (∏j∈s,p j),
      normalizedCubicUnitGauss_coprime_product _ _ hbs hpi.ne_zero
        (primary_finset_product s p hprs) hpri hcpi.symm,
      symbol_mul_denominator,map_mul]
    rw [show (9:Eis)*(h*(∏j∈s,p j))=(9*h)*(∏j∈s,p j) by ring,
      symbol_mul_numerator _ _ (p i) hpri,map_mul]
    ring

lemma symbol_nine_eq_paperLambda (n:Eis) (hn:lambda^2∣n-1) :
    symbol 9 n=symbol ramifiedTraceLambda n := by
  have he:(9:Eis)=ramifiedTraceLambda^4:=by
    rw [show (4:ℕ)=2*2 from rfl,pow_mul,ramifiedTraceLambda_square]
    norm_num
  have hcop:IsCoprime ramifiedTraceLambda n:=
    ramified_character_coprime 0 1 _ n (Or.inl (by simp)) hn
  rw [he,symbol_pow_numerator _ _ hn,show (4:ℕ)=3+1 from rfl,pow_add,
    symbol_cube_of_isCoprime _ _ hn hcop,pow_one,one_mul]

theorem sourceResidualFourierCoefficient_primary_product {ι:Type*}
    (s:Finset ι) (p:ι→Eis) (hp:∀i∈s,Prime (p i))
    (hprimary:∀i∈s,lambda^2∣p i-1)
    (hpair:∀i∈s,∀j∈s,i≠j→IsCoprime (p i) (p j)) :
    star (sourceResidualFourierCoefficient (∏i∈s,p i))=
      star (sourceResidualFourierCoefficient 1)*
        star (eisEmbedding (symbol ramifiedTraceLambda (∏i∈s,p i)))*
        normalizedCubicUnitGauss (∏i∈s,p i) := by
  have he:=sourceResidualFourierCoefficient_prime_product s p hp hprimary hpair 1
    (fun i hi=>fun hd=>(hp i hi).not_isUnit (isUnit_of_dvd_one hd))
  simp only [one_mul,mul_one] at he
  rw [symbol_nine_eq_paperLambda _ (primary_finset_product s p hprimary)] at he
  rw [he,star_mul,star_mul,star_star]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceArithmeticResidue_primary_cube (b:Eis) (hb:b≠0)
    (hbprimary:lambda^2∣b-1) (h:Eis) (hh:h≠0) :
    sourceArithmeticResidue (h*b^3)=sourceArithmeticResidue h := by
  obtain ⟨s,hs,hpr⟩:=exists_primary_prime_factorization b hb hbprimary
  rw [←hs]
  clear hs hb hbprimary b
  induction s using Multiset.induction_on generalizing h with
  | empty=>simp
  | @cons p s ih=>
    have hp:=hpr p (Multiset.mem_cons_self _ _)
    have hs:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hpr q (Multiset.mem_cons_of_mem hq)
    have hs0:s.prod≠0:=by
      intro hz
      exact (hs 0 (Multiset.prod_eq_zero_iff.mp hz)).1.ne_zero rfl
    rw [Multiset.prod_cons,show h*(p*s.prod)^3=(h*s.prod^3)*p^3 by ring,
      sourceArithmeticResidue_prime_cube p hp.1 hp.2 _ (mul_ne_zero hh (pow_ne_zero _ hs0))]
    exact ih h hh hs

theorem sourceResidualFourierCoefficient_primary_cube (b:Eis) (hb:b≠0)
    (hbprimary:lambda^2∣b-1) (h:Eis) (hh:h≠0) :
    sourceResidualFourierCoefficient (h*b^3)=
      (‖eisEmbedding b‖:ℂ)*sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,cubicBesselNormalizer_mul_cube h b hb,
    sourceArithmeticResidue_primary_cube b hb hbprimary h hh,sourceResidualFourierCoefficient]
  ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSymbol_prime_zero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (x:Eis) (hpx:p∣x) : symbol x p=0 := by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  rw [symbol_prime p hp hprimary,primeValue_eq _ hg,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpx),MulChar.map_zero]

lemma cubicSymbol_zero_of_not_coprime (n:Eis) (hn:n≠0) (hprimary:lambda^2∣n-1)
    (x:Eis) (hnot:¬IsCoprime n x) : symbol x n=0 := by
  obtain ⟨s,hs,hp⟩:=exists_primary_prime_factorization n hn hprimary
  rw [←hs] at hnot ⊢
  clear hs hn hprimary n
  induction s using Multiset.induction_on with
  | empty=>exact False.elim (hnot (by simpa using (isCoprime_one_left : IsCoprime (1:Eis) x)))
  | @cons p s ih=>
    have hprime:=hp p (Multiset.mem_cons_self _ _)
    have hrest:∀q∈s,Prime q∧lambda^2∣q-1:=fun q hq=>hp q (Multiset.mem_cons_of_mem hq)
    rw [Multiset.prod_cons,symbol_mul_denominator]
    by_cases hc:IsCoprime p x
    · have hnc:¬IsCoprime s.prod x:=fun h=>hnot (by simpa using hc.mul_left h)
      rw [ih hnc hrest,mul_zero]
    · rw [cubicSymbol_prime_zero p hprime.1 hprime.2 x
        (hprime.1.irreducible.dvd_iff_not_isCoprime.mpr hc),zero_mul]

lemma cubicRow_eq_idealSymbol (I:Ideal Eis) (hI:primaryGenerator I≠0)
    (hsq:Squarefree I) (a:Eis) :
    cubicRow I hI (Ideal.Quotient.mk I a)=eisEmbedding (idealSymbol I a) := by
  rw [cubicRow_mk]
  simp_rw [canonicalSextic_pow_two,MulChar.ringHomComp_apply,←primeValue_eq]
  change (∏P:primeSupport I,eisEmbedding (primeValue P.val a))=eisEmbedding (idealSymbol I a)
  rw [←Finset.prod_subtype (primeSupport I) (fun _=>Iff.rfl)
    (fun P=>eisEmbedding (primeValue P a)),←map_prod]
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hnodup: (UniqueFactorizationMonoid.normalizedFactors I).Nodup:=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI0).mp hsq
  congr 1
  rw [idealSymbol,ite_eq_right hI0]
  change (((primeSupport I).val.map (fun P=>primeValue P a)).prod)=_
  have hv:(primeSupport I).val=UniqueFactorizationMonoid.normalizedFactors I:=by
    simpa only [primeSupport, Multiset.toFinset_val] using hnodup.dedup
  rw [hv]

lemma cubicUnitGaussSum_full (n:Eis) (hn:n≠0) (hprimary:lambda^2∣n-1) (h:Eis) :
    cubicUnitGaussSum h n=
      ∑'x:Eis⧸Ideal.span {n},eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
        quotientTrace n hn (Ideal.Quotient.mk _ h*x) := by
  let f:(Eis⧸Ideal.span {n})→ℂ:=fun x=>
    eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
      quotientTrace n hn (Ideal.Quotient.mk _ h*x)
  have hsup:Function.support f⊆{x|IsUnit x}:=by
    intro x hx
    by_contra hnot
    change ¬IsUnit x at hnot
    have hcop:¬IsCoprime n (GaussianShiftedPartition.representative n x):=by
      intro hc
      apply hnot
      have hh:=(isUnit_quotient_span_iff n (GaussianShiftedPartition.representative n x)).mpr hc
      simpa only [GaussianShiftedPartition.representative_spec] using hh
    exact hx (by simp only [f,cubicSymbol_zero_of_not_coprime n hn hprimary _ hcop,map_zero,zero_mul])
  change cubicUnitGaussSum h n=∑'x,f x
  rw [←tsum_subtype_eq_of_support_subset hsup]
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro x
  dsimp only [f]
  rw [←GaussianShiftedPartition.representative_spec n x.val,quotientTrace_mk_product]
  simp only [GaussianShiftedPartition.representative_spec]

theorem normalizedCubicUnitGauss_eq_gaussTwo (I:Ideal Eis)
    (hI:primaryGenerator I≠0) (hsq:Squarefree I) :
    normalizedCubicUnitGauss (primaryGenerator I)=gaussTwo I hI := by
  let n:=primaryGenerator I
  let:Finite (Eis⧸Ideal.span {n}):=finite_quotient_span hI
  let:Fintype (Eis⧸Ideal.span {n}):=Fintype.ofFinite _
  let e:=Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  rw [normalizedCubicUnitGauss,cubicUnitGaussSum_full _ hI (primaryGenerator_spec I hI).2 1,
    tsum_fintype]
  change (∑x:Eis⧸Ideal.span {n},eisEmbedding (symbol (GaussianShiftedPartition.representative n x) n)*
    quotientTrace n hI (Ideal.Quotient.mk _ 1*x))/(‖eisEmbedding n‖:ℂ)=
    (∑x:Eis⧸Ideal.span {n},cubicRow I hI (e x)*quotientTrace n hI x)/(‖eisEmbedding n‖:ℂ)
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
  rw [Ideal.quotEquivOfEq_mk,cubicRow_eq_idealSymbol I hI hsq]
  have hc:n∣GaussianShiftedPartition.representative n (Ideal.Quotient.mk (Ideal.span {n}) a)-a:=
    gaussRep_mk_congr n a
  have hs:symbol a n=idealSymbol I a:=by
    unfold symbol
    rw [(primaryGenerator_spec I hI).1]
  rw [symbol_congr hc,hs,map_one,one_mul]

end CubicEisenstein

end

end OAI
