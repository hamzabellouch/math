import OAI.NumberTheory.DirichletL.Eisenstein.ResidualCuspDecay

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
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

@[simp] lemma cubicUnitGaussSum_one (h:Eis):cubicUnitGaussSum h 1=1:=by
  let:Subsingleton (Eis⧸Ideal.span {(1:Eis)}):=
    Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let r:CubicUnitResidue (1:Eis):=⟨1,isUnit_one⟩
  rw [cubicUnitGaussSum,tsum_eq_single r (fun b hb=>False.elim (hb (Subsingleton.elim b r)))]
  rw [symbol_one,map_one,one_mul,
    residueAdditive_three_congr h 1 _ 0 one_ne_zero (one_dvd _)]
  simp only [residueAdditive,map_zero,mul_zero,zero_div,AddChar.map_zero_eq_one]

lemma cubicUnitGaussSum_frequency_dvd (h c:Eis) (hc:c≠0) (hch:c∣h):
    cubicUnitGaussSum h c=cubicUnitGaussSum 0 c:=
  cubicUnitGaussSum_frequency_congr h 0 c hc (by simpa only [sub_zero] using hch)

lemma cubicUnitGaussSum_prime_power_zero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (n:ℕ):
    cubicUnitGaussSum 0 (p^(n+1))=
      if 3∣n+1 then (Ideal.absNorm (Ideal.span {p}):ℂ)^n*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)-1) else 0:=by
  have he:=cubicUnitGaussSum_prime_power_lift p hp hprimary n 0
  simp only [mul_zero] at he
  rw [he,primeCubicGauss_of_dvd p hp hprimary (n+1) 0 (dvd_zero _)]
  split_ifs <;>ring

lemma cubicUnitGaussSum_prime_power_too_large (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (a k:ℕ) (hk:a+1<k):
    cubicUnitGaussSum (h*p^a) (p^k)=0:=by
  by_contra hG
  cases k with
  | zero=>omega
  | succ n=>
    have hd:=cubicUnitGaussSum_prime_power_support p hp hprimary n (h*p^a) hG
    have hd':p^(a+1)∣p^a*h:=by
      rw [mul_comm]
      exact (pow_dvd_pow p (by omega:a+1≤n)).trans hd
    rw [pow_succ] at hd'
    exact hph ((mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)).mp hd')

lemma unramifiedPrimeDeletedSeries_pow_mod (p:Eis) (hp:Prime p) (s:ℂ) (h:Eis) (n:ℕ):
    unramifiedPrimeDeletedSeries p s (h*p^n)=
      unramifiedPrimeDeletedSeries p s (h*p^(n%3)):=by
  apply tsum_congr
  intro I
  congr 1
  have he:p^n=p^(n%3)*(p^(n/3))^3:=by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  rw [he,←mul_assoc]
  exact cubicUnitGaussSum_cube_shift _ _ _ I.val.2
    (primaryGenerator_spec I.val.val I.val.2).2
    (primeDeleted_generator_coprime p hp I).symm.pow_right

theorem unramifiedCubicGaussSeries_prime_finite (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^a)=
      ∑k∈Finset.range (a+2),((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^k*
        cubicUnitGaussSum (h*p^a) (p^k)*unramifiedPrimeDeletedSeries p s (h*p^a*p^k):=by
  rw [unramifiedCubicGaussSeries_prime_reindex p hp hprimary s hs]
  apply tsum_eq_sum
  intro k hk
  have hk':a+1<k:=by
    have hh: a+2≤k:=by simpa only [Finset.mem_range,not_lt] using hk
    omega
  rw [cubicUnitGaussSum_prime_power_too_large p hp hprimary h hph a k hk',mul_zero,zero_mul]

lemma unramifiedCubicGaussSeries_prime_zero_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s h=unramifiedPrimeDeletedSeries p s h+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h*
        unramifiedPrimeDeletedSeries p s (h*p):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 0
  simpa only [pow_zero,pow_one,mul_one,cubicUnitGaussSum_one,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add,one_mul,
    primeCubicGauss_one_eq] using he

lemma unramifiedCubicGaussSeries_prime_one_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p)=unramifiedPrimeDeletedSeries p s (h*p)+
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^2*(Ideal.absNorm (Ideal.span {p}):ℂ)*
        primeCubicGauss p hp hprimary 2 h*unramifiedPrimeDeletedSeries p s h:=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 1
  have hg1:cubicUnitGaussSum (h*p) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero (dvd_mul_left p h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p) (p^2)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)*primeCubicGauss p hp hprimary 2 h:=by
    simpa only [pow_one,mul_comm p h] using cubicUnitGaussSum_prime_power_lift p hp hprimary 1 h
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,mul_zero,zero_mul,add_zero,hg2] at he
  have hr:h*p*p^2=h*p^3:=by ring
  rw [hr,unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_prime_three_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p^3)=
      (1+((Ideal.absNorm (Ideal.span {p}):ℂ)^3-(Ideal.absNorm (Ideal.span {p}):ℂ)^2)*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*unramifiedPrimeDeletedSeries p s h+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^4*
        primeCubicGauss p hp hprimary 1 h*unramifiedPrimeDeletedSeries p s (h*p):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 3
  have hg0 (k:ℕ) (hk:k≤3):cubicUnitGaussSum (h*p^3) (p^k)=cubicUnitGaussSum 0 (p^k):=
    cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      ((pow_dvd_pow p hk).trans (dvd_mul_left (p^3) h))
  have hg1:cubicUnitGaussSum (h*p^3) p=0:=by
    have hh:=hg0 1 (by omega)
    simp only [pow_one] at hh
    rw [hh]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^3) (p^2)=0:=by
    rw [hg0 2 (by omega)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^3) (p^3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1):=by
    rw [hg0 3 le_rfl]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 2
  have hg4:cubicUnitGaussSum (h*p^3) (p^4)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*primeCubicGauss p hp hprimary 1 h:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 3 h
    rw [primeCubicGauss_mod_three p hp hprimary 4] at hh
    simpa only [mul_comm (p^3) h,Nat.reduceMod] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,hg4,mul_zero,zero_mul,add_zero] at he
  have hr6:h*p^3*p^3=h*p^6:=by ring
  have hr7:h*p^3*p^4=h*p^7:=by ring
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp,hr6,hr7,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 6,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 7] at he
  norm_num only [Nat.reduceMod,pow_zero,pow_one,mul_one] at he
  exact he.trans (by ring)

theorem unramifiedCubicGaussSeries_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h*
        unramifiedCubicGaussSeries s (h*p):=by
  rw [unramifiedCubicGaussSeries_prime_three_power p hp hprimary s hs h hph,
    unramifiedCubicGaussSeries_prime_zero_power p hp hprimary s hs h hph,
    unramifiedCubicGaussSeries_prime_one_power p hp hprimary s hs h hph]
  have hg:=primeCubicGauss_one_mul_two p hp hprimary h hph
  linear_combination ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
    (Ideal.absNorm (Ideal.span {p}):ℂ)*unramifiedPrimeDeletedSeries p s h*hg

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

structure SubexponentialBesselCoefficients where
  value : ActualEisensteinCubic.O→ℂ
  growth : ∀epsilon : ℝ,0<epsilon → ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
    ‖value h‖≤C*Real.exp (epsilon*‖cuspFrequency h‖)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def term (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : ℂ :=
  if h=0 then 0 else (coeff.value h/cubicBesselNormalizer h)*(p.1:ℂ)^(2/3:ℂ)*
    sourceFourierKernel (4/3) (cuspFrequency h*p.1)*ShortDraftTrace.breveE (cuspFrequency h*p.2)

def amplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else coeff.value h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma term_bessel (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.term h (v,z)=coeff.value h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [term,ite_eq_right hh]
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hn := cubicBesselNormalizer_ne_zero h hh
  have hp : (v:ℂ)^3*(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ) := by
    rw [←Complex.cpow_ofNat (v:ℂ) 3,←Complex.cpow_add _ _ hv0]
    congr 1
    ring
  calc
    _ = (coeff.value h/cubicBesselNormalizer h)*(v:ℂ)^3*
        ((v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z) := by rw [←hp];ring
    _ = _ := by
      rw [sourceFourierKernel_cubic_height h hh v hv]
      field_simp

lemma term_eq_amplitude (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (z : ℂ) :
    coeff.term h (v,z)=coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  by_cases hh : h=0
  · simp only [term,amplitude,ite_eq_left hh,zero_mul]
  · rw [coeff.term_bessel h hh v hv z,amplitude,ite_eq_right hh]

lemma term_continuousOn (h : ActualEisensteinCubic.O) :
    ContinuousOn (coeff.term h) {p : ℝ × ℂ | 0<p.1} := by
  unfold term
  by_cases hh : h=0
  · simp only [ite_eq_left hh]
    exact continuousOn_const
  simp only [ite_eq_right hh]
  intro p hp
  change 0<p.1 at hp
  have hpow : ContinuousAt (fun q : ℝ × ℂ => (q.1:ℂ)^(2/3:ℂ)) p :=
    (Complex.continuousAt_ofReal_cpow_const p.1 (2/3:ℂ) (Or.inr hp.ne')).comp continuousAt_fst
  have hsource : ContinuousAt (fun q : ℝ × ℂ => sourceFourierKernel (4/3) (cuspFrequency h*q.1)) p :=
    (sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp (by fun_prop)
  have hphase : Continuous (fun q : ℝ × ℂ => ShortDraftTrace.breveE (cuspFrequency h*q.2)) := by
    change Continuous (fun q : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2))))
    fun_prop
  exact (((continuousAt_const.mul hpow).mul hsource).mul hphase.continuousAt).continuousWithinAt

lemma slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.term h p‖≤C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hb : 0<b := ha.trans_le hab
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hCu := cubicBesselUpperAway_pos delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*b*cubicBesselUpperAway delta,by positivity,?_⟩
  intro h p hp
  have hv : 0<p.1 := ha.trans_le hp.1
  by_cases hh : h=0
  · simp only [term,ite_eq_left hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*p.1 := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hp.1 ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [show p=(p.1,p.2) from rfl,coeff.term_bessel h hh _ hv,
    norm_mul,norm_mul,norm_mul,breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*b*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*p.1)/2)) :=
      mul_le_mul (mul_le_mul (hcoeff h hh) hp.2 hv.le (by positivity))
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*b*cubicBesselUpperAway delta)*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*p.1)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*p.1)/2=
        -(4*Real.pi*‖cuspFrequency h‖*p.1/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hp.1 (mul_pos Real.pi_pos hr).le]

lemma summable (p : ℝ × ℂ) (hp : 0<p.1) : Summable (fun h : ActualEisensteinCubic.O => coeff.term h p) := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound p.1 p.1 hp le_rfl
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h p ⟨le_rfl,le_rfl⟩)
    ((summable_exp_neg_cuspFrequency_norm (Real.pi*p.1) (mul_pos Real.pi_pos hp)).mul_left C)

def series (p : ℝ × ℂ) : ℂ := ∑'h : ActualEisensteinCubic.O,coeff.term h p

lemma series_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn coeff.series {p : ℝ × ℂ | p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  apply continuousOn_tsum (u := fun h : ActualEisensteinCubic.O => C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))
  · intro h
    exact (coeff.term_continuousOn h).mono (fun p hp => ha.trans_le hp.1)
  · exact (summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound

lemma series_continuousOn : ContinuousOn coeff.series {p : ℝ × ℂ | 0<p.1} := by
  intro p hp
  change 0<p.1 at hp
  have hclosed := coeff.series_continuousOn_slab (p.1/2) (2*p.1) (by linarith) (by linarith)
  have hnb : {q : ℝ × ℂ | q.1∈Set.Icc (p.1/2) (2*p.1)}∈𝓝 p :=
    continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  exact (hclosed.continuousAt hnb).continuousWithinAt

lemma series_uniform (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    TendstoUniformlyOn (fun t : Finset ActualEisensteinCubic.O => fun p : ℝ × ℂ => ∑h∈t,coeff.term h p)
      coeff.series atTop {p : ℝ × ℂ | p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  exact tendstoUniformlyOn_tsum
    ((summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C) hbound

lemma series_bessel (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.series (v,z)=∑'h : ActualEisensteinCubic.O,coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  exact tsum_congr (fun h => coeff.term_eq_amplitude v hv h z)

lemma series_period (v : ℝ) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.series (v,z+3*ConcreteTraceCRT.eisEmbedding n)=coeff.series (v,z) := by
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · simp only [term,ite_eq_left hh]
  simp only [term,ite_eq_right hh]
  rw [mul_add,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

def function (w : HyperbolicSpace) : ℂ := coeff.series (hyperbolicHeight w,hyperbolicHorizontal w)

lemma function_continuous : Continuous coeff.function := by
  apply continuous_iff_continuousAt.mpr
  intro w
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  have hp : (hyperbolicHeight w,hyperbolicHorizontal w)∈{p : ℝ × ℂ | 0<p.1} := hyperbolicHeight_pos w
  exact (coeff.series_continuousOn.continuousAt (hopen.mem_nhds hp)).comp
    (f := fun u : HyperbolicSpace => (hyperbolicHeight u,hyperbolicHorizontal u))
    (hyperbolicHeight_continuous.prodMk hyperbolicHorizontal_continuous).continuousAt

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma series_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,coeff.series (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v k := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
    ShortDraftTrace.breveE (-cuspFrequency k*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => coeff.amplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*z)+starRingEnd ℂ (cuspFrequency h*z)))*
      Complex.exp (2*Real.pi*Complex.I*((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
    change ‖(coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z))*
      ShortDraftTrace.breveE (-cuspFrequency k*z)‖≤_
    rw [←coeff.term_eq_amplitude v hv h z,norm_mul,breveE_norm,mul_one]
    exact hbound h (v,z) ⟨le_rfl,le_rfl⟩
  have hi (h : ActualEisensteinCubic.O) : IntegrableOn (f h) periodDomain volume :=
    (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hfbound h))
  have hnorm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,‖f h z‖)≤
      volume.real periodDomain*(C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) := by
    have hh := integral_mono_ae (hi h).norm (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)))
      (Eventually.of_forall (hfbound h))
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hs : Summable (fun h : ActualEisensteinCubic.O => ∫z in periodDomain,‖f h z‖) := by
    apply Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
    exact ((summable_exp_neg_cuspFrequency_norm (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
      (volume.real periodDomain)
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=
      if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v h else 0 := by
    change (∫z in periodDomain,coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=_
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_cusp_character_product]
    split_ifs <;> ring
  calc
    _ = ∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        change (∑'h : ActualEisensteinCubic.O,coeff.term h (v,z))*ShortDraftTrace.breveE (-cuspFrequency k*z)=_
        rw [←tsum_mul_right]
        apply tsum_congr
        intro h
        rw [coeff.term_eq_amplitude v hv h z])
    _ = ∑'h : ActualEisensteinCubic.O,∫z in periodDomain,f h z := (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = ∑'h : ActualEisensteinCubic.O,if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v h else 0 := tsum_congr hterm
    _ = _ := by simp

lemma series_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => coeff.series (v,z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  exact (coeff.series_continuousOn.continuousAt (hopen.mem_nhds hv)).comp
    (f := fun z : ℂ => (v,z)) (by fun_prop)

def fullFunction (constant : ℂ) (w : HyperbolicSpace) : ℂ :=
  constant*(hyperbolicHeight w:ℂ)^(2/3:ℂ)+coeff.function w

lemma fullFunction_continuous (constant : ℂ) : Continuous (coeff.fullFunction constant) := by
  have hp : Continuous (fun w : HyperbolicSpace => (hyperbolicHeight w:ℂ)^(2/3:ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (Complex.continuousAt_ofReal_cpow_const (hyperbolicHeight w) (2/3:ℂ)
      (Or.inr (hyperbolicHeight_pos w).ne')).comp (f := hyperbolicHeight) hyperbolicHeight_continuous.continuousAt
  exact (continuous_const.mul hp).add coeff.function_continuous

lemma fullFunction_fourier (constant : ℂ) (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,coeff.fullFunction constant (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(if k=0 then constant*(v:ℂ)^(2/3:ℂ) else coeff.amplitude v k) := by
  have hphase : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-cuspFrequency k*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  have hc0 := periodDomain_integrable_of_continuous
    (fun z => (constant*(v:ℂ)^(2/3:ℂ))*ShortDraftTrace.breveE (-cuspFrequency k*z))
    (continuous_const.mul hphase)
  have hcn := periodDomain_integrable_of_continuous
    (fun z => coeff.series (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))
    ((coeff.series_height_continuous v hv).mul hphase)
  simp_rw [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,add_mul]
  rw [integral_add hc0 hcn,integral_const_mul,integral_cusp_character,coeff.series_fourier v hv k]
  by_cases hk : k=0
  · simp only [ite_eq_left hk,amplitude,mul_zero]
    ring
  · simp only [ite_eq_right hk,mul_zero,zero_add]

lemma fullFunction_period (constant : ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.fullFunction constant (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=
      coeff.fullFunction constant (upperPoint z v hv) := by
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint,
    coeff.series_period]

lemma fullFunction_height_continuous (constant : ℂ) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => coeff.fullFunction constant (upperPoint z v hv)) := by
  have hc := coeff.series_height_continuous v hv
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  fun_prop

lemma fullFunction_height_memLp (constant : ℂ) (v : ℝ) (hv : 0<v) :
    MemLp (fun z : ℂ => coeff.fullFunction constant (cuspCoordinateLift (v,z))) 2
      (volume.restrict periodDomain) := by
  simp_rw [cuspCoordinateLift_positive v _ hv]
  have hc := coeff.fullFunction_height_continuous constant v hv
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hn : Continuous (fun z : ℂ => ‖coeff.fullFunction constant (upperPoint z v hv)‖^2) := by
    fun_prop
  apply (hn.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

end SubexponentialBesselCoefficients
end CubicEisenstein

open scoped BigOperators Classical

namespace ShortDraftCRT
variable {R : Type*} [CommRing R]

theorem inverse_residue_congr (D r r0 u u0 : R) (hcop : IsCoprime D r)
    (hr : D∣r-r0) (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) : D∣u-u0 := by
  apply hcop.dvd_of_dvd_mul_right
  have hh := dvd_sub (dvd_sub hu hu0) (dvd_mul_of_dvd_right hr u0)
  convert hh using 1 ; ring

theorem inverse_weight_residue_congr (D r r0 u u0 d d0 : R)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    D∣(-d*u)-(-d0*u0) := by
  have hi := inverse_residue_congr D r r0 u u0 hcop hr hu hu0
  have hh := dvd_add (dvd_mul_of_dvd_left hd u) (dvd_mul_of_dvd_right hi d0)
  convert dvd_neg.mpr hh using 1 ; ring

theorem fixed_additive_sector {K : Type*} [Field K]
    (ι : R→+*K) (ψ : AddChar K ℂ) (lam D r r0 u u0 d d0 x : R)
    (hlam : ι lam≠0) (hD : ι D≠0)
    (hperiod : ∀y : R,ψ (ι y/ι lam)=1)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    ψ (ι (-d*u)*ι x/(ι lam*ι D))=
      ψ (ι (-d0*u0)*ι x/(ι lam*ι D)) :=
  addChar_congr_of_dvd ι ψ lam D (-d*u) (-d0*u0) x hlam hD hperiod
    (inverse_weight_residue_congr D r r0 u u0 d d0 hcop hr hu hu0 hd)

theorem strong_sector_additive_congruences (M lam c r r0 d d0 : R)
    (hlam : lam^3∣M) (hc : c∣M) (hr : M^2∣r-r0) (hd : M*c∣d-d0) :
    lam^3*c∣r-r0 ∧ lam^3*c∣d-d0 := by
  constructor
  · apply (show lam^3*c∣M^2 by simpa only [pow_two] using mul_dvd_mul hlam hc).trans hr
  · exact (mul_dvd_mul hlam (dvd_refl c)).trans hd

end ShortDraftCRT

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def translatedHeightCompact (M:levelTwo) (a b:ℝ) : Set KernelQuotient :=
  kernelSourceAction M '' cuspHeightQuotientCompact a b

lemma translatedHeightCompact_isCompact (M:levelTwo) (a b:ℝ) (ha:0<a) :
    IsCompact (translatedHeightCompact M a b) :=
  (cuspHeightQuotientCompact_isCompact a b ha).image (kernelSourceAction_continuous M)

def translatedHeightFourier (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) : KernelQuotientL2→L[ℂ]ℂ :=
  (kernelCuspHeightFourier a b ha ρ h).comp (kernelSourcePullback M).toContinuousLinearMap

lemma translatedHeightFourier_integral (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h M F=
      ∫w in cuspPeriodStrip a b,F (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  rw [translatedHeightFourier,ContinuousLinearMap.comp_apply,kernelCuspHeightFourier_integral]
  have he:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp (kernelSourcePullback_ae_eq M F)
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspWeightedFourierPhase ρ h w) hw

lemma translatedHeightFourier_restrict (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (F:KernelQuotientL2) :
    translatedHeightFourier a b ha ρ h M
      (kernelMassRestrictionCLM (translatedHeightCompact M a b)
        (translatedHeightCompact_isCompact M a b ha).measurableSet F)=translatedHeightFourier a b ha ρ h M F := by
  rw [translatedHeightFourier_integral,translatedHeightFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha).measurableSet F)
  have he:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hsource
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  have hm:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedHeightCompact M a b :=
    ⟨_,cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspWeightedFourierPhase ρ h w)
    (hw.trans (Set.indicator_of_mem hm _))

def translatedHeightFamily (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) : ℂ :=
  translatedHeightFourier a b ha ρ h M
    (kernelLocalCorrectedSeed (translatedHeightCompact M a b)
      (translatedHeightCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)

lemma translatedHeightFamily_analyticAt (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) (hs:s.re≠1) (hi:s.im≠0) :
    AnalyticAt ℂ (translatedHeightFamily a b ha ρ h M) s :=
  (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (translatedHeightFourier a b ha ρ h M) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (translatedHeightCompact_isCompact M a b ha)
        2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma translatedHeightFamily_residue_limit (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) :
    Tendsto (fun s:ℂ=>(s-4/3)*translatedHeightFamily a b ha ρ h M s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (translatedHeightFourier a b ha ρ h M cubicEisensteinResidue)) := by
  have hh:=(translatedHeightFourier a b ha ρ h M).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (translatedHeightCompact_isCompact M a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,translatedHeightFourier_restrict,
    translatedHeightFamily] using hh

lemma translatedHeightFamily_initial (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ)
    (h:Eis) (M:levelTwo) (s:ℂ) (hs:4<s.re) (hi:0<s.im) :
    translatedHeightFamily a b ha ρ h M s=
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (sourceComplexMatrix M • w)*
        cuspWeightedFourierPhase ρ h w∂hyperbolicVolume := by
  have hcorrected:kernelCorrectedSeed 2 3 (by norm_num) (by norm_num) s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith) := by
    filter_upwards [kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi] with q hq
    change kernelQuotientSeed 2 3 s q+kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s q=_
    rw [hq]
    ring
  have hlocal:=kernelLocalCorrectedSeed_ae_eq _ (translatedHeightCompact_isCompact M a b ha)
    2 3 (by norm_num) (by norm_num) s
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hlocal
  have hE:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hcorrected
  have hp:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hsource
  have hpE:=(kernelCuspHeight_quasiMeasurePreserving a b ha).ae_eq_comp hE
  rw [translatedHeightFamily,translatedHeightFourier_integral]
  apply integral_congr_ae
  filter_upwards [hp,hpE,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwe hwm
  have hm:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedHeightCompact M a b :=
    ⟨_,cuspPeriodStrip_image_subset a b ha ⟨w,hwm,rfl⟩,rfl⟩
  dsimp only [Function.comp_def] at hw hwe
  rw [hw,Set.indicator_of_mem hm,hwe,kernelSourceAction_mk,kernelQuotientEisenstein_mk]

end CubicEisenstein

end

end OAI
