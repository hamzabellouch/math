import OAI.NumberTheory.DirichletL.Eisenstein.PrimePowerGaussSums

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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def cubicBesselDensityDeriv (x t : ℝ) : ℝ := -(x/(2*t))*cubicBesselDensity x t

lemma cubicBesselDensity_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y : ℝ => cubicBesselDensity y t) (cubicBesselDensityDeriv x t) x := by
  have he := ((((hasDerivAt_id x).pow 2).div_const (4*t)).const_sub (-t)).exp.const_mul (t^(-(2:ℝ)/3))
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one] at he
  convert he using 1
  · funext y
    rfl
  · unfold cubicBesselDensityDeriv cubicBesselDensity
    ring

lemma cubic_exp_damping (y : ℝ) : y*Real.exp (-y)≤1 := by
  have hy : y≤Real.exp y := by linarith [Real.add_one_le_exp y]
  calc
    _ ≤ Real.exp y*Real.exp (-y) := mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
    _ = 1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]

lemma cubicBesselDensityDeriv_bound (delta x t : ℝ)
    (hdelta : 0<delta) (hx : delta≤x) (ht : 0<t) :
    ‖cubicBesselDensityDeriv x t‖≤
      (4/delta)*Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
  have hxp : 0<x := hdelta.trans_le hx
  have hdamp : (x/(2*t))*Real.exp (-(x^2/(8*t)))≤4/x := by
    have hrewrite : x/(2*t)=(4/x)*(x^2/(8*t)) := by field_simp;ring
    rw [hrewrite,mul_assoc]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (cubic_exp_damping (x^2/(8*t))) (by positivity : 0≤4/x)
  have hyoung : x/2-t/2≤x^2/(8*t) :=
    (le_div_iff₀ (show 0<8*t by positivity)).mpr (by nlinarith [sq_nonneg (x-2*t)])
  have he : Real.exp (-t-x^2/(4*t))≤
      Real.exp (-x/2)*Real.exp (-t/2)*Real.exp (-(x^2/(8*t))) := by
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsplit : x^2/(4*t)=2*(x^2/(8*t)) := by ring
    rw [hsplit]
    linarith
  have hnorm : ‖cubicBesselDensityDeriv x t‖=
      (x/(2*t))*t^(-(2:ℝ)/3)*Real.exp (-t-x^2/(4*t)) := by
    unfold cubicBesselDensityDeriv cubicBesselDensity
    rw [norm_mul,norm_neg,Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)]
    ring
  rw [hnorm]
  calc
    _ ≤ (x/(2*t))*t^(-(2:ℝ)/3)*
        (Real.exp (-x/2)*Real.exp (-t/2)*Real.exp (-(x^2/(8*t)))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((x/(2*t))*Real.exp (-(x^2/(8*t))))*
        Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by ring
    _ ≤ (4/x)*Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
      gcongr
    _ ≤ _ := by
      gcongr

lemma cubicBesselDerivativeMajorant_integrable :
    IntegrableOn (fun t : ℝ => t^(-(2:ℝ)/3)*Real.exp (-t/2)) (Set.Ioi 0) volume := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (s:=-(2:ℝ)/3) (p:=1) (b:=1/2)
    (by norm_num) (by norm_num) (by norm_num)
  apply hh.congr
  filter_upwards with t
  rw [Real.rpow_one]
  congr 1
  congr 1
  ring

lemma cubicBesselDensityDeriv_integrable (x : ℝ) (hx : 0<x) :
    IntegrableOn (cubicBesselDensityDeriv x) (Set.Ioi 0) volume := by
  apply (cubicBesselDerivativeMajorant_integrable.const_mul ((4/x)*Real.exp (-x/2))).mono'
  · unfold cubicBesselDensityDeriv cubicBesselDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselDensityDeriv_bound x x t hx le_rfl ht

lemma cubicBesselIntegral_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun y : ℝ => ∫t in Set.Ioi (0:ℝ),cubicBesselDensity y t)
      (∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  have hU : Set.Ioi delta∈𝓝 x := isOpen_Ioi.mem_nhds (by
    change delta<x
    dsimp [delta]
    linarith)
  have hbound : ∀ᵐt ∂volume.restrict (Set.Ioi (0:ℝ)),∀y∈Set.Ioi delta,
      ‖cubicBesselDensityDeriv y t‖≤(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : 0<t := ht
    intro y hy
    have hyp : 0<y := hdelta.trans hy
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (F := cubicBesselDensity) (F' := cubicBesselDensityDeriv)
    (bound := fun t => (4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2))) hU
    (Eventually.of_forall (fun y => by unfold cubicBesselDensity;fun_prop))
    (cubicBesselDensity_integrable x)
    (by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
    hbound (cubicBesselDerivativeMajorant_integrable.const_mul (4/delta))
    (Eventually.of_forall (fun t y _ => cubicBesselDensity_hasDerivAt y t))
  exact h.2

def cubicBesselRealDeriv (x : ℝ) : ℝ :=
  (-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)+
    (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t)

def schlafliBesselK_cubic_derivative (x : ℝ) : ℂ := (cubicBesselRealDeriv x:ℂ)

lemma schlafliBesselK_cubic_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun y : ℝ => schlafliBesselK (1/3) y)
      (schlafliBesselK_cubic_derivative x) x := by
  have hp : HasDerivAt (fun y : ℝ => (1/2:ℝ)*(y/2)^(-(1:ℝ)/3))
      ((-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)) x := by
    have hh := (((hasDerivAt_id x).div_const 2).rpow_const
      (p:=-(1:ℝ)/3) (Or.inl (by positivity : x/2≠0))).const_mul (1/2:ℝ)
    convert hh using 1 <;> norm_num ; ring
  have hr := hp.mul (cubicBesselIntegral_hasDerivAt x hx)
  have hreal : HasDerivAt (fun y : ℝ => (1/2:ℝ)*(y/2)^(-(1:ℝ)/3)*
      (∫t in Set.Ioi (0:ℝ),cubicBesselDensity y t)) (cubicBesselRealDeriv x) x := by
    exact hr
  apply hreal.ofReal_comp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact schlafliBesselK_cubic_real y hy

lemma cubicBesselDerivativeMajorant_integral :
    (∫t in Set.Ioi (0:ℝ),t^(-(2:ℝ)/3)*Real.exp (-t/2))=
      (2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3) := by
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1/3:ℝ)) (r := (1/2:ℝ)) (by norm_num) (by norm_num)
  convert hh using 1 <;> norm_num ; congr 2 ; funext t ; ring_nf

lemma cubicBesselIntegral_norm_bound (x : ℝ) :
    ‖∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t‖≤
      Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hpos : 0≤∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselDensity_nonneg x t ht.le
  rw [Real.norm_of_nonneg hpos]
  exact cubicBesselIntegral_upper x

lemma cubicBesselIntegralDeriv_norm_bound (delta x : ℝ) (hdelta : 0<delta) (hx : delta≤x) :
    ‖∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t‖≤
      (4/delta)*Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hi := cubicBesselDensityDeriv_integrable x (hdelta.trans_le hx)
  have hb := integral_mono_ae hi.norm
    (cubicBesselDerivativeMajorant_integrable.const_mul ((4/delta)*Real.exp (-x/2)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselDensityDeriv_bound delta x t hdelta hx ht)
  rw [integral_const_mul,cubicBesselDerivativeMajorant_integral] at hb
  exact (norm_integral_le_integral_norm _).trans hb

def cubicBesselDerivativeUpper (delta : ℝ) : ℝ :=
  ((1/12:ℝ)*(delta/2)^(-(4:ℝ)/3)+
    (1/2:ℝ)*(delta/2)^(-(1:ℝ)/3)*(4/delta))*
      ((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

lemma cubicBesselDerivativeUpper_nonneg (delta : ℝ) (hdelta : 0<delta) :
    0≤cubicBesselDerivativeUpper delta := by
  unfold cubicBesselDerivativeUpper
  positivity

lemma schlafliBesselK_cubic_derivative_bound (delta x : ℝ) (hdelta : 0<delta) (hx : delta≤x) :
    ‖schlafliBesselK_cubic_derivative x‖≤cubicBesselDerivativeUpper delta*Real.exp (-x/2) := by
  have hxp : 0<x := hdelta.trans_le hx
  have hp1 : (x/2)^(-(1:ℝ)/3)≤(delta/2)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hp4 : (x/2)^(-(4:ℝ)/3)≤(delta/2)^(-(4:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  rw [schlafliBesselK_cubic_derivative,Complex.norm_real,cubicBesselRealDeriv]
  calc
    _ ≤ ‖(-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)‖+
        ‖(1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t)‖ := norm_add_le _ _
    _ = (1/12:ℝ)*(x/2)^(-(4:ℝ)/3)*‖∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t‖+
        (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*‖∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t‖ := by
      have hn4 : ‖(x/2)^(-(4:ℝ)/3)‖=(x/2)^(-(4:ℝ)/3) :=
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      have hn1 : ‖(x/2)^(-(1:ℝ)/3)‖=(x/2)^(-(1:ℝ)/3) :=
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      simp only [norm_mul,hn4,hn1]
      norm_num
    _ ≤ (1/12:ℝ)*(delta/2)^(-(4:ℝ)/3)*
          (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)))+
        (1/2:ℝ)*(delta/2)^(-(1:ℝ)/3)*
          ((4/delta)*Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      gcongr
      · exact cubicBesselIntegral_norm_bound x
      · exact cubicBesselIntegralDeriv_norm_bound delta x hdelta hx
    _ = _ := by unfold cubicBesselDerivativeUpper;ring

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicGauss_add_three (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis):primeCubicGauss p hp hprimary (e+3) h=primeCubicGauss p hp hprimary e h:=by
  unfold primeCubicGauss
  rw [pow_add,primeCubicMulChar_cube,mul_one]

lemma cubicUnitGaussSum_prime_cube_shift_pos (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum (h*p^3) (p^(n+4))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*cubicUnitGaussSum h (p^(n+1)):=by
  by_cases hd:p^n∣h
  · obtain ⟨r,rfl⟩:=hd
    have harg:p^n*r*p^3=p^(n+3)*r:=by rw [pow_add];ring
    rw [harg,show n+4=(n+3)+1 by omega,
      cubicUnitGaussSum_prime_power_lift p hp hprimary (n+3) r,
      cubicUnitGaussSum_prime_power_lift p hp hprimary n r]
    rw [show n+3+1=(n+1)+3 by omega,primeCubicGauss_add_three,pow_add]
    ring
  · have hlow:cubicUnitGaussSum h (p^(n+1))=0:=by
      by_contra hh
      exact hd (cubicUnitGaussSum_prime_power_support p hp hprimary n h hh)
    have hhigh:cubicUnitGaussSum (h*p^3) (p^(n+4))=0:=by
      by_contra hh
      have hh':cubicUnitGaussSum (h*p^3) (p^((n+3)+1))≠0:=by convert hh using 1
      have hd':p^(n+3)∣h*p^3:=cubicUnitGaussSum_prime_power_support p hp hprimary (n+3) (h*p^3) hh'
      have hd'':p^3*p^n∣p^3*h:=by simpa only [pow_add,mul_comm,mul_left_comm,mul_assoc] using hd'
      exact hd ((mul_dvd_mul_iff_left (pow_ne_zero 3 hp.ne_zero)).mp hd'')
    rw [hhigh,hlow,mul_zero]

lemma cubicUnitGaussSum_prime_cube_shift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (k:ℕ) (h:Eis):
    cubicUnitGaussSum (h*p^3) (p^(k+3))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*cubicUnitGaussSum h (p^k)-
        if k=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2 else 0:=by
  cases k with
  | zero=>
    rw [Nat.zero_add,cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      (dvd_mul_left (p^3) h)]
    have he:=cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    norm_num at he ⊢
    rw [he]
    ring
  | succ n=>
    simpa only [show n+1+3=n+4 by omega,Nat.succ_ne_zero,ite_false,sub_zero] using
      cubicUnitGaussSum_prime_cube_shift_pos p hp hprimary n h

private def primeExpansionTerm (p:Eis) (s:ℂ) (h:Eis) (k:ℕ):ℂ:=
  ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^k*cubicUnitGaussSum h (p^k)*
    unramifiedPrimeDeletedSeries p s (h*p^k)

private lemma primeExpansionTerm_cube_shift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (h:Eis) (k:ℕ):
    primeExpansionTerm p s (h*p^3) (k+3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        primeExpansionTerm p s h k-
      if k=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*unramifiedPrimeDeletedSeries p s h else 0:=by
  have hv:unramifiedPrimeDeletedSeries p s (h*p^3*p^(k+3))=
      unramifiedPrimeDeletedSeries p s (h*p^k):=by
    have he:h*p^3*p^(k+3)=(h*p^k*p^3)*p^3:=by rw [pow_add];ring
    rw [he,unramifiedPrimeDeletedSeries_cube_shift p hp,
      unramifiedPrimeDeletedSeries_cube_shift p hp]
  unfold primeExpansionTerm
  rw [cubicUnitGaussSum_prime_cube_shift p hp hprimary k h,hv,pow_add]
  split_ifs with hk
  · subst k
    simp only [pow_zero,mul_one,cubicUnitGaussSum_one]
    ring
  · ring

theorem unramifiedCubicGaussSeries_cube_step (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^(a+3))=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^a)+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph (a+3)
  have hold:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph a
  change unramifiedCubicGaussSeries s (h*p^a)=
    ∑k∈Finset.range (a+2),primeExpansionTerm p s (h*p^a) k at hold
  have harg:h*p^(a+3)=(h*p^a)*p^3:=by rw [pow_add,mul_assoc]
  change unramifiedCubicGaussSeries s (h*p^(a+3))=
    ∑k∈Finset.range (a+3+2),primeExpansionTerm p s (h*p^(a+3)) k at he
  rw [show a+3+2=3+(a+2) by omega,Finset.sum_range_add,harg] at he
  have hsmall:∑k∈Finset.range 3,primeExpansionTerm p s (h*p^a*p^3) k=
      unramifiedPrimeDeletedSeries p s (h*p^a):=by
    have hg1:cubicUnitGaussSum (h*p^a*p^3) p=0:=by
      rw [cubicUnitGaussSum_frequency_dvd _ _ hp.ne_zero
        ((dvd_pow_self p (by decide:3≠0)).trans (dvd_mul_left (p^3) (h*p^a)))]
      simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
    have hg2:cubicUnitGaussSum (h*p^a*p^3) (p^2)=0:=by
      rw [cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
        ((pow_dvd_pow p (by omega:2≤3)).trans (dvd_mul_left (p^3) (h*p^a)))]
      simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,primeExpansionTerm,
      pow_zero,pow_one,cubicUnitGaussSum_one,mul_one,one_mul,zero_add,hg1,hg2,
      mul_zero,zero_mul,add_zero]
    rw [unramifiedPrimeDeletedSeries_cube_shift p hp]
  rw [hsmall] at he
  have htail:∑k∈Finset.range (a+2),primeExpansionTerm p s (h*p^a*p^3) (3+k)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedPrimeDeletedSeries p s (h*p^a):=by
    simp_rw [show ∀k:ℕ,3+k=k+3 by omega,primeExpansionTerm_cube_shift p hp hprimary]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←hold]
    simp
  rw [htail,←harg] at he
  exact he.trans (by ring)

theorem unramifiedCubicGaussSeries_cube_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^(a+6))=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s (h*p^(a+3))-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a):=by
  have hfirst:=unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h hph a
  have hsecond:=unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h hph (a+3)
  have hv:unramifiedPrimeDeletedSeries p s (h*p^(a+3))=
      unramifiedPrimeDeletedSeries p s (h*p^a):=by
    rw [pow_add,←mul_assoc,unramifiedPrimeDeletedSeries_cube_shift p hp]
  rw [hv,show a+3+3=a+6 by omega] at hsecond
  linear_combination hsecond-hfirst

end

section

open scoped BigOperators Classical Topology
open Filter Set
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem unramifiedGaussResidue_of_initial_relation (h0 h1 h2:Eis) (A B:ℂ→ℂ)
    (hA:AnalyticOnNhd ℂ A {s:ℂ|1<s.re ∧ 0<s.im})
    (hB:AnalyticOnNhd ℂ B {s:ℂ|1<s.re ∧ 0<s.im})
    (hAc:ContinuousAt A (4/3:ℂ)) (hBc:ContinuousAt B (4/3:ℂ))
    (hrel:∀s:ℂ,4<s.re→0<s.im→unramifiedCubicGaussSeries s h0=
      A s*unramifiedCubicGaussSeries s h1+B s*unramifiedCubicGaussSeries s h2):
    unramifiedGaussResidue h0=A (4/3)*unramifiedGaussResidue h1+
      B (4/3)*unramifiedGaussResidue h2:=by
  let T (h:Eis):ℂ→ℂ:=translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num)
  let H (h:Eis):ℂ→ℂ:=fun s=>cuspWhittakerHeightFactor s (3*h)
  let D:Set ℂ:={s|1<s.re ∧ 0<s.im}
  let f:ℂ→ℂ:=fun s=>T h0 s*H h1 s*H h2 s
  let g:ℂ→ℂ:=fun s=>A s*T h1 s*H h0 s*H h2 s+B s*T h2 s*H h0 s*H h1 s
  have hT (h:Eis):AnalyticOnNhd ℂ (T h) D:=fun s hs=>
    translatedCuspFamily_analyticAt_nonreal (3*h) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hH (h:Eis):AnalyticOnNhd ℂ (H h) D:=fun s hs=>
    cuspWhittakerHeightFactor_analyticAt (3*h) s hs.1
  have hf:AnalyticOnNhd ℂ f D:=fun s hs=>((hT h0 s hs).mul (hH h1 s hs)).mul (hH h2 s hs)
  have hg:AnalyticOnNhd ℂ g D:=fun s hs=>
    (((hA s hs).mul (hT h1 s hs)).mul (hH h0 s hs)).mul (hH h2 s hs) |>.add
      ((((hB s hs).mul (hT h2 s hs)).mul (hH h0 s hs)).mul (hH h1 s hs))
  have hconvex:Convex ℝ D:=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hstart:(5+Complex.I:ℂ)∈D:=by norm_num [D]
  have hopen:IsOpen {s:ℂ|4<s.re ∧ 0<s.im}:=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev:f=ᶠ[𝓝 (5+Complex.I:ℂ)]g:=by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g,T,H]
    rw [translatedCuspFamily_opposite_initial h0 s hs.1 hs.2,
      translatedCuspFamily_opposite_initial h1 s hs.1 hs.2,
      translatedCuspFamily_opposite_initial h2 s hs.1 hs.2,hrel s hs.1 hs.2]
    ring
  have heq:=hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hlimH (h:Eis):Tendsto (H h) (𝓝[≠] (4/3:ℂ)) (𝓝 (H h (4/3))):=
    (cuspWhittakerHeightFactor_analyticAt (3*h) (4/3) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  let R (h:Eis):ℂ:=translatedCuspFourier (3*h) oppositeSource cubicEisensteinResidue
  have hlimT (h:Eis):Tendsto (fun s:ℂ=>(s-4/3)*T h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (R h)):=
    translatedCuspFamily_residue_limit (3*h) oppositeSource 2 3 (by norm_num) (by norm_num)
  have hl:=(((hlimT h0).mul (hlimH h1)).mul (hlimH h2)).comp upperVertical_tendsto_cubic_punctured
  have hr:=((((hAc.tendsto.mono_left nhdsWithin_le_nhds).mul (hlimT h1)).mul (hlimH h0)).mul
    (hlimH h2) |>.add ((((hBc.tendsto.mono_left nhdsWithin_le_nhds).mul (hlimT h2)).mul
      (hlimH h0)).mul (hlimH h1))).comp upperVertical_tendsto_cubic_punctured
  have hcross:R h0*H h1 (4/3)*H h2 (4/3)=
      A (4/3)*R h1*H h0 (4/3)*H h2 (4/3)+B (4/3)*R h2*H h0 (4/3)*H h1 (4/3):=by
    apply tendsto_nhds_unique_of_eventuallyEq hl hr
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have htD:(4/3:ℂ)+(t:ℂ)*Complex.I∈D:=by
      constructor
      · norm_num
      · simpa using ht
    have hc:=heq htD
    dsimp only [Function.comp_def,f,g] at *
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hc
  change R h0/H h0 (4/3)=A (4/3)*(R h1/H h1 (4/3))+B (4/3)*(R h2/H h2 (4/3))
  have h0ne:H h0 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h0)
  have h1ne:H h1 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h1)
  have h2ne:H h2 (4/3)≠0:=cuspWhittakerHeightFactor_center_ne_zero (3*h2)
  field_simp [h0ne,h1ne,h2ne]
  linear_combination hcross

lemma gaussPrimeWeight_analytic (p:Eis) (hp:Prime p) (s:ℂ):
    AnalyticAt ℂ (fun z:ℂ=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-z)) s:=by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact Eventually.of_forall fun z=>(differentiableAt_id.neg).const_cpow (Or.inl
    (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))))

lemma gaussPrimeWeight_center (p:Eis) (hp:Prime p):
    (Ideal.absNorm (Ideal.span {p}):ℂ)^3*
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ)))^3=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹:=by
  have hQ:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  rw [←Complex.cpow_nat_mul,←Complex.cpow_natCast _ 3,←Complex.cpow_add _ _ hQ]
  convert Complex.cpow_neg_one (Ideal.absNorm (Ideal.span {p}):ℂ) using 1 ;congr 1 ;norm_num

theorem unramifiedGaussResidue_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h):
    unramifiedGaussResidue (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(4/3:ℂ))*primeCubicGauss p hp hprimary 1 h*
        unramifiedGaussResidue (h*p):=by
  let A:ℂ→ℂ:=fun s=>1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  let B:ℂ→ℂ:=fun s=>-((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h)
  have hA (s:ℂ):AnalyticAt ℂ A s:=analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have hB (s:ℂ):AnalyticAt ℂ B s:=((gaussPrimeWeight_analytic p hp s).mul analyticAt_const).neg
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^3) h (h*p) A B
    (fun s _=>hA s) (fun s _=>hB s) (hA _).continuousAt (hB _).continuousAt
    (fun s hs _=>by
      have hh:=unramifiedCubicGaussSeries_prime_recurrence p hp hprimary s (by linarith) h hph
      simpa only [A,B,neg_mul,sub_eq_add_neg] using hh)
  dsimp only [A,B] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [neg_mul,sub_eq_add_neg] using he

end

section

open scoped BigOperators Classical Topology
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem unramifiedGaussResidue_cube_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedGaussResidue (h*p^(a+6))=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue (h*p^(a+3))-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue (h*p^a):=by
  let q:ℂ→ℂ:=fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  have hq (s:ℂ):AnalyticAt ℂ q s:=analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3)
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^(a+6)) (h*p^(a+3)) (h*p^a)
    (fun s=>1+q s) (fun s=>-q s)
    (fun s _=>analyticAt_const.add (hq s)) (fun s _=>(hq s).neg)
    (continuousAt_const.add (hq _).continuousAt) (hq _).continuousAt.neg
    (fun s hs _=>by
      have hh:=unramifiedCubicGaussSeries_cube_recurrence p hp hprimary s (by linarith) h hph a
      simpa only [q,neg_mul,sub_eq_add_neg] using hh)
  dsimp only [q] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [neg_mul,sub_eq_add_neg] using he

private lemma recurrence_roots_closed (r:ℕ→ℂ) (q:ℂ)
    (hr:∀k,r (k+2)=(1+q)*r (k+1)-q*r k) (k:ℕ):
    (1-q)*r k=(r 1-q*r 0)+(r 0-r 1)*q^k:=by
  have hpair:∀k:ℕ,
      ((1-q)*r k=(r 1-q*r 0)+(r 0-r 1)*q^k) ∧
      ((1-q)*r (k+1)=(r 1-q*r 0)+(r 0-r 1)*q^(k+1)):=by
    intro k
    induction k with
    | zero=>constructor <;>norm_num <;>ring
    | succ k ih=>
      refine ⟨ih.2,?_⟩
      have hk:=hr k
      rw [show k+1+1=k+2 by omega]
      simp only [pow_succ] at *
      linear_combination (1-q)*hk+(1+q)*ih.2-q*ih.1
  exact (hpair k).1

theorem unramifiedGaussResidue_cube_closed (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (k:ℕ):
    (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue (h*p^(3*k))=
      (unramifiedGaussResidue (h*p^3)-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue h)+
      (unramifiedGaussResidue h-unramifiedGaussResidue (h*p^3))*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)^k:=by
  let r:ℕ→ℂ:=fun j=>unramifiedGaussResidue (h*p^(3*j))
  have hr:∀j,r (j+2)=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*r (j+1)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*r j:=by
    intro j
    have he:=unramifiedGaussResidue_cube_recurrence p hp hprimary h hph (3*j)
    rw [show 3*j+6=3*(j+2) by omega,show 3*j+3=3*(j+1) by omega] at he
    exact he
  have he:=recurrence_roots_closed r (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ hr k
  simpa only [r,Nat.mul_zero,Nat.mul_one,pow_zero,mul_one] using he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

def inverseCuspPath (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) : ℂ×ℝ :=
  (-d/c-(t:ℂ)*star direction/(c^2*((v^2+t^2*‖direction‖^2:ℝ):ℂ)),
    v/(‖c‖^2*(v^2+t^2*‖direction‖^2)))

lemma inverseCuspPath_zero (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) :
    inverseCuspPath c d v direction 0=(-d/c,1/(‖c‖^2*v)) := by
  unfold inverseCuspPath
  simp only [Complex.ofReal_zero,zero_pow (by decide : 2≠0),zero_mul,add_zero,zero_div,sub_zero]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hc,hv.ne']

theorem inverseCuspPath_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) :
    HasDerivAt (inverseCuspPath c d v direction)
      (-(star direction)/(c^2*(v:ℂ)^2),0) 0 := by
  have hn : ‖c‖≠0 := norm_ne_zero_iff.mpr hc
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hden : HasDerivAt (fun t : ℝ=>v^2+t^2*‖direction‖^2) 0 0 := by
    convert (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (‖direction‖^2)).const_add (v^2) using 1 <;> norm_num
  have hnum : HasDerivAt (fun t : ℝ=>(t:ℂ)*star direction) (star direction) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const (star direction))
  have hdenC := hden.ofReal_comp.const_mul (c^2)
  have hdenR := hden.const_mul (‖c‖^2)
  have hcz : c^2*((v^2+(0:ℝ)^2*‖direction‖^2:ℝ):ℂ)≠0 := by
    simpa using mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 hvc)
  have hrz : ‖c‖^2*(v^2+(0:ℝ)^2*‖direction‖^2)≠0 := by positivity
  have hz : HasDerivAt
      (fun t : ℝ=>-d/c-(t:ℂ)*star direction/(c^2*((v^2+t^2*‖direction‖^2:ℝ):ℂ)))
      (-(star direction)/(c^2*(v:ℂ)^2)) 0 := by
    convert (hnum.div hdenC hcz).const_sub (-d/c) using 1 ;
      simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero,Complex.ofReal_pow,
        Complex.ofReal_zero,mul_zero,sub_zero]
    field_simp

  have hvd : HasDerivAt (fun t : ℝ=>v/(‖c‖^2*(v^2+t^2*‖direction‖^2))) 0 0 := by
    convert (hasDerivAt_const (0:ℝ) v).div hdenR hrz using 1 ; simp
  exact hz.prodMk hvd

theorem inverseCuspPath_comp_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    HasDerivAt (fun t=>F (inverseCuspPath c d v direction t))
      (A (-(star direction)/(c^2*(v:ℂ)^2),0)) 0 := by
  have hf : HasFDerivAt F A (inverseCuspPath c d v direction 0) := by
    rwa [inverseCuspPath_zero c d v direction hc hv]
  exact hf.comp_hasDerivAt 0 (inverseCuspPath_hasDerivAt c d v direction hc hv)

end CubicEisenstein

end

end OAI
