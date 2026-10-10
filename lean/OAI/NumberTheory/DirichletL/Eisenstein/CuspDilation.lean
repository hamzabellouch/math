import OAI.NumberTheory.DirichletL.Eisenstein.ArbitraryCuspPullback

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
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedTraceLambda : Eis := 1+2*omega

lemma ramifiedEmbedding_traceLambda : eisEmbedding ramifiedTraceLambda=eisLam := by
  change eisEmbedding (1+2*omega)=1+2*EisensteinEmbedding.omega3
  rw [map_add,map_one,map_mul,map_ofNat,eisEmbedding_omega_actual]

lemma breveE_embedding_third_eval (A B : ℤ) :
    ShortDraftTrace.breveE (eisEmbedding (ActualEisensteinCoordinates.eval A B)/3)=
      eisEmbedding (cubicExp (2*A-B)) := by
  have htrace : ramifiedTraceLambda=ActualEisensteinCoordinates.eval 1 2 := by
    change 1+2*omega=(1:Eis)+(2:Eis)*omega
    rfl
  have h := breveE_real_trace_of_O (3:ℝ)
    (ActualEisensteinCoordinates.eval A B*ramifiedTraceLambda)
  rw [map_mul,ramifiedEmbedding_traceLambda,mul_div_cancel_right₀ _ eisLam_ne_zero] at h
  rw [htrace,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval] at h
  norm_num only [Complex.ofReal_ofNat] at h
  rw [h,embedding_cubicExp]
  congr 3
  ring_nf

lemma primary_add_three (a r : Eis) (ha : lambda^2∣a-1) :
    lambda^2∣a+3*r-1 := by
  have h3 : (3:Eis)∣a-1 := three_dvd_lambda_sq.trans ha
  exact lambda_sq_dvd_three.trans (by
    convert dvd_add h3 (dvd_mul_right (3:Eis) r) using 1 ;ring)

lemma symbol_omega_pow_primary_shift (j : ℕ) (a r : Eis) (ha : lambda^2∣a-1) :
    eisEmbedding (symbol (omega^j) (a+3*r))=
      eisEmbedding (symbol (omega^j) a)*
        ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3) := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  let C := (ActualEisensteinCoordinates.coords r).1
  let D := (ActualEisensteinCoordinates.coords r).2
  have hr : r=ActualEisensteinCoordinates.eval C D := (ActualEisensteinCoordinates.eval_coords r).symm
  have hsum : primaryCoord A B+3*r=primaryCoord (A+C) (B+D) := by
    rw [hr,primaryCoord_eq,primaryCoord_eq]
    change 1+3*(A:Eis)+3*(B:Eis)*omega+3*((C:Eis)+(D:Eis)*omega)=_
    push_cast
    ring
  rw [hsum,symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    linearRay_primaryCoord,linearRay_primaryCoord,map_pow,map_pow]
  have hp : ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3)=
      (ShortDraftTrace.breveE (eisEmbedding r/3))^j := by
    simpa only [nsmul_eq_mul,mul_div_assoc] using
      AddChar.map_nsmul_eq_pow ShortDraftTrace.breveE j (eisEmbedding r/3)
  rw [hp,hr,breveE_embedding_third_eval]
  rw [show 2*(A+C)+(-1)*(B+D)=(2*A+(-1)*B)+(2*C-D) by ring,
    cubicExp_add,map_mul,mul_pow]

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ninthCuspFrequency (h : Eis) : ℂ := cuspFrequency h/3

def unitLowerGauss (h : Eis) (u : Eisˣ) (a : Eis) : ℂ :=
  ∑'r:CubicUnitResidue a,
    (eisEmbedding (symbol (u:Eis) (a+3*GaussianShiftedPartition.representative a r.val))*
      eisEmbedding (symbol (a+3*GaussianShiftedPartition.representative a r.val) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*
        eisEmbedding (a+3*GaussianShiftedPartition.representative a r.val)/eisEmbedding ((u:Eis)*a))

lemma unitLower_phase_identity (h a r k : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3)*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*residueAdditive (3*k) a r := by
  have ha0 := eisEmbedding_ne_zero ha
  have hu0 := eisEmbedding_ne_zero u.ne_zero
  have hui : eisEmbedding (↑u⁻¹:Eis)=(eisEmbedding (u:Eis))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←map_mul]
    simp
  have hk' : 3*eisEmbedding k=eisEmbedding h/(eisEmbedding (u:Eis))+
      (j:ℂ)*eisEmbedding a*eisLam := by
    have he := congrArg eisEmbedding hk
    simpa only [map_mul,map_add,map_ofNat,map_natCast,hui,ramifiedEmbedding_traceLambda,
      div_eq_mul_inv] using he
  have hkk : eisEmbedding k=(eisEmbedding h/eisEmbedding (u:Eis)+
      (j:ℂ)*eisEmbedding a*eisLam)/3 := by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    linear_combination hk'
  rw [←AddChar.map_add_eq_mul]
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  apply congrArg ShortDraftTrace.breveE
  simp only [ninthCuspFrequency,cuspFrequency,map_add,map_mul,map_ofNat]
  rw [hkk]
  field_simp [ha0,hu0,eisLam_ne_zero]
  ;ring

lemma unitLowerGauss_factor (h a k : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    unitLowerGauss h u a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a))*cubicUnitGaussSum k a := by
  rw [unitLowerGauss,cubicUnitGaussSum,←tsum_mul_left]
  apply tsum_congr
  intro r
  let x := GaussianShiftedPartition.representative a r.val
  have hchar : eisEmbedding (symbol (u:Eis) (a+3*x))=
      eisEmbedding (symbol (u:Eis) a)*ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding x/3) := by
    rw [hu]
    exact symbol_omega_pow_primary_shift j a x hprimary
  have hs : symbol (a+3*x) a=symbol (3*x) a := symbol_congr ⟨1,by ring⟩
  change (eisEmbedding (symbol (u:Eis) (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding ((u:Eis)*a))=_
  rw [hchar,hs,symbol_mul_numerator _ _ _ hprimary,map_mul]
  have hp := unitLower_phase_identity h a x k u j ha hk
  calc
    _ = (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol x a))*
      (ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding x/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding ((u:Eis)*a))) := by ring
    _ = _ := by rw [hp];ring

theorem unitLowerGauss_eq_unramified (h a k : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    unitLowerGauss h u a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        cubicUnitGaussSum (3*h*(u:Eis)) a := by
  rw [unitLowerGauss_factor h a k u j ha hprimary hu hk]
  have hu3 : (u:Eis)^3=1 := by
    rw [hu,←pow_mul,mul_comm j 3,pow_mul,omega_primitive.pow_eq_one,one_pow]
  have hu4 : (u:Eis)^4=(u:Eis) := by
    rw [show (4:ℕ)=3+1 by rfl,pow_add,hu3,pow_one,one_mul]
  have hcop : IsCoprime (3*(u:Eis)^2) a :=
    (isCoprime_mul_unit_right_left (u.isUnit.pow 2) 3 a).mpr
      (primary_coprime_three a hprimary).symm
  have hphase := cubicUnitGaussSum_phase_shift k ((u:Eis)^2) a ha hprimary hcop
  have hchars : eisEmbedding (symbol ((u:Eis)^2) a)*eisEmbedding (symbol (3*(u:Eis)^2) a)=
      eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a) := by
    rw [←map_mul,←symbol_mul_numerator _ _ a hprimary]
    rw [show (u:Eis)^2*(3*(u:Eis)^2)=3*(u:Eis)^4 by ring,hu4,
      symbol_mul_numerator _ _ a hprimary,map_mul]
    ring
  rw [hchars] at hphase
  have hcong : a∣k*(9*(u:Eis)^2)-3*h*(u:Eis) := by
    refine ⟨3*(j:Eis)*ramifiedTraceLambda*(u:Eis)^2,?_⟩
    have hi : (↑u⁻¹:Eis)*(u:Eis)^2=(u:Eis) := by
      rw [pow_two,←mul_assoc]
      simp
    have he := congrArg (fun z:Eis=>3*(u:Eis)^2*z) hk
    have hi' : (u:Eis)^2*(↑u⁻¹:Eis)=(u:Eis) := by simpa only [mul_comm] using hi
    linear_combination he+3*h*hi'
  have hg := cubicUnitGaussSum_frequency_congr (k*(9*(u:Eis)^2)) (3*h*(u:Eis)) a ha hcong
  calc
    _ = ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
      (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)*cubicUnitGaussSum k a) := by ring
    _ = _ := by rw [hphase,hg]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def UnitCuspFrequency (h : Eis) (u : Eisˣ) (j : ℕ) : Prop :=
  (3:Eis)∣h*(↑u⁻¹:Eis)+(j:Eis)*ramifiedTraceLambda

lemma unitCuspFrequency_lift (h a : Eis) (u : Eisˣ) (j : ℕ)
    (ha : lambda^2∣a-1) (hh : UnitCuspFrequency h u j) :
    ∃k:Eis,3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda := by
  obtain ⟨q,hq⟩ := hh
  obtain ⟨r,hr⟩ := three_dvd_lambda_sq.trans ha
  refine ⟨q+(j:Eis)*r*ramifiedTraceLambda,?_⟩
  linear_combination -hq-(j:Eis)*ramifiedTraceLambda*hr

lemma unitLowerGauss_eq_unramified_of_frequency (h : Eis) (a : PrimaryLower)
    (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j) (hh : UnitCuspFrequency h u j) :
    unitLowerGauss h u a.val=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        cubicUnitGaussSum (3*h*(u:Eis)) a.val := by
  obtain ⟨k,hk⟩ := unitCuspFrequency_lift h a.val u j (primaryLower_primary a) hh
  exact unitLowerGauss_eq_unramified h a.val k u j (primaryLower_ne_zero a)
    (primaryLower_primary a) hu hk

def unitCuspArithmeticSeries (s : ℂ) (h : Eis) (u : Eisˣ) : ℂ :=
  ∑'a:PrimaryLower,((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val

theorem unitCuspArithmeticSeries_eq (s : ℂ) (h : Eis) (u : Eisˣ) (j : ℕ)
    (hu : (u:Eis)=omega^j) (hh : UnitCuspFrequency h u j) :
    unitCuspArithmeticSeries s h u=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
        unramifiedCubicGaussSeries s (3*h*(u:Eis)) := by
  rw [unitCuspArithmeticSeries,←primaryLowerIdealEquiv.symm.tsum_eq,
    unramifiedCubicGaussSeries,←tsum_mul_left]
  apply tsum_congr
  intro I
  rw [unitLowerGauss_eq_unramified_of_frequency h _ u j hu hh]
  change ((‖eisEmbedding (primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
      cubicUnitGaussSum (3*h*(u:Eis)) (primaryGenerator I.val))=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]
  ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma cuspTransition_dilate (A : ℝ) (hA : A≠0) :
    cuspTransition A (2*A)=fun v => cuspTransition 1 2 (v/A) := by
  funext v
  unfold cuspTransition
  congr 1
  field_simp

lemma cuspTransition_dilate_deriv (A v : ℝ) (hA : A≠0) :
    deriv (cuspTransition A (2*A)) v=deriv (cuspTransition 1 2) (v/A)/A := by
  rw [cuspTransition_dilate A hA]
  have hd := (((cuspTransition_contDiff 1 2).differentiable (by simp) (v/A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)
  simpa [Function.comp_def,id_eq,div_eq_mul_inv] using hd.deriv

lemma cuspTransition_dilate_second (A v : ℝ) (hA : A≠0) :
    deriv (deriv (cuspTransition A (2*A))) v=
      deriv (deriv (cuspTransition 1 2)) (v/A)/A^2 := by
  have he : deriv (cuspTransition A (2*A))=
      fun x => deriv (cuspTransition 1 2) (x/A)/A := by
    funext x
    exact cuspTransition_dilate_deriv A x hA
  rw [he]
  have hc := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have hd := (((hc.differentiable (by simp) (v/A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)).div_const A
  simp only [Function.comp_def,id_eq] at hd
  convert hd.deriv using 1; field_simp

def cuspBaseDefectFactor (s : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^2*(deriv (deriv (cuspTransition 1 2)) x:ℝ)+
    (2*s-1)*(x:ℂ)*(deriv (cuspTransition 1 2) x:ℝ)

lemma cuspBaseDefectFactor_continuous (s : ℂ) : Continuous (cuspBaseDefectFactor s) := by
  have h1 := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  unfold cuspBaseDefectFactor
  exact ((Complex.continuous_ofReal.pow 2).mul (Complex.continuous_ofReal.comp h2.continuous)).add
    ((continuous_const.mul Complex.continuous_ofReal).mul (Complex.continuous_ofReal.comp h1.continuous))

lemma cuspBaseDefectFactor_compact (s : ℂ) : HasCompactSupport (cuspBaseDefectFactor s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 2))
  intro x hx
  by_contra hn
  have hout : x<1 ∨ 2<x := by simpa only [Set.mem_Icc,not_and_or,not_le] using hn
  obtain ⟨h1,h2⟩ := cuspTransition_derivatives 1 2 x (by norm_num) hout
  exact hx (by simp [cuspBaseDefectFactor,h1,h2])

lemma cuspSeedDefectProfile_dilate (A v : ℝ) (hA : A≠0) (s : ℂ) :
    cuspSeedDefectProfile A (2*A) s v=
      positiveHeightPower s v*cuspBaseDefectFactor s (v/A) := by
  rw [cuspSeedDefectProfile,cuspTransition_dilate_deriv A v hA,cuspTransition_dilate_second A v hA]
  unfold cuspBaseDefectFactor
  push_cast
  field_simp

theorem cuspSeedDefectProfile_dilate_bound :
    ∃C : ℝ,0≤C ∧ ∀A : ℝ,1≤A → ∀v : ℝ,
      ‖cuspSeedDefectProfile A (2*A) (4/3) v‖≤C*A^2 := by
  obtain ⟨B,hB⟩ := (cuspBaseDefectFactor_compact (4/3)).exists_bound_of_continuous
    (cuspBaseDefectFactor_continuous (4/3))
  let C := max B 0
  have hC : 0≤C := le_max_right _ _
  have hbound (x : ℝ) : ‖cuspBaseDefectFactor (4/3) x‖≤C := (hB x).trans (le_max_left _ _)
  refine ⟨4*C,by positivity,fun A hA v => ?_⟩
  have hApos : 0<A := lt_of_lt_of_le zero_lt_one hA
  by_cases hv : v∈Set.Icc A (2*A)
  · have hv1 : 1≤v := hA.trans hv.1
    have hvpos : 0<v := hApos.trans_le hv.1
    have hp : ‖positiveHeightPower (4/3) v‖≤v^2 := by
      rw [positiveHeightPower_eq_cpow _ _ hvpos,Complex.norm_cpow_eq_rpow_re_of_pos hvpos]
      norm_num
      have hh := Real.rpow_le_rpow_of_exponent_le hv1 (show (4/3:ℝ)≤2 by norm_num)
      simpa using hh
    rw [cuspSeedDefectProfile_dilate A v hApos.ne',norm_mul]
    have hm := mul_le_mul hp (hbound (v/A)) (norm_nonneg _) (sq_nonneg v)
    calc
      _ ≤ v^2*C := hm
      _ ≤ (2*A)^2*C := mul_le_mul_of_nonneg_right (sq_le_sq₀ hvpos.le (by positivity) |>.mpr hv.2) hC
      _ = (4*C)*A^2 := by ring
  · have hout : v<A ∨ 2*A<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hv
    rw [cuspSeedDefectProfile_zero A (2*A) (4/3) v (by linarith) hout,norm_zero]
    positivity

theorem smoothCuspSeedDefect_dilate_bound :
    ∃C : ℝ,0≤C ∧ ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2 := by
  obtain ⟨C,hC,hbound⟩ := cuspSeedDefectProfile_dilate_bound
  exact ⟨C,hC,fun A hA w => cuspCutoffCorrection_norm_le _ _ (by positivity) (hbound A hA) w⟩

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

lemma movingDefect_product_bound
    (f : KernelQuotient→ℂ) (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3)
    (hbound : ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2)
    (A : ℝ) (hA : 1<A) (q : KernelQuotient) :
    ‖f q‖*‖kernelQuotientDefect A (2*A) (4/3) q‖≤K*C/A := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change ‖f (integralOrbitProjection globalKubotaKernel w)‖*
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤_
    have hApos : 0<A := zero_lt_one.trans hA
    by_cases hz : smoothCuspSeedDefect A (2*A) (4/3) w=0
    · rw [hz,norm_zero,mul_zero]
      positivity
    obtain ⟨r,hr,hr'⟩ := smoothCuspSeedDefect_support A (2*A) (4/3) (by linarith) w hz
    have hheight : 0<cosetHeight r w := hApos.trans_le hr
    have hf : ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/A^3 := by
      apply (hdec w r (hA.trans_le hr)).trans
      apply div_le_div_of_nonneg_left hK (pow_pos hApos 3)
      exact pow_le_pow_left₀ hApos.le hr 3
    calc
      _ ≤ (K/A^3)*(C*A^2) := mul_le_mul hf (hbound A hA.le w) (norm_nonneg _) (by positivity)
      _ = K*C/A := by field_simp

lemma movingDefect_inner_bound
    (F : KernelQuotientL2) (f : KernelQuotient→ℂ)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3)
    (hbound : ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2)
    (A : ℝ) (hA : 1<A) :
    ‖inner ℂ F (kernelL2Defect A (2*A) (by linarith) (by linarith) (4/3))‖≤
      (K*C/A)*(integralQuotientVolume globalKubotaKernel).real Set.univ := by
  rw [L2.inner_def]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hrep,kernelL2Defect_ae_eq A (2*A) (by linarith) (by linarith) (4/3)] with q hf hd
  rw [hf,hd,RCLike.inner_apply,norm_mul]
  simpa only [starRingEnd_apply,norm_star,mul_comm] using
    movingDefect_product_bound f K C hK hC hdec hbound A hA q

theorem cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K : ℝ) (hK : 0≤K)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3) :
    inner ℂ F cubicEisensteinResidue=0 := by
  obtain ⟨C,hC,hbound⟩ := smoothCuspSeedDefect_dilate_bound
  let B : ℝ := (3/2)*(K*C)*(integralQuotientVolume globalKubotaKernel).real Set.univ
  have hB : 0≤B := by dsimp [B]; positivity
  have hb (A : ℝ) (hA : 1<A) : ‖inner ℂ F cubicEisensteinResidue‖≤B/A := by
    have he : cubicEisensteinResidue=
        kernelEisensteinResidueVector A (2*A) (by linarith) (by linarith) :=
      kernelEisensteinResidueVector_cutoff_independent 2 3 A (2*A)
        (by norm_num) (by norm_num) hA (by linarith)
    rw [he,kernelEisensteinResidueVector_pairing,norm_mul]
    norm_num
    calc
      _ ≤ (3/2)*((K*C/A)*(integralQuotientVolume globalKubotaKernel).real Set.univ) :=
        mul_le_mul_of_nonneg_left (movingDefect_inner_bound F f hrep K C hK hC hdec hbound A hA) (by norm_num)
      _ = B/A := by dsimp [B]; ring
    exact hF
  apply norm_eq_zero.mp
  by_contra hn
  have hnpos : 0<‖inner ℂ F cubicEisensteinResidue‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  let A := B/‖inner ℂ F cubicEisensteinResidue‖+2
  have hA : 1<A := by
    have hh := div_nonneg hB hnpos.le
    dsimp [A]
    linarith
  have hh := (le_div_iff₀ (zero_lt_one.trans hA)).mp (hb A hA)
  have he : ‖inner ℂ F cubicEisensteinResidue‖*A=B+2*‖inner ℂ F cubicEisensteinResidue‖ := by
    dsimp [A]
    field_simp

  rw [he] at hh
  linarith

lemma coset_decay_of_cusp_chart_decay
    (f : KernelQuotient→ℂ) (K : ℝ)
    (hdec : ∀M : CubicKubota.levelThree, ∀z : ℂ, ∀v : ℝ, ∀hv : 0<v,1<v →
      ‖f (integralOrbitProjection globalKubotaKernel
        (complexMatrix M • upperPoint z v hv))‖≤K/v^3) :
    ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3 := by
  intro w r
  induction r using Quotient.inductionOn with
  | _ M =>
    intro hr
    change 1<cosetHeight (cosetOf M) w at hr
    change _≤K/(cosetHeight (cosetOf M) w)^3
    rw [cosetHeight_cosetOf] at hr ⊢
    obtain ⟨z,v,hv,hpt⟩ := upperPoint_surjective (complexMatrix M • w)
    have hh : hyperbolicHeight (complexMatrix M • w)=v := by
      rw [←hpt,hyperbolicHeight_upperPoint]
    rw [hh] at hr ⊢
    have he : complexMatrix M⁻¹ • upperPoint z v hv=w := by
      rw [hpt,map_inv,inv_smul_smul]
    simpa only [he] using hdec M⁻¹ z v hv hr

theorem cubicEisensteinResidue_orthogonal_of_cusp_chart_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K : ℝ) (hK : 0≤K)
    (hdec : ∀M : CubicKubota.levelThree, ∀z : ℂ, ∀v : ℝ, ∀hv : 0<v,1<v →
      ‖f (integralOrbitProjection globalKubotaKernel
        (complexMatrix M • upperPoint z v hv))‖≤K/v^3) :
    inner ℂ F cubicEisensteinResidue=0 :=
  cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay F hF f hrep K hK
    (coset_decay_of_cusp_chart_decay f K hdec)

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota

section
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_congruent_cusp_completion (A : SL(2,Eis)) (x y : Eis)
    (hxy : IsCoprime x y) (hx : (3:Eis)∣x-A 0 0) (hy : (3:Eis)∣y-A 1 0) :
    ∃ N : SL(2,Eis), N 0 0=x ∧ N 1 0=y ∧ N*A⁻¹∈levelThree := by
  obtain ⟨u,v,huv⟩ := hxy
  let t := u*A 0 1+v*A 1 1
  let N : SL(2,Eis) := ⟨!![x,-v+x*t;y,u+y*t],by
    rw [Matrix.det_fin_two_of]
    linear_combination huv⟩
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hr : (3:Eis)∣1+y*A 0 1-x*A 1 1 := by
    convert dvd_sub (dvd_mul_of_dvd_left hy (A 0 1))
      (dvd_mul_of_dvd_left hx (A 1 1)) using 1 ; linear_combination -hd
  have hmod : ∀i j,(3:Eis)∣N i j-A i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hx
    · have hv := dvd_mul_of_dvd_left hr (-v)
      convert hv using 1 ; dsimp [N,t] ; linear_combination (A 0 1)*huv
    · exact hy
    · have hu := dvd_mul_of_dvd_left hr u
      convert hu using 1 ; dsimp [N,t] ; linear_combination (A 1 1)*huv
  have hq : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) N =
      Matrix.SpecialLinearGroup.map (n:=Fin 2)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) A := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (hmod i j))
  refine ⟨N,rfl,rfl,?_⟩
  change Matrix.SpecialLinearGroup.map (n:=Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (N*A⁻¹)=1
  rw [map_mul,map_inv,hq,mul_inv_cancel]

lemma cusp_completion_upper_factor (A N : SL(2,Eis)) (q g x y : Eis)
    (hx : A 0 0+3*q*A 1 0=g*N 0 0) (hy : x*A 1 0=g*N 1 0)
    (hg : g≠0) (hdet : x=g*y) :
    N.val⁻¹ * (!![1,3*q;0,x] * A.val) =
      !![g,(N.val⁻¹ * (!![1,3*q;0,x] * A.val)) 0 1;0,y] := by
  have hNdet : N 0 0*N 1 1-N 0 1*N 1 0=1 := by
    simpa only [Matrix.det_fin_two] using N.property
  have hAdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hinv : N.val⁻¹ = !![N 1 1,-N 0 1;-N 1 0,N 0 0] := by
    rw [Matrix.inv_def,Matrix.SpecialLinearGroup.det_coe,Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hx,hy]
    linear_combination g*hNdet
  · rfl
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hx,hy]
    ring
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    apply mul_left_cancel₀ hg
    linear_combination x*hAdet-x*(A 1 1)*hx+(A 0 1+3*q*A 1 1)*hy+hdet

end

open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

private lemma bounded_power_factor (p a : Eis) (n : ℕ) :
    ∃ j≤n,∃b,a=p^j*b ∧ (j=n ∨ ¬p∣b) := by
  induction n generalizing a with
  | zero => exact ⟨0,le_rfl,a,by simp,Or.inl rfl⟩
  | succ n ih =>
    by_cases h:p∣a
    · obtain ⟨a',rfl⟩:=h
      obtain ⟨j,hj,b,hab,hb⟩:=ih a'
      refine ⟨j+1,Nat.succ_le_succ hj,b,?_,?_⟩
      · rw [hab,pow_succ]
        ring
      · exact hb.elim (fun h=>Or.inl (congrArg (fun k=>k+1) h)) Or.inr
    · exact ⟨0,Nat.zero_le _,a,by simp,Or.inr h⟩

lemma cube_average_cusp_reduction (A : SL(2,Eis)) (p q : Eis)
    (hp : Prime p) (hprimary : lambda^2∣p-1) :
    ∃ j≤3,∃N : SL(2,Eis),
      A 0 0+3*q*A 1 0=p^j*N 0 0 ∧
      p^3*A 1 0=p^j*N 1 0 ∧ N*A⁻¹∈levelThree ∧
      (j=3 ∨ ¬p∣N 0 0) ∧
      N.val⁻¹*(!![1,3*q;0,p^3]*A.val)=
        !![p^j,(N.val⁻¹*(!![1,3*q;0,p^3]*A.val)) 0 1;0,p^(3-j)] := by
  let a:=A 0 0+3*q*A 1 0
  have haC:IsCoprime a (A 1 0) := by
    have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
      simpa only [Matrix.det_fin_two] using A.property
    refine ⟨A 1 1,-(A 0 1+3*q*A 1 1),?_⟩
    dsimp [a]
    linear_combination hd
  obtain ⟨j,hj,b,hab,hb⟩:=bounded_power_factor p a 3
  have hbC:IsCoprime b (A 1 0) := by
    rw [hab] at haC
    exact haC.of_mul_left_right
  have hbY:IsCoprime b (p^(3-j)*A 1 0) := by
    rcases hb with h | h
    · simpa [h] using hbC
    · exact ((hp.coprime_iff_not_dvd.mpr h).symm.pow_right).mul_right hbC
  have hpow (k:ℕ):(3:Eis)∣p^k-1 := by
    have hd:(3:Eis)∣p-1:=CubicJacobiGlobal.three_dvd_primary_sub_one p hprimary
    simpa using hd.trans (sub_dvd_pow_sub_pow p 1 k)
  have hbA:(3:Eis)∣b-A 0 0 := by
    have h1:(3:Eis)∣a-A 0 0:=by
      refine ⟨q*A 1 0,?_⟩
      dsimp [a]
      ring
    have h2:(3:Eis)∣a-b:=by
      rw [hab]
      convert dvd_mul_of_dvd_left (hpow j) b using 1 ; ring
    convert dvd_sub h1 h2 using 1 ; ring
  have hyC:(3:Eis)∣p^(3-j)*A 1 0-A 1 0 := by
    convert dvd_mul_of_dvd_left (hpow (3-j)) (A 1 0) using 1 ; ring
  obtain ⟨N,hN0,hN1,hNA⟩:=exists_congruent_cusp_completion A b (p^(3-j)*A 1 0) hbY hbA hyC
  have hA:a=p^j*N 0 0:=by rw [hN0];exact hab
  have hC:p^3*A 1 0=p^j*N 1 0:=by
    rw [hN1,←mul_assoc,←pow_add,Nat.add_sub_of_le hj]
  refine ⟨j,hj,N,hA,hC,hNA,?_,?_⟩
  · simpa [hN0] using hb
  · exact cusp_completion_upper_factor A N q (p^j) (p^3) (p^(3-j))
      hA hC (pow_ne_zero j hp.ne_zero) (by rw [←pow_add,Nat.add_sub_of_le hj])

end CubicKubota

end

end OAI
