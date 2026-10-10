import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ConformalFlow

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open ExactSLEMain ExactSLEGenerator ExactSLEGreen

abbrev Angle := Ioo (0:ℝ) Real.pi

def angleArea : Measure Angle := volume.comap (Subtype.val : Angle→ℝ)

def angleWeight (a : ℝ) (θ : Angle) : ℝ≥0∞ := ENNReal.ofReal ((Real.sin θ)^(4*a))

def angleNormalization (a : ℝ) : ℝ≥0∞ := ∫⁻θ,angleWeight a θ∂angleArea

 

def angleLaw (a : ℝ) : Measure Angle :=
  (angleNormalization a)⁻¹ • angleArea.withDensity (angleWeight a)

lemma angleArea_univ : angleArea univ=ENNReal.ofReal Real.pi := by
  rw [angleArea,MeasurableEmbedding.comap_apply
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo) _ univ]
  rw [show (Subtype.val : Angle→ℝ) '' univ=Ioo (0:ℝ) Real.pi by ext x; simp,
    Real.volume_Ioo,sub_zero]

instance : IsFiniteMeasure angleArea := ⟨by rw [angleArea_univ]; exact ENNReal.ofReal_lt_top⟩

lemma angleArea_ne_zero : angleArea univ≠0 := by
  rw [angleArea_univ]
  exact (ENNReal.ofReal_pos.mpr Real.pi_pos).ne'

lemma angleWeight_measurable (a : ℝ) : Measurable (angleWeight a) := by
  unfold angleWeight
  fun_prop

lemma angleWeight_pos (a : ℝ) (θ : Angle) : 0<angleWeight a θ :=
  ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2) _)

lemma angleWeight_le_one (a : ℝ) (ha : 0≤a) (θ : Angle) : angleWeight a θ≤1 := by
  rw [←ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one
    (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2).le (Real.sin_le_one θ) (by positivity))

lemma angleNormalization_pos (a : ℝ) : 0<angleNormalization a := by
  rw [angleNormalization,lintegral_pos_iff_support (angleWeight_measurable a)]
  have hs : Function.support (angleWeight a)=univ := by
    ext θ
    simp [Function.mem_support,(angleWeight_pos a θ).ne']
  rw [hs]
  exact bot_lt_iff_ne_bot.mpr angleArea_ne_zero

lemma angleNormalization_lt_top (a : ℝ) (ha : 0≤a) : angleNormalization a<∞ := by
  calc
    _ ≤ ∫⁻_ : Angle,(1:ℝ≥0∞)∂angleArea := lintegral_mono (angleWeight_le_one a ha)
    _ < ∞ := by simp [angleArea_univ]

lemma angleLaw_probability (a : ℝ) (ha : 0≤a) : IsProbabilityMeasure (angleLaw a) := by
  rw [isProbabilityMeasure_iff]
  rw [angleLaw,Measure.smul_apply,smul_eq_mul,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel (angleNormalization_pos a).ne' (angleNormalization_lt_top a ha).ne

lemma angleLaw_integral (a : ℝ) (f : Angle→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻θ,f θ∂angleLaw a)=(angleNormalization a)⁻¹*
      ∫⁻θ,angleWeight a θ*f θ∂angleArea := by
  rw [angleLaw,lintegral_smul_measure,smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _ (angleWeight_measurable a) hf]
  rfl

lemma angleWeight_cancel (a : ℝ) (θ : Angle) :
    angleWeight a θ*ENNReal.ofReal ((Real.sin θ)^(-p a))=
      ENNReal.ofReal (Real.sin θ) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2
  rw [angleWeight,←ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),←Real.rpow_add hs]
  simp [p]

 
lemma angle_inverse_power_finite (a : ℝ) :
    (∫⁻θ : Angle,ENNReal.ofReal ((Real.sin θ)^(-p a))∂angleLaw a)<∞ := by
  rw [angleLaw_integral a _ (by fun_prop)]
  simp_rw [angleWeight_cancel]
  apply ENNReal.mul_lt_top
  · exact ENNReal.inv_lt_top.mpr (angleNormalization_pos a)
  · calc
      _ ≤ ∫⁻_ : Angle,(1:ℝ≥0∞)∂angleArea := by
        apply lintegral_mono
        intro θ
        rw [←ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.sin_le_one θ)
      _ < ∞ := by simp [angleArea_univ]

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open Polynomial

namespace SLEExactGauge.Jacobi

 
def operator (nu : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (1-X^2)*p.derivative.derivative - C (1+nu)*X*p.derivative

 
def raise (nu n : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C (1/(2*n+nu)) * (C (n+nu)*X*p - (1-X^2)*p.derivative)

lemma raise_derivative (nu n : ℝ) (p : ℝ[X])
    (hp : operator nu p = -C (n*(n+nu))*p) :
    (raise nu n p).derivative =
      C (1/(2*n+nu))*C (n+1)*(C (n+nu)*p+X*p.derivative) := by
  dsimp only [raise,operator] at *
  simp only [derivative_mul,derivative_sub,derivative_C,derivative_X,derivative_one,
    derivative_pow,zero_mul,zero_sub,zero_add]
  simp only [map_mul,map_add,map_one,Nat.cast_ofNat,map_ofNat] at hp ⊢
  linear_combination -C (1/(2*n+nu)) * hp

lemma raise_eigen (nu n : ℝ) (p : ℝ[X])
    (hp : operator nu p = -C (n*(n+nu))*p) :
    operator nu (raise nu n p) = -C ((n+1)*(n+1+nu)) * raise nu n p := by
  have hd := raise_derivative nu n p hp
  have hd2 := congrArg Polynomial.derivative hd
  simp only [derivative_mul,derivative_add,derivative_C,derivative_X,
    zero_mul,mul_zero,zero_add,one_mul,add_zero] at hd2
  rw [operator,hd2,hd]
  dsimp only [raise,operator] at *
  simp only [map_mul,map_add,map_one] at hp ⊢
  linear_combination C (1/(2*n+nu))*(C n+1)*X * hp

lemma raise_lowering (nu n : ℝ) (p : ℝ[X])
    (hp : operator nu p = -C (n*(n+nu))*p) :
    (1-X^2)*(raise nu n p).derivative + C (n+1)*X*raise nu n p =
      C ((n+1)*(n+nu)/(2*n+nu))*p := by
  rw [raise_derivative nu n p hp]
  simp only [raise,map_mul,map_add,map_one,div_eq_mul_inv]
  ring

 
def poly (nu : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n+1 => raise nu n (poly nu n)

@[simp] lemma poly_zero (nu : ℝ) : poly nu 0=1 := rfl
@[simp] lemma poly_succ (nu : ℝ) (n : ℕ) :
    poly nu (n+1)=raise nu n (poly nu n) := rfl

lemma poly_eigen (nu : ℝ) (n : ℕ) :
    operator nu (poly nu n) = -C ((n:ℝ)*(n+nu))*poly nu n := by
  induction n with
  | zero => simp [operator]
  | succ n ih => simpa only [poly_succ,Nat.cast_add,Nat.cast_one] using
      raise_eigen nu n (poly nu n) ih

lemma poly_lowering (nu : ℝ) (n : ℕ) :
    (1-X^2)*(poly nu (n+1)).derivative + C ((n:ℝ)+1)*X*poly nu (n+1) =
      C (((n:ℝ)+1)*(n+nu)/(2*n+nu))*poly nu n :=
  raise_lowering nu n (poly nu n) (poly_eigen nu n)

lemma raise_eq_X_sub (nu n : ℝ) (p : ℝ[X]) (h : 2*n+nu≠0) :
    raise nu n p = X*p - C (1/(2*n+nu))*((1-X^2)*p.derivative+C n*X*p) := by
  have hc : C (1/(2*n+nu))*(2*C n+C nu)=(1:ℝ[X]) := by
    have he : (2*C n+C nu : ℝ[X])=C (2*n+nu) := by simp only [map_add,map_mul,map_ofNat]
    rw [he,←map_mul,one_div_mul_cancel h,map_one]
  simp only [raise,map_add]
  linear_combination X*p*hc

lemma poly_one (nu : ℝ) (hnu : nu≠0) : poly nu 1=X := by
  rw [show 1=0+1 from rfl,poly_succ,poly_zero,Nat.cast_zero,raise_eq_X_sub nu 0 1 (by simpa using hnu)]
  simp

 
def beta (nu : ℝ) (n : ℕ) : ℝ :=
  ((n:ℝ)+1)*(n+nu)/((2*n+nu+2)*(2*n+nu))

lemma poly_recurrence (nu : ℝ) (hnu : 0<nu) (n : ℕ) :
    poly nu (n+2)=X*poly nu (n+1)-C (beta nu n)*poly nu n := by
  have hd : 2*((n:ℝ)+1)+nu≠0 := ne_of_gt (by positivity)
  change raise nu ((n+1:ℕ):ℝ) (poly nu (n+1))=_
  rw [Nat.cast_add,Nat.cast_one,raise_eq_X_sub nu ((n:ℝ)+1) _ hd,poly_lowering]
  congr 1
  rw [←mul_assoc,←map_mul]
  congr 2
  unfold beta
  field_simp
  ring

lemma beta_pos (nu : ℝ) (hnu : 0<nu) (n : ℕ) : 0<beta nu n := by
  unfold beta
  positivity

lemma beta_le_one (nu : ℝ) (hnu : 0<nu) (n : ℕ) : beta nu n≤1 := by
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  unfold beta
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg ((n:ℝ)),sq_nonneg nu,mul_nonneg hn hnu.le]

lemma beta_lower (nu : ℝ) (hnu : 1≤nu) (n : ℕ) :
    1/(nu+2)^2≤beta nu n := by
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hnu0 : 0<nu := lt_of_lt_of_le zero_lt_one hnu
  have h1 : 0<(nu+2)^2 := by positivity
  have h2 : 0<(2*(n:ℝ)+nu+2)*(2*n+nu) := by positivity
  have hden : (2*(n:ℝ)+nu+2)*(2*n+nu)≤(nu+2)^2*((n:ℝ)+1)^2 := by
    have hb1 : 2*(n:ℝ)+nu+2≤(nu+2)*((n:ℝ)+1) := by
      nlinarith [mul_nonneg hnu0.le hn]
    have hb2 : 2*(n:ℝ)+nu≤(nu+2)*((n:ℝ)+1) := by linarith
    have hh := mul_le_mul hb1 hb2 (by positivity : 0≤2*(n:ℝ)+nu)
      (by positivity : 0≤(nu+2)*((n:ℝ)+1))
    nlinarith only [hh]
  have hnum : ((n:ℝ)+1)^2≤((n:ℝ)+1)*(n+nu) := by nlinarith
  rw [beta,div_le_div_iff₀ h1 h2]
  have hm := mul_le_mul_of_nonneg_left hnum h1.le
  nlinarith only [hden,hm]

lemma poly_eval_bound (nu : ℝ) (hnu : 0<nu) (n : ℕ) (x : ℝ) (hx : |x|≤1) :
    |(poly nu n).eval x|≤2^n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [poly_one nu hnu.ne',eval_X,pow_one]
    exact hx.trans (by norm_num)
  | more n hn hn1 =>
    rw [poly_recurrence nu hnu n,eval_sub,eval_mul,eval_X,eval_mul,eval_C]
    calc
      _ ≤ |x*(poly nu (n+1)).eval x|+|beta nu n*(poly nu n).eval x| := abs_sub _ _
      _ = |x| * |(poly nu (n+1)).eval x|+beta nu n * |(poly nu n).eval x| := by
        rw [abs_mul,abs_mul,abs_of_pos (beta_pos nu hnu n)]
      _ ≤ 2^(n+1)+2^n := add_le_add
        ((mul_le_mul hx hn1 (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
        ((mul_le_mul (beta_le_one nu hnu n) hn (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
      _ ≤ 2^(n+2) := by
        simp only [pow_add,pow_one]
        norm_num
        nlinarith [show (0:ℝ)≤2^n by positivity]

end SLEExactGauge.Jacobi
end
end
 

 
section
 
noncomputable section
open Polynomial MeasureTheory Set
open scoped Interval

namespace SLEExactGauge.Jacobi

def weight (nu x : ℝ) : ℝ := (1-x^2)^((nu-1)/2)
def flux (nu x : ℝ) : ℝ := (1-x^2)^((nu+1)/2)

def inner (nu : ℝ) (p q : ℝ[X]) : ℝ :=
  ∫ x in (-1:ℝ)..1, weight nu x * p.eval x * q.eval x

lemma continuous_weight (nu : ℝ) (hnu : 1≤nu) : Continuous (weight nu) :=
  (continuous_const.sub (continuous_id.pow 2)).rpow_const (fun _ => Or.inr (by linarith))

lemma continuous_flux (nu : ℝ) (hnu : 1≤nu) : Continuous (flux nu) :=
  (continuous_const.sub (continuous_id.pow 2)).rpow_const (fun _ => Or.inr (by linarith))

lemma flux_eq (nu : ℝ) (hnu : 1<nu) (x : ℝ) (hx : x∈Icc (-1:ℝ) 1) :
    flux nu x = (1-x^2)*weight nu x := by
  have hx0 : 0≤1-x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0≤1+x by linarith [hx.1])]
  have he : (nu+1)/2=(nu-1)/2+1 := by ring
  rw [flux,he,Real.rpow_add' hx0 (by linarith : (nu-1)/2+1≠0),Real.rpow_one,weight]
  ring

lemma hasDerivAt_flux (nu : ℝ) (hnu : 1≤nu) (x : ℝ) :
    HasDerivAt (flux nu) (-(nu+1)*x*weight nu x) x := by
  have hd := ((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).pow 2)).rpow_const
    (Or.inr (by linarith : 1≤(nu+1)/2))
  convert hd using 1
  · rfl
  · dsimp [weight]
    rw [show (nu+1)/2-1=(nu-1)/2 by ring]
    ring

lemma inner_comm (nu : ℝ) (p q : ℝ[X]) : inner nu p q=inner nu q p := by
  apply intervalIntegral.integral_congr
  intro x hx
  ring

lemma inner_integrable (nu : ℝ) (hnu : 1≤nu) (p q : ℝ[X]) :
    IntervalIntegrable (fun x => weight nu x*p.eval x*q.eval x) volume (-1) 1 :=
  (((continuous_weight nu hnu).mul p.continuous).mul q.continuous).intervalIntegrable _ _

lemma inner_add_left (nu : ℝ) (hnu : 1≤nu) (p q r : ℝ[X]) :
    inner nu (p+q) r=inner nu p r+inner nu q r := by
  simp only [inner,eval_add,mul_add,add_mul]
  exact intervalIntegral.integral_add (inner_integrable nu hnu p r) (inner_integrable nu hnu q r)

lemma inner_sub_left (nu : ℝ) (hnu : 1≤nu) (p q r : ℝ[X]) :
    inner nu (p-q) r=inner nu p r-inner nu q r := by
  simp only [inner,eval_sub,mul_sub,sub_mul]
  exact intervalIntegral.integral_sub (inner_integrable nu hnu p r) (inner_integrable nu hnu q r)

lemma inner_C_mul_left (nu c : ℝ) (p q : ℝ[X]) :
    inner nu (C c*p) q=c*inner nu p q := by
  simp only [inner,eval_mul,eval_C]
  simp_rw [show ∀ x, weight nu x*(c*p.eval x)*q.eval x=c*(weight nu x*p.eval x*q.eval x) by intro x; ring]
  exact intervalIntegral.integral_const_mul _ _

lemma inner_neg_left (nu : ℝ) (p q : ℝ[X]) :
    inner nu (-p) q= -inner nu p q := by
  simp [inner]

lemma inner_X (nu : ℝ) (p q : ℝ[X]) : inner nu (X*p) q=inner nu p (X*q) := by
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [eval_mul,eval_X]
  ring

 
lemma operator_symmetric (nu : ℝ) (hnu : 1<nu) (p q : ℝ[X]) :
    inner nu p (operator nu q)=inner nu (operator nu p) q := by
  let f (x : ℝ) := flux nu x * (p.eval x*q.derivative.eval x-p.derivative.eval x*q.eval x)
  let g (x : ℝ) := weight nu x*p.eval x*(operator nu q).eval x-
    weight nu x*(operator nu p).eval x*q.eval x
  have hd (x : ℝ) (hx : x∈uIcc (-1:ℝ) 1) : HasDerivAt f (g x) x := by
    have hxx : x∈Icc (-1:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (-1:ℝ)≤1)] using hx
    have hh := (hasDerivAt_flux nu hnu.le x).mul
      (((p.hasDerivAt x).mul (q.derivative.hasDerivAt x)).sub
        ((p.derivative.hasDerivAt x).mul (q.hasDerivAt x)))
    convert hh using 1
    try rfl
    all_goals simp only [g,operator,Pi.mul_apply,Pi.sub_apply,eval_sub,eval_mul,eval_pow,eval_X,eval_one,eval_C,flux_eq nu hnu x hxx]
    all_goals ring
  have hi : IntervalIntegrable g volume (-1) 1 :=
    (inner_integrable nu hnu.le p (operator nu q)).sub
      (inner_integrable nu hnu.le (operator nu p) q)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hz : flux nu 1=0 ∧ flux nu (-1)=0 := by
    simp [flux,Real.zero_rpow (by linarith : (nu+1)/2≠0)]
  have hg : (∫ x in (-1:ℝ)..1, g x) = inner nu p (operator nu q)-inner nu (operator nu p) q :=
    intervalIntegral.integral_sub (inner_integrable nu hnu.le p (operator nu q))
      (inner_integrable nu hnu.le (operator nu p) q)
  rw [hg] at hh
  simpa [f,hz.1,hz.2,sub_eq_zero] using hh

lemma eigenvalue_strictMono (nu : ℝ) (hnu : 0<nu) :
    StrictMono (fun n : ℕ => (n:ℝ)*(n+nu)) := by
  intro n m hnm
  have hnm' : (n:ℝ) < m := Nat.cast_lt.mpr hnm
  nlinarith [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) m]

 
lemma poly_orthogonal (nu : ℝ) (hnu : 1<nu) (n m : ℕ) (hnm : n≠m) :
    inner nu (poly nu n) (poly nu m)=0 := by
  have hs := operator_symmetric nu hnu (poly nu n) (poly nu m)
  simp only [poly_eigen,neg_mul] at hs
  rw [inner_comm nu (poly nu n),inner_neg_left,inner_C_mul_left,
    inner_neg_left,inner_C_mul_left,inner_comm nu (poly nu m)] at hs
  have he := (eigenvalue_strictMono nu (by linarith)).injective.ne hnm
  have hp : ((n:ℝ)*(n+nu)-(m:ℝ)*(m+nu))*inner nu (poly nu n) (poly nu m)=0 := by linarith
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr he)

end SLEExactGauge.Jacobi
end
end
 

 
section
 
noncomputable section
open Polynomial MeasureTheory Set
open scoped Interval

namespace SLEExactGauge.Jacobi

lemma poly_monic_degree (nu : ℝ) (hnu : 0<nu) (n : ℕ) :
    (poly nu n).Monic ∧ (poly nu n).degree=n := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [poly_zero,Nat.cast_zero,monic_one,degree_one,and_self]
  | one => rw [poly_one nu hnu.ne']; exact ⟨monic_X,degree_X⟩
  | more n hn hn1 =>
    have hd : (C (beta nu n)*poly nu n).degree < (X*poly nu (n+1)).degree := by
      rw [degree_C_mul (beta_pos nu hnu n).ne',degree_mul,degree_X,hn.2,hn1.2]
      norm_cast
      omega
    rw [poly_recurrence nu hnu n]
    refine ⟨(monic_X.mul hn1.1).sub_of_left hd, ?_⟩
    rw [degree_sub_eq_left_of_degree_lt hd,degree_mul,degree_X,hn1.2]
    norm_cast
    omega

 
def basis (nu : ℝ) (hnu : 0<nu) : Module.Basis ℕ ℝ ℝ[X] :=
  let seq : Polynomial.Sequence ℝ := ⟨poly nu, fun n => (poly_monic_degree nu hnu n).2⟩
  seq.basis (fun n => by
    change IsUnit (poly nu n).leadingCoeff
    rw [(poly_monic_degree nu hnu n).1.leadingCoeff]
    exact isUnit_one)

@[simp] lemma basis_apply (nu : ℝ) (hnu : 0<nu) (n : ℕ) : basis nu hnu n=poly nu n := by
  simp only [basis,Polynomial.Sequence.basis_eq_self]

def normSq (nu : ℝ) (n : ℕ) : ℝ := inner nu (poly nu n) (poly nu n)

lemma normSq_zero_pos (nu : ℝ) (hnu : 1≤nu) : 0<normSq nu 0 := by
  change 0<∫ x in (-1:ℝ)..1, weight nu x*(poly nu 0).eval x*(poly nu 0).eval x
  simp only [poly_zero,eval_one,mul_one]
  apply intervalIntegral.integral_pos (by norm_num) (continuous_weight nu hnu).continuousOn
  · intro x hx
    apply Real.rpow_nonneg
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0≤1+x by linarith [hx.1])]
  · refine ⟨0,by norm_num, ?_⟩
    simp [weight]

lemma normSq_succ (nu : ℝ) (hnu : 1<nu) (n : ℕ) :
    normSq nu (n+1)=beta nu n*normSq nu n := by
  have hnu0 : 0<nu := by linarith
  have hr (j : ℕ) : X*poly nu (j+1)=poly nu (j+2)+C (beta nu j)*poly nu j := by
    rw [poly_recurrence nu hnu0 j]
    ring
  have hl : inner nu (X*poly nu (n+1)) (poly nu n)=beta nu n*normSq nu n := by
    rw [hr,inner_add_left nu hnu.le,inner_C_mul_left,
      poly_orthogonal nu hnu (n+2) n (by omega),zero_add]
    rfl
  rw [inner_X,inner_comm] at hl
  rw [←hl]
  cases n with
  | zero =>
    change inner nu (poly nu 1) (poly nu 1)=_
    rw [poly_zero,mul_one,poly_one nu hnu0.ne']
  | succ n =>
    rw [hr n,inner_add_left nu hnu.le,inner_C_mul_left,
      poly_orthogonal nu hnu n (n+1+1) (by omega),mul_zero,add_zero]
    rfl

lemma normSq_pos (nu : ℝ) (hnu : 1<nu) (n : ℕ) : 0<normSq nu n := by
  induction n with
  | zero => exact normSq_zero_pos nu hnu.le
  | succ n hn =>
    rw [normSq_succ nu hnu n]
    exact mul_pos (beta_pos nu (by linarith) n) hn

lemma normSq_lower (nu : ℝ) (hnu : 1<nu) (n : ℕ) :
    normSq nu 0 / ((nu+2)^2)^n ≤ normSq nu n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [normSq_succ nu hnu,pow_succ]
    have hb := beta_lower nu hnu.le n
    have hz := normSq_zero_pos nu hnu.le
    have hh := mul_le_mul hb hn (by positivity : 0≤normSq nu 0/((nu+2)^2)^n)
      (beta_pos nu (by linarith) n).le
    calc
      _ = (1/(nu+2)^2)*(normSq nu 0/((nu+2)^2)^n) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ ≤ _ := hh

end SLEExactGauge.Jacobi
end
end
 

 
section
 
noncomputable section
open Polynomial MeasureTheory Set
open scoped ENNReal Interval Topology
namespace SLEExactGauge.Jacobi

abbrev Interval := Icc (-1:ℝ) 1

def baseMeasure : Measure Interval := volume.comap Subtype.val

instance base_finite : IsFiniteMeasure baseMeasure := by
  constructor
  rw [baseMeasure,(MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_apply]
  simp only [image_univ,Subtype.range_coe_subtype,ofPred_mem_eq]
  exact isCompact_Icc.measure_lt_top

lemma weight_nonneg (nu : ℝ) (x : Interval) : 0≤weight nu x := by
  apply Real.rpow_nonneg
  have hx := x.2
  nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show (0:ℝ)≤1+x.1 by linarith [hx.1])]

lemma continuous_weight_interval (nu : ℝ) (hnu : 1≤nu) :
    Continuous (fun x : Interval => weight nu x) := (continuous_weight nu hnu).comp continuous_subtype_val

lemma integrable_weight_interval (nu : ℝ) (hnu : 1≤nu) :
    Integrable (fun x : Interval => weight nu x) baseMeasure := by
  exact (continuous_weight_interval nu hnu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integral_base (f : ℝ → ℝ) :
    (∫ x : Interval, f x ∂baseMeasure)=∫ x in (-1:ℝ)..1, f x := by
  rw [baseMeasure,integral_subtype_comap measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1)]

lemma integral_weight_base (nu : ℝ) :
    (∫ x : Interval, weight nu x ∂baseMeasure)=normSq nu 0 := by
  rw [integral_base]
  simp only [normSq,inner,poly_zero,eval_one,mul_one]

def rawMeasure (nu : ℝ) : Measure Interval :=
  baseMeasure.withDensity (fun x => ENNReal.ofReal (weight nu x))

def pi (nu : ℝ) : Measure Interval := (ENNReal.ofReal (normSq nu 0))⁻¹ • rawMeasure nu

lemma rawMeasure_univ (nu : ℝ) (hnu : 1≤nu) :
    rawMeasure nu univ=ENNReal.ofReal (normSq nu 0) := by
  rw [rawMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_weight_interval nu hnu)
    (Filter.Eventually.of_forall (weight_nonneg nu)),integral_weight_base]

lemma pi_probability (nu : ℝ) (hnu : 1≤nu) : IsProbabilityMeasure (pi nu) := by
  constructor
  rw [pi,Measure.smul_apply,rawMeasure_univ nu hnu,smul_eq_mul]
  exact ENNReal.inv_mul_cancel ((ENNReal.ofReal_pos.mpr (normSq_zero_pos nu hnu)).ne') ENNReal.ofReal_ne_top

lemma integral_pi_mul (nu : ℝ) (hnu : 1≤nu) (p q : ℝ[X]) :
    (∫ x : Interval, p.eval (x:ℝ)*q.eval (x:ℝ) ∂pi nu)=inner nu p q/normSq nu 0 := by
  rw [pi,integral_smul_measure,rawMeasure,integral_withDensity_eq_integral_toReal_smul
    ((continuous_weight_interval nu hnu).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (weight_nonneg nu _),smul_eq_mul]
  rw [ENNReal.toReal_inv,ENNReal.toReal_ofReal (normSq_zero_pos nu hnu).le]
  have hi : (∫ x : Interval, weight nu x*(p.eval (x:ℝ)*q.eval (x:ℝ)) ∂baseMeasure)=inner nu p q := by
    simp_rw [←mul_assoc]
    exact integral_base (fun x : ℝ => weight nu x*p.eval x*q.eval x)
  rw [hi]
  ring

lemma integral_pi_poly (nu : ℝ) (hnu : 1<nu) (n m : ℕ) :
    (∫ x : Interval, (poly nu n).eval (x:ℝ) * (poly nu m).eval (x:ℝ) ∂pi nu)=
      if n=m then normSq nu n/normSq nu 0 else 0 := by
  rw [integral_pi_mul nu hnu.le]
  split_ifs with hnm
  · subst m; rfl
  · rw [poly_orthogonal nu hnu n m hnm,zero_div]

lemma poly_interval_integrable (nu : ℝ) (hnu : 1<nu) (p : ℝ[X]) :
    Integrable (fun x : Interval => p.eval (x:ℝ)) (pi nu) := by
  let := pi_probability nu hnu.le
  exact (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integral_pi_poly_single (nu : ℝ) (hnu : 1<nu) (n : ℕ) :
    (∫ x : Interval, (poly nu n).eval (x:ℝ) ∂pi nu)=if n=0 then 1 else 0 := by
  have hh := integral_pi_poly nu hnu n 0
  simp only [poly_zero,eval_one,mul_one] at hh
  rw [hh]
  split_ifs with hn
  · subst n; exact div_self (normSq_zero_pos nu hnu.le).ne'
  · rfl

end SLEExactGauge.Jacobi
end
end

end OAI
