import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.AngleGenerators
import OAI.Probability.SLEGauge.AngleMeasure

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open Polynomial MeasureTheory Filter Set
open scoped ENNReal Topology
namespace SLEExactGauge.Jacobi

def eigenvalue (nu : ℝ) (n : ℕ) : ℝ := (n:ℝ)*(n+nu)/2
def majorantBase (nu : ℝ) : ℝ := 4*(nu+2)^2
def mixingTime (nu : ℝ) : ℝ := 4*majorantBase nu

def mode (nu s : ℝ) (n : ℕ) (v w : Interval) : ℝ :=
  Real.exp (-s*eigenvalue nu n) * (normSq nu 0/normSq nu n) *
    (poly nu n).eval (v:ℝ) * (poly nu n).eval (w:ℝ)

def kernel (nu s : ℝ) (v w : Interval) : ℝ := ∑' n, mode nu s n v w

lemma eigenvalue_nonneg (nu : ℝ) (hnu : 0≤nu) (n : ℕ) : 0≤eigenvalue nu n := by
  unfold eigenvalue
  positivity

lemma eigenvalue_ge (nu : ℝ) (hnu : 1≤nu) (n : ℕ) : (n:ℝ)≤eigenvalue nu n := by
  cases n with
  | zero => simp [eigenvalue]
  | succ n =>
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    dsimp [eigenvalue]
    push_cast
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hnu),sq_nonneg (n:ℝ)]

lemma norm_ratio_le (nu : ℝ) (hnu : 1<nu) (n : ℕ) :
    normSq nu 0/normSq nu n ≤ ((nu+2)^2)^n := by
  have hd : 0<((nu+2)^2)^n := by positivity
  rw [div_le_iff₀ (normSq_pos nu hnu n)]
  have hn := (div_le_iff₀ hd).mp (normSq_lower nu hnu n)
  simpa only [mul_comm] using hn

lemma mode_bound (nu : ℝ) (hnu : 1<nu) (s : ℝ) (n : ℕ) (v w : Interval) :
    ‖mode nu s n v w‖≤Real.exp (-s*eigenvalue nu n)*(majorantBase nu)^n := by
  have hn := normSq_pos nu hnu n
  have hz := normSq_zero_pos nu hnu.le
  have hv : |(v:ℝ)|≤1 := abs_le.mpr v.2
  have hw : |(w:ℝ)|≤1 := abs_le.mpr w.2
  rw [mode,norm_mul,norm_mul,norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    Real.norm_eq_abs,abs_of_pos (div_pos hz hn),Real.norm_eq_abs,Real.norm_eq_abs]
  calc
    _ ≤ Real.exp (-s*eigenvalue nu n)*((nu+2)^2)^n*2^n*2^n := by
      gcongr
      · exact norm_ratio_le nu hnu n
      · exact poly_eval_bound nu (by linarith) n v hv
      · exact poly_eval_bound nu (by linarith) n w hw
    _ = _ := by
      unfold majorantBase
      rw [mul_pow,show (4:ℝ)=2*2 by norm_num,mul_pow]
      ring

lemma geometric_factor (nu : ℝ) (_hnu : 1<nu) (s : ℝ) (hs : mixingTime nu ≤ s) :
    Real.exp (-s)*majorantBase nu≤1/4 := by
  rw [Real.exp_neg,inv_mul_le_iff₀ (Real.exp_pos s)]
  have he := Real.add_one_le_exp s
  dsimp [mixingTime] at hs
  linarith

 
lemma mode_geometric_bound (nu : ℝ) (hnu : 1<nu) (s : ℝ) (hs : mixingTime nu ≤ s)
    (n : ℕ) (v w : Interval) : ‖mode nu s n v w‖≤(1/4:ℝ)^n := by
  have hb : 0 < majorantBase nu := by unfold majorantBase; positivity
  have hs0 : 0 ≤ s := le_trans (by unfold mixingTime; positivity) hs
  have h1 : Real.exp (-s*eigenvalue nu n)≤Real.exp (-s*(n:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (eigenvalue_ge nu hnu.le n) (neg_nonpos.mpr hs0))
  calc
    _ ≤ Real.exp (-s*eigenvalue nu n)*(majorantBase nu)^n := mode_bound nu hnu s n v w
    _ ≤ Real.exp (-s*(n:ℝ))*(majorantBase nu)^n := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (Real.exp (-s)*majorantBase nu)^n := by rw [mul_comm (-s),Real.exp_nat_mul,mul_pow]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (geometric_factor nu hnu s hs) _

lemma mode_summable (nu : ℝ) (hnu : 1<nu) (s : ℝ) (hs : mixingTime nu ≤ s) (v w : Interval) :
    Summable (fun n => mode nu s n v w) :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num))
    (fun n => mode_geometric_bound nu hnu s hs n v w)

lemma mode_continuous (nu s : ℝ) (n : ℕ) (v : Interval) : Continuous (mode nu s n v) := by
  exact continuous_const.mul ((poly nu n).continuous.comp continuous_subtype_val)

lemma kernel_continuous (nu : ℝ) (hnu : 1<nu) (s : ℝ) (hs : mixingTime nu ≤ s) (v : Interval) :
    Continuous (kernel nu s v) :=
  continuous_tsum (fun n => mode_continuous nu s n v)
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num))
    (fun n w => mode_geometric_bound nu hnu s hs n v w)

lemma mode_zero (nu : ℝ) (hnu : 1<nu) (s : ℝ) (v w : Interval) : mode nu s 0 v w=1 := by
  simp only [mode,eigenvalue,Nat.cast_zero,zero_mul,zero_div,mul_zero,
    Real.exp_zero,div_self (normSq_zero_pos nu hnu.le).ne',poly_zero,eval_one,one_mul]

 
lemma kernel_bounds (nu : ℝ) (hnu : 1<nu) (s : ℝ) (hs : mixingTime nu ≤ s) (v w : Interval) :
    1/2≤kernel nu s v w ∧ kernel nu s v w≤2 := by
  have htail : ‖∑' n, mode nu s (n+1) v w‖≤(1/3:ℝ) := by
    have hh : HasSum (fun n : ℕ => (1/4:ℝ)^(n+1)) (1/3:ℝ) := by
      have hg : HasSum (fun n : ℕ => (1/4:ℝ)^n) ((1-(1/4:ℝ))⁻¹) :=
        hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
      have hh := hg.mul_right (1/4:ℝ)
      norm_num only [show (1-(1/4:ℝ))⁻¹*(1/4)=1/3 by norm_num] at hh
      simpa only [pow_succ] using hh
    exact tsum_of_norm_bounded hh (fun n => mode_geometric_bound nu hnu s hs (n+1) v w)
  rw [Real.norm_eq_abs,abs_le] at htail
  have he := (mode_summable nu hnu s hs v w).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,mode_zero nu hnu s v w] at he
  unfold kernel
  rw [←he]
  constructor <;> linarith [htail.1,htail.2]

end SLEExactGauge.Jacobi
end
end
 

 
section
 

noncomputable section
open Polynomial MeasureTheory Filter Set
open scoped ENNReal Topology CompactlySupported
namespace SLEExactGauge.Jacobi

lemma integral_mode_poly (nu : ℝ) (hnu : 1 < nu) (s : ℝ) (n m : ℕ) (v : Interval) :
    (∫ w : Interval, mode nu s n v w * (poly nu m).eval (w:ℝ) ∂pi nu) =
      if n=m then Real.exp (-s*eigenvalue nu m)*(poly nu m).eval (v:ℝ) else 0 := by
  have he : (fun w : Interval => mode nu s n v w * (poly nu m).eval (w:ℝ)) =
      fun w : Interval => (Real.exp (-s*eigenvalue nu n)*(normSq nu 0/normSq nu n)*
        (poly nu n).eval (v:ℝ))*((poly nu n).eval (w:ℝ)*(poly nu m).eval (w:ℝ)) := by
    funext w; unfold mode; ring
  rw [he,integral_const_mul,integral_pi_poly nu hnu]
  split_ifs with hnm
  · subst n
    have hn := (normSq_pos nu hnu m).ne'
    have hz := (normSq_zero_pos nu hnu.le).ne'
    field_simp
  · ring

lemma integral_kernel_poly (nu : ℝ) (hnu : 1 < nu) (s : ℝ) (hs : mixingTime nu ≤ s)
    (m : ℕ) (v : Interval) :
    (∫ w : Interval, kernel nu s v w * (poly nu m).eval (w:ℝ) ∂pi nu) =
      Real.exp (-s*eigenvalue nu m)*(poly nu m).eval (v:ℝ) := by
  let := pi_probability nu hnu.le
  let F (n : ℕ) (w : Interval) := mode nu s n v w * (poly nu m).eval (w:ℝ)
  have hc (n : ℕ) : Continuous (F n) := (mode_continuous nu s n v).mul
    ((poly nu m).continuous.comp continuous_subtype_val)
  have hb (n : ℕ) (w : Interval) : ‖F n w‖ ≤ (1/4:ℝ)^n*2^m := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul (mode_geometric_bound nu hnu s hs n v w)
      (poly_eval_bound nu (by linarith) m w (abs_le.mpr w.2))
      (norm_nonneg _) (by positivity)
  have hg : Summable (fun n : ℕ => (1/4:ℝ)^n*2^m) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num)).mul_right _
  have hi := hasSum_integral_of_dominated_convergence (μ := pi nu) (F := F)
    (f := fun w => kernel nu s v w * (poly nu m).eval (w:ℝ))
    (fun n (_ : Interval) => (1/4:ℝ)^n*2^m)
    (fun n => (hc n).aestronglyMeasurable)
    (fun n => Eventually.of_forall (hb n)) (Eventually.of_forall fun _ => hg)
    (integrable_const _) (Eventually.of_forall fun w =>
      (mode_summable nu hnu s hs v w).hasSum.mul_right ((poly nu m).eval (w:ℝ)))
  have he (n : ℕ) : (∫ w, F n w ∂pi nu) =
      if n=m then Real.exp (-s*eigenvalue nu m)*(poly nu m).eval (v:ℝ) else 0 :=
    integral_mode_poly nu hnu s n m v
  have ht := hi.tsum_eq.symm
  rw [show (∑' n, ∫ w, F n w ∂pi nu) =
      Real.exp (-s*eigenvalue nu m)*(poly nu m).eval (v:ℝ) by simp only [he,tsum_ite_eq]] at ht
  exact ht

lemma kernel_integrable (nu : ℝ) (hnu : 1 < nu) (s : ℝ) (hs : mixingTime nu ≤ s)
    (v : Interval) : Integrable (kernel nu s v) (pi nu) := by
  let := pi_probability nu hnu.le
  exact (kernel_continuous nu hnu s hs v).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integral_kernel (nu : ℝ) (hnu : 1 < nu) (s : ℝ) (hs : mixingTime nu ≤ s)
    (v : Interval) : (∫ w, kernel nu s v w ∂pi nu)=1 := by
  simpa only [poly_zero,eval_one,mul_one,eigenvalue,Nat.cast_zero,zero_mul,zero_div,
    mul_zero,Real.exp_zero] using integral_kernel_poly nu hnu s hs 0 v

 
def transition (nu s : ℝ) (v : Interval) : Measure Interval :=
  (pi nu).withDensity (fun w => ENNReal.ofReal (kernel nu s v w))

lemma transition_probability (nu : ℝ) (hnu : 1 < nu) (s : ℝ) (hs : mixingTime nu ≤ s)
    (v : Interval) : IsProbabilityMeasure (transition nu s v) := by
  constructor
  rw [transition,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal (kernel_integrable nu hnu s hs v)
    (Eventually.of_forall fun w => le_trans (by norm_num : (0:ℝ)≤1/2)
      (kernel_bounds nu hnu s hs v w).1),integral_kernel nu hnu s hs v]
  norm_num

lemma integral_transition_poly (nu : ℝ) (hnu : 1 < nu) (s : ℝ) (hs : mixingTime nu ≤ s)
    (v : Interval) (m : ℕ) :
    (∫ w : Interval, (poly nu m).eval (w:ℝ) ∂transition nu s v) =
      Real.exp (-s*eigenvalue nu m)*(poly nu m).eval (v:ℝ) := by
  rw [transition,integral_withDensity_eq_integral_toReal_smul
    (kernel_continuous nu hnu s hs v).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (le_trans (by norm_num : (0:ℝ)≤1/2)
    (kernel_bounds nu hnu s hs v _).1),smul_eq_mul]
  exact integral_kernel_poly nu hnu s hs m v

end SLEExactGauge.Jacobi
end
end
 

 
section
 
noncomputable section
open Polynomial MeasureTheory Filter Set
open scoped ENNReal Topology CompactlySupported
namespace SLEExactGauge.Jacobi

lemma polynomial_integrable (μ : Measure Interval) [IsFiniteMeasure μ] (p : ℝ[X]) :
    Integrable (fun x : Interval => p.eval (x:ℝ)) μ :=
  (p.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

 
lemma measure_eq_of_polynomial_integral (μ ν : Measure Interval)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (he : ∀ p : ℝ[X], (∫ x : Interval, p.eval (x:ℝ) ∂μ)=∫ x : Interval, p.eval (x:ℝ) ∂ν) :
    μ=ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨p,hp⟩ := exists_polynomial_near_continuousMap (-1) 1
    f.toContinuousMap (ε/2) (by positivity)
  have hb (x : Interval) : ‖p.eval (x:ℝ)-f x‖≤ε/2 :=
    ((p.toContinuousMapOn Interval-f.toContinuousMap).norm_coe_le_norm x).trans hp.le
  have hbμ : ‖(∫ x : Interval,p.eval (x:ℝ) ∂μ)-(∫ x,f x∂μ)‖≤ε/2 := by
    rw [←integral_sub (polynomial_integrable μ p) f.integrable]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=μ) (Eventually.of_forall hb)
  have hbν : ‖(∫ x : Interval,p.eval (x:ℝ) ∂ν)-(∫ x,f x∂ν)‖≤ε/2 := by
    rw [←integral_sub (polynomial_integrable ν p) f.integrable]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=ν) (Eventually.of_forall hb)
  calc
    _ ≤ dist (∫ x,f x∂μ) (∫ x : Interval,p.eval (x:ℝ) ∂μ)+
        dist (∫ x : Interval,p.eval (x:ℝ) ∂μ) (∫ x,f x∂ν) := dist_triangle _ _ _
    _ ≤ ε/2+ε/2 := by
      apply add_le_add
      · simpa only [dist_eq_norm,norm_sub_rev] using hbμ
      · simpa only [he p,dist_eq_norm] using hbν
    _ = ε := by ring

def polynomialIntegral (μ : Measure Interval) [IsFiniteMeasure μ] : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x : Interval, p.eval (x:ℝ) ∂μ
  map_add' p q := by
    simp only [eval_add]
    exact integral_add (polynomial_integrable μ p) (polynomial_integrable μ q)
  map_smul' c p := by
    simp only [eval_smul,smul_eq_mul,RingHom.id_apply]
    exact integral_const_mul _ _

lemma measure_eq_of_poly_integral (nu : ℝ) (hnu : 0 < nu)
    (μ ν : Measure Interval) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (he : ∀ n, (∫ x : Interval,(poly nu n).eval (x:ℝ) ∂μ)=
      ∫ x : Interval,(poly nu n).eval (x:ℝ) ∂ν) : μ=ν := by
  have heq : polynomialIntegral μ=polynomialIntegral ν := by
    apply (basis nu hnu).ext
    intro n
    simpa only [basis_apply, polynomialIntegral, LinearMap.coe_mk, AddHom.coe_mk] using he n
  apply measure_eq_of_polynomial_integral
  intro p
  exact congrArg (fun L : ℝ[X] →ₗ[ℝ] ℝ => L p) heq

 

lemma transition_identified (nu : ℝ) (hnu : 1 < nu) (s : ℝ) (hs : mixingTime nu ≤ s)
    (v : Interval) (μ : Measure Interval) [IsProbabilityMeasure μ]
    (he : ∀ m, (∫ w : Interval,(poly nu m).eval (w:ℝ) ∂μ)=
      Real.exp (-s*eigenvalue nu m)*(poly nu m).eval (v:ℝ)) : μ=transition nu s v := by
  let := transition_probability nu hnu s hs v
  apply measure_eq_of_poly_integral nu (by linarith)
  intro m
  rw [he m,integral_transition_poly nu hnu s hs v m]

 

lemma transition_lintegral_bounds (nu : ℝ) (hnu : 1 < nu) (s : ℝ) (hs : mixingTime nu ≤ s)
    (v : Interval) (f : Interval→ℝ≥0∞) (hf : Measurable f) :
    (1/2:ℝ≥0∞)*(∫⁻w,f w∂pi nu) ≤ ∫⁻w,f w∂transition nu s v ∧
      (∫⁻w,f w∂transition nu s v) ≤ 2*(∫⁻w,f w∂pi nu) := by
  rw [transition,lintegral_withDensity_eq_lintegral_mul _
    (kernel_continuous nu hnu s hs v).measurable.ennreal_ofReal hf]
  constructor
  · rw [←lintegral_const_mul _ hf]
    apply lintegral_mono
    intro w
    apply mul_le_mul_left
    have h := ENNReal.ofReal_le_ofReal (kernel_bounds nu hnu s hs v w).1
    norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2), ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div] at h ⊢
    exact h
  · rw [←lintegral_const_mul _ hf]
    apply lintegral_mono
    intro w
    apply mul_le_mul_left
    have h := ENNReal.ofReal_le_ofReal (kernel_bounds nu hnu s hs v w).2
    norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2), ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div] at h ⊢
    exact h

end SLEExactGauge.Jacobi
end
end
 

 
section
 

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Interval
namespace SLEExactGauge.Jacobi
open CenteredMoments

lemma weight_cos_sin (nu : ℝ) (hnu : 1<nu) (θ : ℝ) (hθ : θ∈Icc 0 Real.pi) :
    weight nu (Real.cos θ)*Real.sin θ=(Real.sin θ)^nu := by
  have hs : 0≤Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ
  have hid : 1-Real.cos θ^2=Real.sin θ^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [weight,hid,←Real.rpow_natCast_mul hs]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*((nu-1)/2)=nu-1 by ring]
  calc
    (Real.sin θ)^(nu-1)*Real.sin θ = (Real.sin θ)^(nu-1)*(Real.sin θ)^(1:ℝ) := by rw [Real.rpow_one]
    _ = (Real.sin θ)^(nu-1+1) := (Real.rpow_add' hs (by linarith : nu-1+1≠0)).symm
    _ = (Real.sin θ)^nu := by congr 1; ring

lemma integral_sin_cos (nu : ℝ) (hnu : 1<nu) (p : ℝ[X]) :
    (∫θ in 0..Real.pi,(Real.sin θ)^nu*p.eval (Real.cos θ))=
      ∫v in (-1:ℝ)..1,weight nu v*p.eval v := by
  have hsub := intervalIntegral.integral_comp_mul_deriv (a:=0) (b:=Real.pi)
    (f:=Real.cos) (fun θ _ => Real.hasDerivAt_cos θ)
    Real.continuous_sin.neg.continuousOn ((continuous_weight nu hnu.le).mul p.continuous)
  simp only [Real.cos_zero,Real.cos_pi,Function.comp_apply,Pi.mul_apply] at hsub
  rw [intervalIntegral.integral_symm (a := (-1:ℝ)) (b := 1)] at hsub
  have he : (∫θ in 0..Real.pi,weight nu (Real.cos θ)*p.eval (Real.cos θ)*(-Real.sin θ))=
      -(∫θ in 0..Real.pi,(Real.sin θ)^nu*p.eval (Real.cos θ)) := by
    rw [←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' : θ∈Icc 0 Real.pi := by
      simpa only [uIcc_of_le Real.pi_pos.le] using hθ
    dsimp only
    rw [show weight nu (Real.cos θ)*p.eval (Real.cos θ)*(-Real.sin θ)=
      -(weight nu (Real.cos θ)*Real.sin θ)*p.eval (Real.cos θ) by ring,
      weight_cos_sin nu hnu θ hθ']
    ring
  rw [he] at hsub
  exact neg_injective hsub

lemma integral_angleArea (f : ℝ→ℝ) :
    (∫θ : Angle,f θ∂angleArea)=∫θ in 0..Real.pi,f θ := by
  rw [angleArea,integral_subtype_comap measurableSet_Ioo,←integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le Real.pi_pos.le]

lemma angleNormalization_jacobi (a : ℝ) (ha : 1<4*a) :
    angleNormalization a=ENNReal.ofReal (normSq (4*a) 0) := by
  have ha0 : 0≤4*a := by linarith
  have hm : AEStronglyMeasurable (fun θ : Angle => (Real.sin θ)^(4*a)) angleArea := by
    fun_prop
  have hb (θ : Angle) : ‖(Real.sin θ)^(4*a)‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg
      (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2).le _)]
    exact Real.rpow_le_one (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2).le (Real.sin_le_one _) (by linarith)
  have hi : Integrable (fun θ : Angle => (Real.sin θ)^(4*a)) angleArea :=
    Integrable.of_bound hm 1 (Eventually.of_forall hb)
  unfold angleNormalization
  simp only [angleWeight]
  rw [←ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun θ : Angle => Real.rpow_nonneg
      (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2).le _)),integral_angleArea (fun θ : ℝ => (Real.sin θ)^(4*a))]
  have hh := integral_sin_cos (4*a) ha (1:ℝ[X])
  simp only [eval_one,mul_one] at hh
  rw [hh]
  simp only [normSq,inner,poly_zero,eval_one,mul_one]

def angleCos (θ : Angle) : Interval := ⟨Real.cos θ,Real.neg_one_le_cos _,Real.cos_le_one _⟩

lemma angleCos_measurable : Measurable angleCos := by
  unfold angleCos
  fun_prop

lemma integral_angleLaw_poly (a : ℝ) (ha : 1<4*a) (p : ℝ[X]) :
    (∫θ : Angle,p.eval (Real.cos θ)∂angleLaw a)=
      (∫v in (-1:ℝ)..1,weight (4*a) v*p.eval v)/normSq (4*a) 0 := by
  rw [angleLaw,integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (angleWeight_measurable a) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hn (θ : Angle) : 0≤(Real.sin θ)^(4*a) := Real.rpow_nonneg
    (Real.sin_pos_of_pos_of_lt_pi θ.2.1 θ.2.2).le _
  simp_rw [angleWeight,ENNReal.toReal_ofReal (hn _),smul_eq_mul]
  rw [angleNormalization_jacobi a ha,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (normSq_zero_pos (4*a) ha.le).le,integral_angleArea (fun θ : ℝ => (Real.sin θ)^(4*a)*p.eval (Real.cos θ)),integral_sin_cos (4*a) ha p]
  ring

 
lemma map_angleLaw_eq_pi (a : ℝ) (ha : 1<4*a) :
    (angleLaw a).map angleCos=pi (4*a) := by
  have := angleLaw_probability a (by linarith)
  have := pi_probability (4*a) ha.le
  apply measure_eq_of_polynomial_integral
  intro p
  have hf : AEStronglyMeasurable (fun v : Interval => p.eval (v:ℝ)) ((angleLaw a).map angleCos) :=
    (p.continuous.comp continuous_subtype_val).aestronglyMeasurable
  rw [integral_map angleCos_measurable.aemeasurable hf]
  change (∫θ : Angle,p.eval (Real.cos θ)∂angleLaw a)=_
  rw [integral_angleLaw_poly a ha]
  have hh := integral_pi_mul (4*a) ha.le p (1:ℝ[X])
  simpa only [eval_one,mul_one,inner] using hh.symm

end SLEExactGauge.Jacobi
end
end

end OAI
