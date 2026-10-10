import Mathlib
import OAI.Probability.LogConcave.Numerics.NodePolynomial

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma chainTaylor_hasDerivAt (J : ℕ → ℝ → E) (n : ℕ) (a x : ℝ) :
    HasDerivAt (chainTaylor J (n+1) a)
      (chainTaylor (fun k => J (k+1)) n a x) x := by
  have he (t : ℝ) : chainTaylor J (n+1) a t=
      (∑k∈Finset.range (n+1), (((k+1).factorial:ℝ)⁻¹*(t-a)^(k+1)) • J (k+1) a)+J 0 a := by
    simp only [chainTaylor,Finset.sum_range_succ',Nat.factorial_zero,Nat.cast_one,
      inv_one,pow_zero,mul_one,one_smul]
  rw [funext he]
  have h (k : ℕ) : HasDerivAt
      (fun t : ℝ => (((k+1).factorial:ℝ)⁻¹*(t-a)^(k+1)) • J (k+1) a)
      (((k.factorial:ℝ)⁻¹*(x-a)^k) • J (k+1) a) x := by
    have hh := ((((hasDerivAt_id x).sub_const a).pow (k+1)).const_mul
      (((k+1).factorial:ℝ)⁻¹)).smul_const (J (k+1) a)
    convert hh using 1
    congr 1
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hk : (k:ℝ)+1≠0 := by positivity
    have hkf : (k.factorial:ℝ)≠0 := by positivity
    simp only [Nat.add_sub_cancel,mul_one]
    field_simp
    rfl
  exact (HasDerivAt.fun_sum (fun k _ => h k)).add_const (J 0 a)

omit [CompleteSpace E] in
lemma chainTaylor_deriv (J : ℕ → ℝ → E) (n : ℕ) (a x : ℝ) :
    deriv (chainTaylor J (n+1) a) x=chainTaylor (fun k => J (k+1)) n a x :=
  (chainTaylor_hasDerivAt J n a x).deriv

omit [CompleteSpace E] in
lemma chainTaylor_second_deriv (J : ℕ → ℝ → E) (n : ℕ) (a x : ℝ) :
    deriv (deriv (chainTaylor J (n+2) a)) x=chainTaylor (fun k => J (k+2)) n a x := by
  rw [show deriv (chainTaylor J (n+2) a)=chainTaylor (fun k => J (k+1)) (n+1) a from
    funext (chainTaylor_deriv J (n+1) a)]
  exact chainTaylor_deriv (fun k => J (k+1)) n a x

omit [CompleteSpace E] in
lemma chainTaylor_joint_continuous {X : Type*} [TopologicalSpace X]
    (J : ℕ → ℝ → X → E) (a : ℝ) (hJ : ∀k,Continuous (J k a)) (n : ℕ) :
    Continuous (fun p : ℝ × X => chainTaylor (fun k t => J k t p.2) n a p.1) := by
  unfold chainTaylor
  exact continuous_finsetSum _ (fun k _ =>
    (continuous_const.mul ((continuous_fst.sub continuous_const).pow k)).smul ((hJ k).comp continuous_snd))
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def basisDerivative (u : I → ℝ) (i : I) (t : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ u i).derivative.eval t

def derivativeInterpolation (u : I → ℝ) (v : I → E) (t : ℝ) : E :=
  ∑i,basisDerivative u i t • v i

lemma basisDerivative_continuous (u : I → ℝ) (i : I) : Continuous (basisDerivative u i) :=
  Polynomial.continuous _

omit [CompleteSpace E] in
lemma interpolation_hasDerivAt (u : I → ℝ) (v : I → E) (t : ℝ) :
    HasDerivAt (interpolation u v) (derivativeInterpolation u v t) t := by
  exact HasDerivAt.fun_sum (fun i _ =>
    ((Lagrange.basis Finset.univ u i).hasDerivAt t).smul_const (v i))

omit [CompleteSpace E] in
lemma derivativeInterpolation_chainTaylor (u : I → ℝ) (hu : Function.Injective u)
    (n : ℕ) (hn : n+2≤Fintype.card I) (J : ℕ → ℝ → E) (a ℓ t : ℝ) :
    derivativeInterpolation u (fun i => chainTaylor J (n+1) a (a+ℓ*u i)) t=
      ℓ • chainTaylor (fun k => J (k+1)) n a (a+ℓ*t) := by
  have he : interpolation u (fun i => chainTaylor J (n+1) a (a+ℓ*u i))=
      fun t => chainTaylor J (n+1) a (a+ℓ*t) :=
    funext (reproduces_cell_chainTaylor u hu (n+1) hn J a ℓ)
  have h := interpolation_hasDerivAt u (fun i => chainTaylor J (n+1) a (a+ℓ*u i)) t
  rw [he] at h
  have ht := ((chainTaylor_hasDerivAt J n a (a+ℓ*t)).scomp t
    (((hasDerivAt_id t).const_mul ℓ).const_add a))
  have ht' : HasDerivAt (fun t => chainTaylor J (n+1) a (a+ℓ*t))
      (ℓ • chainTaylor (fun k => J (k+1)) n a (a+ℓ*t)) t := by
    simpa only [Function.comp_def,mul_one,id_eq] using ht
  exact h.unique ht'

omit [CompleteSpace E] in
lemma derivativeInterpolation_sub (u : I → ℝ) (v w : I → E) (t : ℝ) :
    derivativeInterpolation u (fun i => v i-w i) t=
      derivativeInterpolation u v t-derivativeInterpolation u w t := by
  simp only [derivativeInterpolation,smul_sub,Finset.sum_sub_distrib]

omit [CompleteSpace E] in
lemma derivative_cell_chain_error_eq (u : I → ℝ) (hu : Function.Injective u)
    (n : ℕ) (hn : n+2≤Fintype.card I) (J : ℕ → ℝ → E)
    (a t : ℝ) {ℓ : ℝ} (hℓ : ℓ≠0) :
    J 1 (a+ℓ*t)-ℓ⁻¹ • derivativeInterpolation u (fun i => J 0 (a+ℓ*u i)) t=
      (J 1 (a+ℓ*t)-chainTaylor (fun k => J (k+1)) n a (a+ℓ*t))-
        ℓ⁻¹ • derivativeInterpolation u
          (fun i => J 0 (a+ℓ*u i)-chainTaylor J (n+1) a (a+ℓ*u i)) t := by
  rw [derivativeInterpolation_sub,derivativeInterpolation_chainTaylor u hu n hn,
    smul_sub,smul_smul,inv_mul_cancel₀ hℓ,one_smul]
  abel

lemma exists_basisDerivative_budget (u : I → ℝ) :
    ∃C : ℝ,1≤C ∧ ∀t∈Icc (0:ℝ) 1,∑i,|basisDerivative u i t|≤C := by
  have hc : Continuous (fun t => ∑i,|basisDerivative u i t|) :=
    continuous_finsetSum _ (fun i _ => (basisDerivative_continuous u i).abs)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1,le_max_right _ _,fun t ht => ?_⟩
  have hn : 0≤∑i,|basisDerivative u i t| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hh : (∑i,|basisDerivative u i t|)≤C := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hC t ht
  exact hh.trans (le_max_left _ _)
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Filter
open scoped BigOperators

namespace RMSIntegral
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma smul_sq_bound (c : ℝ) {f : Ω → E}
    (hi : Integrable (fun z => ‖f z‖^2) μ) {B : ℝ}
    (hB : (∫z,‖f z‖^2 ∂μ)≤B) :
    Integrable (fun z => ‖c • f z‖^2) μ ∧
      (∫z,‖c • f z‖^2 ∂μ)≤c^2*B := by
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  exact ⟨hi.const_mul _,by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hB (sq_nonneg c)⟩
end RMSIntegral

namespace Quadrature
variable {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [SFinite μ]

lemma chainTaylor_cell_rms (J : ℕ → ℝ × Ω → E)
    (hJc : ∀k,Continuous (J k))
    (hJ : ∀k t z,HasDerivAt (fun t => J k (t,z)) (J (k+1) (t,z)) t)
    (n : ℕ) {a x b B : ℝ} (hax : a≤x) (hxb : x≤b) (hB0 : 0≤B)
    (hi : ∀t∈Icc a b,Integrable (fun z => ‖J (n+1) (t,z)‖^2) μ)
    (hB : ∀t∈Icc a b,(∫z,‖J (n+1) (t,z)‖^2 ∂μ)≤B) :
    Integrable (fun z => ‖J 0 (x,z)-chainTaylor (fun k t => J k (t,z)) n a x‖^2) μ ∧
      (∫z,‖J 0 (x,z)-chainTaylor (fun k t => J k (t,z)) n a x‖^2 ∂μ)≤
        ((x-a)^(n+1))^2*B := by
  have hh := chainTaylor_remainder_rms (J:=fun k t z => J k (t,z)) (s:=univ) (n:=n)
    hax hB0 (subset_univ _) (fun z k t _ => (hJ k t z).hasDerivWithinAt)
    (hJc (n+1)).aestronglyMeasurable
    (fun t ht => hi t ⟨ht.1.le,ht.2.trans hxb⟩)
    (fun t ht => hB t ⟨ht.1.le,ht.2.trans hxb⟩)
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ hB0
  apply pow_le_pow_left₀ (div_nonneg (pow_nonneg (sub_nonneg.mpr hax) _) (Nat.cast_nonneg _))
  apply div_le_self (pow_nonneg (sub_nonneg.mpr hax) _)
  exact_mod_cast Nat.factorial_pos n

lemma chainTaylor_regularized_derivative_rms (J : ℕ → ℝ × Ω → E)
    (hJc : ∀k,Continuous (J k))
    (hJ : ∀k t z,HasDerivAt (fun t => J k (t,z)) (J (k+1) (t,z)) t)
    (n : ℕ) {ℓ z B : ℝ} (hℓ : 0<ℓ) (hz : z∈Icc (0:ℝ) 1) (hB0 : 0≤B)
    (hi : ∀t∈Icc (0:ℝ) ℓ,Integrable (fun y => ‖J (n+2) (t,y)‖^2) μ)
    (hB : ∀t∈Icc (0:ℝ) ℓ,(∫y,‖J (n+2) (t,y)‖^2 ∂μ)≤B) :
    let f := fun y => z⁻¹ • (J 1 (ℓ*z,y)-
      chainTaylor (fun k t => J (k+1) (t,y)) n 0 (ℓ*z))
    Integrable (fun y => ‖f y‖^2) μ ∧
      (∫y,‖f y‖^2 ∂μ)≤(ℓ^(n+1))^2*B := by
  dsimp only
  have h0 : 0≤ℓ*z := mul_nonneg hℓ.le hz.1
  have h1 : ℓ*z≤ℓ := by nlinarith [hz.2]
  have hh := chainTaylor_cell_rms (fun k => J (k+1)) (fun k => hJc (k+1))
    (fun k t y => hJ (k+1) t y) n h0 h1 hB0 hi hB
  simp only [Nat.zero_add,sub_zero] at hh
  have hv := RMSIntegral.smul_sq_bound z⁻¹ hh.1 hh.2
  refine ⟨hv.1,hv.2.trans ?_⟩
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ hB0
  by_cases hzne : z=0
  · simp only [hzne,inv_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul]
    exact sq_nonneg _
  · have he : z⁻¹^2*((ℓ*z)^(n+1))^2=(ℓ^(n+1))^2*(z^n)^2 := by
      rw [mul_pow,pow_succ z]
      field_simp
    rw [he]
    apply mul_le_of_le_one_right (sq_nonneg _)
    exact pow_le_one₀ (pow_nonneg hz.1 _) (pow_le_one₀ hz.1 hz.2)
end Quadrature
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Filter
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [SFinite μ]

theorem derivative_cell_error_rms (u : I → ℝ) (hu : Function.Injective u)
    (hun : ∀i,u i∈Icc (0:ℝ) 1) (n : ℕ) (hcard : n+2≤Fintype.card I)
    (J : ℕ → ℝ × Ω → E) (hJc : ∀k,Continuous (J k))
    (hJ : ∀k t z,HasDerivAt (fun t => J k (t,z)) (J (k+1) (t,z)) t)
    {a ℓ t B : ℝ} (hℓ : 0<ℓ) (ht : t∈Icc (0:ℝ) 1) (hB0 : 0≤B)
    (hi : ∀s∈Icc a (a+ℓ),Integrable (fun z => ‖J (n+2) (s,z)‖^2) μ)
    (hB : ∀s∈Icc a (a+ℓ),(∫z,‖J (n+2) (s,z)‖^2 ∂μ)≤B) :
    let err := fun z => J 1 (a+ℓ*t,z)-ℓ⁻¹ •
      derivativeInterpolation u (fun i => J 0 (a+ℓ*u i,z)) t
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤
        2*(1+(∑i,|basisDerivative u i t|)^2)*(ℓ^(n+1))^2*B := by
  dsimp only
  let P := fun (t : ℝ) (z : Ω) => J 0 (t,z)-chainTaylor (fun k v => J k (v,z)) (n+1) a t
  let R := fun z => J 1 (a+ℓ*t,z)-chainTaylor (fun k v => J (k+1) (v,z)) n a (a+ℓ*t)
  have hpoint (v : ℝ) (hv : v∈Icc (0:ℝ) 1) :
      a≤a+ℓ*v ∧ a+ℓ*v≤a+ℓ := by
    constructor <;> nlinarith [hv.1,hv.2]
  have hR := chainTaylor_cell_rms (fun k => J (k+1)) (fun k => hJc (k+1))
    (fun k s z => hJ (k+1) s z) n (hpoint t ht).1 (hpoint t ht).2 hB0 hi hB
  have hRb : (∫z,‖R z‖^2 ∂μ)≤(ℓ^(n+1))^2*B := by
    refine hR.2.trans ?_
    apply mul_le_mul_of_nonneg_right _ hB0
    apply pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr (hpoint t ht).1) _)
    exact pow_le_pow_left₀ (sub_nonneg.mpr (hpoint t ht).1) (by linarith [(hpoint t ht).2]) _
  have hnode (i : I) : Integrable (fun z => ‖P (a+ℓ*u i) z‖^2) μ ∧
      (∫z,‖P (a+ℓ*u i) z‖^2 ∂μ)≤(ℓ^(n+2))^2*B := by
    have hh := chainTaylor_cell_rms J hJc hJ (n+1)
      (hpoint (u i) (hun i)).1 (hpoint (u i) (hun i)).2 hB0 hi hB
    refine ⟨hh.1,hh.2.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ hB0
    apply pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr (hpoint (u i) (hun i)).1) _)
    exact pow_le_pow_left₀ (sub_nonneg.mpr (hpoint (u i) (hun i)).1)
      (by linarith [(hpoint (u i) (hun i)).2]) _
  have hPc : Continuous (fun p : ℝ × Ω => P p.1 p.2) :=
    (hJc 0).sub (chainTaylor_joint_continuous (fun k v z => J k (v,z)) a
      (fun k => (hJc k).comp (continuous_const.prodMk continuous_id)) (n+1))
  have hnm (i : I) : AEStronglyMeasurable (P (a+ℓ*u i)) μ :=
    (hPc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hsum := RMSIntegral.weighted_sum_sq (fun i => basisDerivative u i t)
    (fun i => P (a+ℓ*u i)) hnm (fun i => (hnode i).1) (fun i => (hnode i).2)
  have hscaled := RMSIntegral.smul_sq_bound ℓ⁻¹ hsum.1 hsum.2
  have hRc : Continuous R :=
    ((hJc 1).comp (continuous_const.prodMk continuous_id)).sub
      ((chainTaylor_joint_continuous (fun k v z => J (k+1) (v,z)) a
        (fun k => (hJc (k+1)).comp (continuous_const.prodMk continuous_id)) n).comp
          (continuous_const.prodMk continuous_id))
  have hsm : AEStronglyMeasurable
      (fun z => ℓ⁻¹ • ∑i,basisDerivative u i t • P (a+ℓ*u i) z) μ := by
    exact (Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (hnm i).const_smul _)).const_smul _
  have hdiff := RMSIntegral.sub_sq_bound hRc.aestronglyMeasurable hsm
    hR.1 hscaled.1 hRb hscaled.2
  have he (z : Ω) := derivative_cell_chain_error_eq u hu n hcard
    (fun k s => J k (s,z)) a t hℓ.ne'
  simp_rw [he]
  refine ⟨hdiff.1,hdiff.2.trans_eq ?_⟩
  rw [pow_succ ℓ (n+1)]
  field_simp
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Filter
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma regularized_intervalIntegrable {f : ℝ → E} (hf : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (h0 : f 0=0) :
    IntervalIntegrable (fun t => t⁻¹ • f t) volume 0 1 := by
  have hc : Continuous (dslope f 0) := continuousOn_univ.mp
    ((continuousOn_dslope (s:=univ) (by simp)).mpr ⟨hf.continuousOn,hd⟩)
  apply (hc.intervalIntegrable 0 1).congr_uIoo
  intro t ht
  rw [uIoo_of_le (by norm_num : (0:ℝ)≤1)] at ht
  simp only [dslope_of_ne f ht.1.ne',slope_def_module,h0,sub_zero]

lemma zeroHermite_chainTaylor_integral (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (n : ℕ) (hcard : n+1≤Fintype.card I)
    (J : ℕ → ℝ → E) (hJ : J 1 0=0) {ℓ : ℝ} (hℓ : 0<ℓ) :
    (∫t in (0:ℝ)..1,t⁻¹ • chainTaylor (fun k => J (k+1)) n 0 (ℓ*t))=
      ∑i,(zeroHermiteWeight u i₀ i/ℓ) • chainTaylor J (n+1) 0 (ℓ*u i) := by
  let v := fun i => chainTaylor J (n+1) 0 (ℓ*u i)
  have he := funext (zeroHermite_reproduces_chainTaylor u hu i₀ hu0 (n+1)
    (by omega) hcard J hJ ℓ)
  have heD (t : ℝ) : deriv (zeroHermiteInterpolation u i₀ v) t=
      ℓ • chainTaylor (fun k => J (k+1)) n 0 (ℓ*t) := by
    dsimp only [v]
    rw [he]
    simpa only [Function.comp_def,mul_one] using
      ((chainTaylor_hasDerivAt J n 0 (ℓ*t)).scomp t
        ((hasDerivAt_id t).const_mul ℓ)).deriv
  calc
    _ = ∫t in (0:ℝ)..1,ℓ⁻¹ • zeroHermiteAction u i₀ v t := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      dsimp only
      rw [zeroHermiteAction_eq u hu i₀ hu0 v ht.1.ne',heD]
      simp only [smul_smul]
      congr 1
      field_simp
    _ = ℓ⁻¹ • ∑i,zeroHermiteWeight u i₀ i • v i := by
      rw [intervalIntegral.integral_smul,zeroHermiteAction_integral]
    _ = _ := by
      simp only [Finset.smul_sum,smul_smul,div_eq_mul_inv,mul_comm,v]

lemma zeroHermite_derivative_error_eq (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (n : ℕ) (hcard : n+1≤Fintype.card I)
    (J : ℕ → ℝ → E) (hJc : ∀k,Continuous (J k))
    (hJ : ∀k t,HasDerivAt (J k) (J (k+1) t) t) (hz : J 1 0=0)
    {ℓ : ℝ} (hℓ : 0<ℓ) :
    (∫t in (0:ℝ)..1,t⁻¹ • J 1 (ℓ*t))-
      (∑i,(zeroHermiteWeight u i₀ i/ℓ) • J 0 (ℓ*u i))=
    (∫t in (0:ℝ)..1,t⁻¹ • (J 1 (ℓ*t)-chainTaylor (fun k => J (k+1)) n 0 (ℓ*t)))-
      (∑i,(zeroHermiteWeight u i₀ i/ℓ) • (J 0 (ℓ*u i)-chainTaylor J (n+1) 0 (ℓ*u i))) := by
  have h1 := regularized_intervalIntegrable ((hJc 1).comp (continuous_const.mul continuous_id))
    (((hJ 1 (ℓ*0)).scomp 0 ((hasDerivAt_id 0).const_mul ℓ)).differentiableAt)
    (by simpa using hz)
  change IntervalIntegrable (fun t => t⁻¹ • J 1 (ℓ*t)) volume 0 1 at h1
  have hp : Continuous (fun t => chainTaylor (fun k => J (k+1)) n 0 (ℓ*t)) := by
    unfold chainTaylor
    fun_prop
  have hpd : DifferentiableAt ℝ (fun t => chainTaylor (fun k => J (k+1)) n 0 (ℓ*t)) 0 := by
    unfold chainTaylor
    fun_prop
  have hp0 : chainTaylor (fun k => J (k+1)) n 0 (ℓ*0)=0 := by
    simp [chainTaylor,Finset.sum_range_succ',hz]
  have h2 := regularized_intervalIntegrable hp hpd hp0
  simp only [smul_sub,Finset.sum_sub_distrib]
  rw [intervalIntegral.integral_sub h1 h2,zeroHermite_chainTaylor_integral u hu i₀ hu0 n hcard J hz hℓ]
  abel
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open Set MeasureTheory Filter
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [SFinite μ]

theorem zeroHermite_derivative_error_rms (u : I → ℝ) (hu : Function.Injective u)
    (i₀ : I) (hu0 : u i₀=0) (hun : ∀i,u i∈Icc (0:ℝ) 1)
    (n : ℕ) (hcard : n+1≤Fintype.card I)
    (J : ℕ → ℝ × Ω → E) (hJc : ∀k,Continuous (J k))
    (hJ : ∀k t z,HasDerivAt (fun t => J k (t,z)) (J (k+1) (t,z)) t)
    (hz : ∀z,J 1 (0,z)=0) {ℓ B : ℝ} (hℓ : 0<ℓ) (hB0 : 0≤B)
    (hi : ∀t∈Icc (0:ℝ) ℓ,Integrable (fun z => ‖J (n+2) (t,z)‖^2) μ)
    (hB : ∀t∈Icc (0:ℝ) ℓ,(∫z,‖J (n+2) (t,z)‖^2 ∂μ)≤B) :
    let err := fun z => (∫t in (0:ℝ)..1,t⁻¹ • J 1 (ℓ*t,z))-
      ∑i,(zeroHermiteWeight u i₀ i/ℓ) • J 0 (ℓ*u i,z)
    Integrable (fun z => ‖err z‖^2) μ ∧
      (∫z,‖err z‖^2 ∂μ)≤
        2*(1+(∑i,|zeroHermiteWeight u i₀ i|)^2)*(ℓ^(n+1))^2*B := by
  dsimp only
  let R := fun (t : ℝ) (z : Ω) => J 1 (ℓ*t,z)-
    chainTaylor (fun k v => J (k+1) (v,z)) n 0 (ℓ*t)
  let f := fun p : ℝ × Ω => p.1⁻¹ • R p.1 p.2
  let η : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)
  have hRc : Continuous (fun p : ℝ × Ω => R p.1 p.2) := by
    apply Continuous.sub
    · exact (hJc 1).comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
    · exact (chainTaylor_joint_continuous (fun k v z => J (k+1) (v,z)) 0
        (fun k => (hJc (k+1)).comp (continuous_const.prodMk continuous_id)) n).comp
          ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hfm : AEStronglyMeasurable f (η.prod μ) :=
    measurable_fst.inv.aestronglyMeasurable.smul hRc.aestronglyMeasurable
  have hrms (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :=
    chainTaylor_regularized_derivative_rms J hJc hJ n hℓ ht hB0 hi hB
  have hint := RMSIntegral.time_seed_uniform hfm
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => (hrms t ⟨ht.1.le,ht.2⟩).1))
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => (hrms t ⟨ht.1.le,ht.2⟩).2))
  have heta : η.real univ=1 := by
    simp only [η,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,
      ENNReal.ofReal_one,ENNReal.toReal_one]
  rw [heta,one_pow,one_mul] at hint
  let P := fun (t : ℝ) (z : Ω) => J 0 (t,z)-chainTaylor (fun k v => J k (v,z)) (n+1) 0 t
  have hPc : Continuous (fun p : ℝ × Ω => P p.1 p.2) :=
    (hJc 0).sub (chainTaylor_joint_continuous (fun k v z => J k (v,z)) 0
      (fun k => (hJc k).comp (continuous_const.prodMk continuous_id)) (n+1))
  have hnode (i : I) : Integrable (fun z => ‖P (ℓ*u i) z‖^2) μ ∧
      (∫z,‖P (ℓ*u i) z‖^2 ∂μ)≤(ℓ^(n+2))^2*B := by
    have h0 : 0≤ℓ*u i := mul_nonneg hℓ.le (hun i).1
    have h1 : ℓ*u i≤ℓ := mul_le_of_le_one_right hℓ.le (hun i).2
    obtain ⟨hi',hb'⟩ := chainTaylor_cell_rms J hJc hJ (n+1) h0 h1 hB0 hi hB
    refine ⟨hi',hb'.trans ?_⟩
    simp only [sub_zero]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (pow_nonneg h0 _) (pow_le_pow_left₀ h0 h1 _) 2) hB0
  have hnm (i : I) : AEStronglyMeasurable (P (ℓ*u i)) μ :=
    (hPc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hsum := RMSIntegral.weighted_sum_sq (fun i => zeroHermiteWeight u i₀ i/ℓ)
    (fun i => P (ℓ*u i)) hnm (fun i => (hnode i).1) (fun i => (hnode i).2)
  rw [zeroHermite_weights_abs u i₀ hℓ] at hsum
  have hsm : AEStronglyMeasurable
      (fun z => ∑i,(zeroHermiteWeight u i₀ i/ℓ) • P (ℓ*u i) z) μ := by
    exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (hnm i).const_smul _)
  have hdiff := RMSIntegral.sub_sq_bound hfm.prod_swap.integral_prod_right' hsm hint.1 hsum.1 hint.2 hsum.2
  have he (z : Ω) := zeroHermite_derivative_error_eq u hu i₀ hu0 n hcard
    (fun k t => J k (t,z)) (fun k => (hJc k).comp (continuous_id.prodMk continuous_const))
    (fun k t => hJ k t z) (hz z) hℓ
  simp_rw [he,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  refine ⟨hdiff.1,hdiff.2.trans_eq ?_⟩
  rw [pow_succ ℓ (n+1)]
  field_simp
end LogConcaveSampling.Quadrature

end

end

end OAI
