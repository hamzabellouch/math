import Mathlib
import OAI.Probability.LogConcave.Numerics.NormSubSqTwo

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def basis (u : I → ℝ) (i : I) (t : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ u i).eval t

def interpolation (u : I → ℝ) (f : I → E) (t : ℝ) : E :=
  ∑i,basis u i t • f i

def weight (u : I → ℝ) (i : I) (a b : ℝ) : ℝ := ∫t in a..b,basis u i t

lemma basis_continuous (u : I → ℝ) (i : I) : Continuous (basis u i) :=
  Polynomial.continuous _

lemma weight_integral (u : I → ℝ) (f : I → E) (a b : ℝ) :
    ∫t in a..b,interpolation u f t=∑i,weight u i a b • f i := by
  simp only [interpolation]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact intervalIntegral.integral_smul_const (basis u i) (f i)
  · intro i _
    exact ((basis_continuous u i).smul continuous_const).intervalIntegrable a b

lemma reproduces_scalar (u : I → ℝ) (hu : Function.Injective u)
    (p : ℝ[X]) (hp : p.degree<Fintype.card I) (t : ℝ) :
    (∑i,basis u i t*p.eval (u i))=p.eval t := by
  have he := congrArg (fun q : ℝ[X] => q.eval t)
    (Lagrange.eq_interpolate (s:=Finset.univ) hu.injOn (by simpa using hp))
  simpa only [Lagrange.interpolate_apply,eval_finsetSum,eval_mul,eval_C,basis,mul_comm] using he.symm

lemma reproduces_power (u : I → ℝ) (hu : Function.Injective u) (k : ℕ)
    (hk : k<Fintype.card I) (t : ℝ) :
    (∑i,basis u i t*(u i)^k)=t^k := by
  have hh := reproduces_scalar u hu (X^k) (by simpa using hk) t
  simpa only [eval_pow,eval_X] using hh

omit [CompleteSpace E] in
lemma reproduces_vector (u : I → ℝ) (hu : Function.Injective u) (m : ℕ)
    (hm : m≤Fintype.card I) (v : Fin m → E) (t : ℝ) :
    interpolation u (fun i => ∑k : Fin m,(u i)^(k:ℕ) • v k) t=
      ∑k : Fin m,t^(k:ℕ) • v k := by
  unfold interpolation
  simp_rw [Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [←Finset.sum_smul,reproduces_power u hu k (lt_of_lt_of_le k.2 hm)]

lemma exists_basis_budget (u : I → ℝ) :
    ∃C : ℝ,1≤C ∧ ∀t∈Icc (0:ℝ) 1,∑i,|basis u i t|≤C := by
  have hc : Continuous (fun t => ∑i,|basis u i t|) :=
    continuous_finsetSum _ (fun i _ => (basis_continuous u i).abs)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1,le_max_right _ _,fun t ht => ?_⟩
  have hn : 0≤∑i,|basis u i t| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hh : (∑i,|basis u i t|)≤C := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hC t ht
  exact hh.trans (le_max_left _ _)
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ]

omit [CompleteSpace E] in
lemma norm_integral_sq (f : α → E) (hf : MemLp f 2 μ) :
    ‖∫x,f x ∂μ‖^2 ≤ μ.real univ * ∫x,‖f x‖^2 ∂μ := by
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 from by constructor <;> norm_num)
    (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))
    (Filter.Eventually.of_forall (fun _ : α => (by norm_num : (0:ℝ)≤1)))
    (by simpa using hf.norm) (by simpa using (memLp_const (μ:=μ) (1:ℝ) : MemLp (fun _ : α => (1:ℝ)) 2 μ))
  simp only [mul_one,Real.rpow_two,one_pow,integral_const,smul_eq_mul,mul_one] at hh
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow] at hh
  have hi : 0≤∫x,‖f x‖^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have ha := (norm_integral_le_integral_norm f).trans hh
  have hs := pow_le_pow_left₀ (norm_nonneg _) ha 2
  simpa only [mul_pow,Real.sq_sqrt hi,Real.sq_sqrt (show 0≤μ.real univ from measureReal_nonneg),mul_comm] using hs

omit [CompleteSpace E] in
lemma time_seed_sq [SFinite ν] {f : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hi : Integrable (fun p => ‖f p‖^2) (μ.prod ν)) :
    Integrable (fun z => ‖∫t,f (t,z) ∂μ‖^2) ν ∧
      (∫z,‖∫t,f (t,z) ∂μ‖^2 ∂ν)≤
        μ.real univ * (∫t,∫z,‖f (t,z)‖^2 ∂ν ∂μ) := by
  have hsq := hi.integral_prod_right
  have hm : AEStronglyMeasurable (fun z => ∫t,f (t,z) ∂μ) ν :=
    hf.prod_swap.integral_prod_right'
  have hbound : ∀ᵐ z ∂ν,‖∫t,f (t,z) ∂μ‖^2≤μ.real univ*(∫t,‖f (t,z)‖^2 ∂μ) := by
    filter_upwards [hi.prod_left_ae,hf.prodMk_right] with z hz hzm
    exact norm_integral_sq _ ((memLp_two_iff_integrable_sq_norm hzm).mpr hz)
  have hiout : Integrable (fun z => ‖∫t,f (t,z) ∂μ‖^2) ν := by
    apply (hsq.const_mul (μ.real univ)).mono' (hm.norm.pow 2)
    filter_upwards [hbound] with z hz
    simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_sq] using hz
  refine ⟨hiout,?_⟩
  calc
    _ ≤ ∫z,μ.real univ*(∫t,‖f (t,z)‖^2 ∂μ) ∂ν := integral_mono_ae hiout (hsq.const_mul _) hbound
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact (integral_integral_swap (f:=fun t z => ‖f (t,z)‖^2) hi).symm
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [SFinite ν]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integrable_sq_of_uniform {f : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν)) {B : ℝ}
    (hslice : ∀ᵐ t ∂μ,Integrable (fun z => ‖f (t,z)‖^2) ν)
    (hB : ∀ᵐ t ∂μ,(∫z,‖f (t,z)‖^2 ∂ν)≤B) :
    Integrable (fun p => ‖f p‖^2) (μ.prod ν) := by
  apply (integrable_prod_iff (hf.norm.pow 2)).mpr
  refine ⟨hslice,?_⟩
  simp only [Pi.pow_apply,Real.norm_eq_abs,abs_sq]
  apply (integrable_const B).mono' ((hf.norm.pow 2).integral_prod_right')
  filter_upwards [hB] with t ht
  have hn : 0≤∫z,‖f (t,z)‖^2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hn,Pi.pow_apply] using ht

omit [CompleteSpace E] in
theorem time_seed_uniform {f : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν)) {B : ℝ}
    (hslice : ∀ᵐ t ∂μ,Integrable (fun z => ‖f (t,z)‖^2) ν)
    (hB : ∀ᵐ t ∂μ,(∫z,‖f (t,z)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∫t,f (t,z) ∂μ‖^2) ν ∧
      (∫z,‖∫t,f (t,z) ∂μ‖^2 ∂ν)≤(μ.real univ)^2*B := by
  have hi := integrable_sq_of_uniform hf hslice hB
  obtain ⟨ho,hv⟩ := time_seed_sq hf hi
  refine ⟨ho,hv.trans ?_⟩
  have hh := integral_mono_ae hi.integral_prod_left (integrable_const B) hB
  simp only [integral_const,smul_eq_mul] at hh
  convert mul_le_mul_of_nonneg_left hh (measureReal_nonneg (μ:=μ) (s:=univ)) using 1
  ring
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure Ω} [SFinite ν]

omit [CompleteSpace E] in
lemma interpolation_continuous (u : I → ℝ) (v : I → E) : Continuous (interpolation u v) :=
  continuous_finsetSum _ (fun i _ => (basis_continuous u i).smul continuous_const)

lemma weights_abs_bound (u : I → ℝ) {C θ : ℝ} (hθ0 : 0≤θ) (hθ1 : θ≤1)
    (hC : ∀t∈Icc (0:ℝ) 1,∑i,|basis u i t|≤C) :
    ∑i,|weight u i 0 θ|≤(Fintype.card I:ℝ)*C*θ := by
  have hb (i : I) : |weight u i 0 θ|≤C*θ := by
    have hw := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=θ)
      (f:=basis u i) (C:=C) (fun t ht => by
        rw [uIoc_of_le hθ0] at ht
        have hc := (Finset.single_le_sum (fun j _ => abs_nonneg (basis u j t)) (Finset.mem_univ i)).trans
          (hC t ⟨ht.1.le,ht.2.trans hθ1⟩)
        simpa only [Real.norm_eq_abs] using hc)
    simpa only [weight,Real.norm_eq_abs,sub_zero,abs_of_nonneg hθ0] using hw
  calc
    _ ≤ ∑_i : I,C*θ := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

def cellQuadrature (u : I → ℝ) (v : I → E) (ℓ θ : ℝ) : E :=
  ∑i,(ℓ*weight u i 0 θ) • v i

lemma cellQuadrature_eq_integral (u : I → ℝ) (v : I → E) (ℓ θ : ℝ) :
    cellQuadrature u v ℓ θ=ℓ • ∫t in 0..θ,interpolation u v t := by
  rw [weight_integral,Finset.smul_sum]
  simp only [cellQuadrature,smul_smul]

theorem cellQuadrature_error_rms (u : I → ℝ) (f : ℝ → Ω → E) (ℓ : ℝ) {θ B : ℝ}
    (hθ : 0≤θ)
    (hf : ∀z,IntervalIntegrable (fun t => f t z) volume 0 θ)
    (hm : AEStronglyMeasurable
      (fun p : ℝ × Ω => f p.1 p.2-interpolation u (fun i => f (u i) p.2) p.1)
      ((volume.restrict (Ioc 0 θ)).prod ν))
    (hi : ∀t∈Ioc 0 θ,Integrable
      (fun z => ‖f t z-interpolation u (fun i => f (u i) z) t‖^2) ν)
    (hB : ∀t∈Ioc 0 θ,(∫z,‖f t z-interpolation u (fun i => f (u i) z) t‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖ℓ • (∫t in 0..θ,f t z)-cellQuadrature u (fun i => f (u i) z) ℓ θ‖^2) ν ∧
      (∫z,‖ℓ • (∫t in 0..θ,f t z)-cellQuadrature u (fun i => f (u i) z) ℓ θ‖^2 ∂ν)≤ℓ^2*θ^2*B := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 θ)
  have hs : ∀ᵐ t ∂μ,Integrable
      (fun z => ‖f t z-interpolation u (fun i => f (u i) z) t‖^2) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hi t ht
  have hb : ∀ᵐ t ∂μ,(∫z,‖f t z-interpolation u (fun i => f (u i) z) t‖^2 ∂ν)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB t ht
  have hv := RMSIntegral.time_seed_uniform hm hs hb
  have he (z : Ω) : ℓ • (∫t in 0..θ,f t z)-cellQuadrature u (fun i => f (u i) z) ℓ θ=
      ℓ • (∫t,(f t z-interpolation u (fun i => f (u i) z) t) ∂μ) := by
    rw [cellQuadrature_eq_integral,←smul_sub,←intervalIntegral.integral_sub (hf z)
      ((interpolation_continuous u (fun i => f (u i) z)).intervalIntegrable 0 θ),
      intervalIntegral.integral_of_le hθ]
  have hnorm (v : E) : ‖ℓ • v‖^2=ℓ^2*‖v‖^2 := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  simp_rw [he,hnorm]
  refine ⟨hv.1.const_mul _,?_⟩
  rw [integral_const_mul]
  have hμ : μ.real univ=θ := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    change volume.real (Ioc 0 θ)=θ
    rw [Real.volume_real_Ioc_of_le hθ,sub_zero]
  rw [hμ] at hv
  exact (mul_le_mul_of_nonneg_left hv.2 (sq_nonneg ℓ)).trans_eq (by ring)
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.RMSIntegral
open MeasureTheory Set
open scoped BigOperators

variable {I β E : Type*} [Fintype I] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ν : Measure β}

omit [CompleteSpace E] in
lemma norm_weighted_sum_sq (w : I → ℝ) (v : I → E) :
    ‖∑i,w i • v i‖^2≤(∑i,|w i|)*(∑i,|w i| *‖v i‖^2) := by
  have h := norm_sum_le Finset.univ (fun i => w i • v i)
  simp only [norm_smul,Real.norm_eq_abs] at h
  apply (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r:=fun i => |w i| * ‖v i‖) (f:=fun i => |w i|) (g:=fun i => |w i| *‖v i‖^2)
  · exact fun i _ => abs_nonneg _
  · exact fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  · intro index _; exact le_of_eq (by ring)

omit [CompleteSpace E] in
theorem weighted_sum_sq (w : I → ℝ) (f : I → β → E) {B : ℝ}
    (hm : ∀i,AEStronglyMeasurable (f i) ν)
    (hi : ∀i,Integrable (fun z => ‖f i z‖^2) ν)
    (hB : ∀i,(∫z,‖f i z‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖∑i,w i • f i z‖^2) ν ∧
      (∫z,‖∑i,w i • f i z‖^2 ∂ν)≤(∑i,|w i|)^2*B := by
  have hw0 : 0≤∑i,|w i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hs : Integrable (fun z => (∑i,|w i|)*(∑i,|w i| *‖f i z‖^2)) ν := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _ => (hi i).const_mul _)
  have hmeas : AEStronglyMeasurable (fun z => ‖∑i,w i • f i z‖^2) ν := by
    have hh := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun i _ => (hm i).const_smul (w i))).norm.pow 2
    convert hh using 1
    ext z
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]
  have ho : Integrable (fun z => ‖∑i,w i • f i z‖^2) ν :=
    hs.mono' hmeas (Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs,abs_sq] using norm_weighted_sum_sq w (fun i => f i z)))
  refine ⟨ho,(integral_mono ho hs (fun z => norm_weighted_sum_sq w (fun i => f i z))).trans ?_⟩
  rw [integral_const_mul,integral_finsetSum]
  · simp only [integral_const_mul]
    have hh := Finset.sum_le_sum (fun (i : I) (_ : i∈Finset.univ) =>
      mul_le_mul_of_nonneg_left (hB i) (abs_nonneg (w i)))
    have h := mul_le_mul_of_nonneg_left hh hw0
    simpa only [←Finset.sum_mul,pow_two,mul_assoc] using h
  · intro i _
    exact (hi i).const_mul _
end LogConcaveSampling.RMSIntegral

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma taylor_remainder_global {f : ℝ → E} {n : ℕ} (hf : ContDiff ℝ (n+1:ℕ) f)
    (a x : ℝ) :
    f x-taylorWithinEval f n univ a x =
      ∫t in a..x,((x-t)^n/(n.factorial:ℝ)) • iteratedDeriv (n+1) f t := by
  by_cases hax : a=x
  · subst x
    simp
  have hd (k : ℕ) (hk : k≤n+1) (t : ℝ) (ht : t∈uIcc a x) :
      iteratedDerivWithin k f (uIcc a x) t=iteratedDeriv k f t :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hax)
      ((hf.of_le (by exact_mod_cast hk)).contDiffAt) ht
  have he : taylorWithinEval f n (uIcc a x) a x=taylorWithinEval f n univ a x := by
    simp only [taylor_within_apply,iteratedDerivWithin_univ]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hd k (by have := Finset.mem_range.mp hk; omega) a (left_mem_uIcc)]
  rw [←he,taylor_integral_remainder hf.contDiffOn]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [hd _ le_rfl t ht]

lemma taylor_kernel_bound {a x t : ℝ} (hat : a≤t) (htx : t≤x) (n : ℕ) :
    |(x-t)^n/(n.factorial:ℝ)|≤(x-a)^n/(n.factorial:ℝ) := by
  have hn : (0:ℝ)<n.factorial := by positivity
  rw [abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) n) hn.le
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set Polynomial
open scoped BigOperators

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma taylor_scaled_eval (f : ℝ → E) (n : ℕ) (a ℓ t : ℝ) :
    taylorWithinEval f n univ a (a+ℓ*t)=
      ∑k : Fin (n+1),t^(k:ℕ) •
        (((k.val.factorial:ℝ)⁻¹*ℓ^(k:ℕ)) • iteratedDeriv k f a) := by
  rw [taylor_within_apply]
  simp only [iteratedDerivWithin_univ]
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [show a+ℓ*t-a=ℓ*t by ring,mul_pow,smul_smul]
  congr 1
  ring

omit [CompleteSpace E] in
lemma reproduces_cell_taylor (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (f : ℝ → E) (a ℓ t : ℝ) :
    interpolation u (fun i => taylorWithinEval f n univ a (a+ℓ*u i)) t=
      taylorWithinEval f n univ a (a+ℓ*t) := by
  simp_rw [taylor_scaled_eval]
  exact reproduces_vector u hu (n+1) hn _ t

omit [CompleteSpace E] in
lemma interpolation_sub (u : I → ℝ) (f g : I → E) (t : ℝ) :
    interpolation u (fun i => f i-g i) t=interpolation u f t-interpolation u g t := by
  simp [interpolation,smul_sub,Finset.sum_sub_distrib]

omit [CompleteSpace E] in
lemma cell_error_eq (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (f : ℝ → E) (a ℓ t : ℝ) :
    f (a+ℓ*t)-interpolation u (fun i => f (a+ℓ*u i)) t=
      (f (a+ℓ*t)-taylorWithinEval f n univ a (a+ℓ*t))-
        interpolation u (fun i => f (a+ℓ*u i)-taylorWithinEval f n univ a (a+ℓ*u i)) t := by
  rw [interpolation_sub,reproduces_cell_taylor u hu n hn]
  abel
end LogConcaveSampling.Quadrature

end

end

section

noncomputable section
namespace LogConcaveSampling.Quadrature
open MeasureTheory Set
open scoped BigOperators

variable {I Ω E : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ν : Measure Ω}

omit [CompleteSpace E] in
theorem cell_error_rms (u : I → ℝ) (hu : Function.Injective u) (n : ℕ)
    (hn : n+1≤Fintype.card I) (f : ℝ → Ω → E) (a ℓ t : ℝ) {B C : ℝ}
    (hB : 0≤B) (hC : 1≤C) (hc : ∑i,|basis u i t|≤C)
    (hm : ∀s∈insert t (Set.range u),AEStronglyMeasurable
      (fun z => f (a+ℓ*s) z-taylorWithinEval (fun v => f v z) n univ a (a+ℓ*s)) ν)
    (hi : ∀s∈insert t (Set.range u),Integrable
      (fun z => ‖f (a+ℓ*s) z-taylorWithinEval (fun v => f v z) n univ a (a+ℓ*s)‖^2) ν)
    (hR : ∀s∈insert t (Set.range u),(∫z,
      ‖f (a+ℓ*s) z-taylorWithinEval (fun v => f v z) n univ a (a+ℓ*s)‖^2 ∂ν)≤B) :
    Integrable (fun z => ‖f (a+ℓ*t) z-interpolation u (fun i => f (a+ℓ*u i) z) t‖^2) ν ∧
      (∫z,‖f (a+ℓ*t) z-interpolation u (fun i => f (a+ℓ*u i) z) t‖^2 ∂ν)≤4*C^2*B := by
  let R (s : ℝ) (z : Ω) := f (a+ℓ*s) z-taylorWithinEval (fun v => f v z) n univ a (a+ℓ*s)
  have hmt := hm t (mem_insert t _)
  have hmn (i : I) := hm (u i) (mem_insert_of_mem t (mem_range_self i))
  have hit := hi t (mem_insert t _)
  have hin (i : I) := hi (u i) (mem_insert_of_mem t (mem_range_self i))
  have hRn (i : I) := hR (u i) (mem_insert_of_mem t (mem_range_self i))
  have hsum := RMSIntegral.weighted_sum_sq (fun i => basis u i t) (fun i => R (u i)) hmn hin hRn
  have hms : AEStronglyMeasurable (fun z => interpolation u (fun i => R (u i) z) t) ν := by
    have hs := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (hmn i).const_smul (basis u i t))
    convert hs using 1
    ext z
    simp only [interpolation,Finset.sum_apply,Pi.smul_apply,R]
  have hsb : (∫z,‖interpolation u (fun i => R (u i) z) t‖^2 ∂ν)≤C^2*B := by
    apply hsum.2.trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hc 2) hB
  have hs := RMSIntegral.sub_sq_bound hmt hms hit hsum.1 (hR t (mem_insert t _)) hsb
  have he (z : Ω) := cell_error_eq u hu n hn (fun v => f v z) a ℓ t
  simp_rw [he]
  refine ⟨hs.1,hs.2.trans ?_⟩
  have hc2 : 1≤C^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hc2 hB]
end LogConcaveSampling.Quadrature

end

end

end

end OAI
