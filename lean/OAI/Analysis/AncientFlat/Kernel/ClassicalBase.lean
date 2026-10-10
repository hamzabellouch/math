import Mathlib

namespace OAI

noncomputable section
open scoped Topology SchwartzMap FourierTransform ContDiff
open Set Filter MeasureTheory
namespace BiharmonicKernel

lemma gaussian_moment_bound (n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x|^n * Real.exp (-(x^2/2)) ≤ C := by
  refine ⟨max 1 ((2:ℝ)^n * (n.factorial : ℝ)), fun x => ?_⟩
  by_cases hx : |x| ≤ 1
  · apply le_trans _ (le_max_left _ _)
    have he : Real.exp (-(x^2/2)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    exact (mul_le_of_le_one_left (Real.exp_nonneg _)
      (pow_le_one₀ (abs_nonneg x) hx)).trans he
  · have hx1 : 1 ≤ |x| := (lt_of_not_ge hx).le
    have hxx : |x| ≤ x^2 := by nlinarith [sq_abs x]
    have hf : (x^2/2)^n ≤ Real.exp (x^2/2)*(n.factorial : ℝ) :=
      (div_le_iff₀ (show (0:ℝ)<(n.factorial : ℝ) by positivity)).mp
        (Real.pow_div_factorial_le_exp _ (by positivity) n)
    have hfm : (x^2/2)^n * Real.exp (-(x^2/2)) ≤ (n.factorial : ℝ) := by
      calc
        _ ≤ (Real.exp (x^2/2)*(n.factorial : ℝ))*Real.exp (-(x^2/2)) :=
          mul_le_mul_of_nonneg_right hf (Real.exp_nonneg _)
        _ = (n.factorial : ℝ) := by rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    calc
      _ ≤ (x^2)^n * Real.exp (-(x^2/2)) := by gcongr
      _ = (2:ℝ)^n *((x^2/2)^n * Real.exp (-(x^2/2))) := by
        rw [← mul_assoc, ← mul_pow]
        congr 2
        ring
      _ ≤ (2:ℝ)^n * (n.factorial : ℝ) := mul_le_mul_of_nonneg_left hfm (by positivity)
      _ ≤ _ := le_max_right _ _

lemma polynomial_gaussian_bound (p : Polynomial ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x|^k * |p.eval x| * Real.exp (-(x^2/2)) ≤ C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Cp,hp⟩ := hp
    obtain ⟨Cq,hq⟩ := hq
    refine ⟨Cp+Cq, fun x => ?_⟩
    calc
      _ ≤ |x|^k*(|p.eval x|+|q.eval x|)*Real.exp (-(x^2/2)) := by
        rw [Polynomial.eval_add]
        gcongr
        exact abs_add_le _ _
      _ = |x|^k*|p.eval x| *Real.exp (-(x^2/2))+
          |x|^k*|q.eval x| *Real.exp (-(x^2/2)) := by ring
      _ ≤ Cp+Cq := add_le_add (hp x) (hq x)
  | monomial n a =>
    obtain ⟨C,hC⟩ := gaussian_moment_bound (k+n)
    refine ⟨|a| *C, fun x => ?_⟩
    calc
      _ = |a| *(|x|^(k+n)*Real.exp (-(x^2/2))) := by
        simp only [Polynomial.eval_monomial, abs_mul, abs_pow, pow_add]
        ring
      _ ≤ |a| *C := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

def gaussian : SchwartzMap ℝ ℝ where
  toFun x := Real.exp (-(x^2/2))
  smooth' := by fun_prop
  decay' k n := by
    obtain ⟨C,hC⟩ := polynomial_gaussian_bound
      ((Polynomial.hermite n).map (algebraMap ℤ ℝ)) k
    refine ⟨C,fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
      Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
    simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Polynomial.eval_map,
      Polynomial.aeval_def, mul_assoc] using hC x

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
lemma norm_le_quadratic (q : ℝ) (hq : 0 < q) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : V, ‖x‖ ≤ C * (1+‖q*‖x‖^2‖)^k := by
  refine ⟨1,1+q⁻¹,fun x => ?_⟩
  rw [pow_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have he : (1+q⁻¹)*(1+q*‖x‖^2) = 1+‖x‖^2+q*‖x‖^2+q⁻¹ := by
    field_simp
    ring
  rw [he]
  nlinarith [sq_nonneg (‖x‖-1/2), inv_pos.mpr hq, mul_nonneg hq.le (sq_nonneg ‖x‖)]

def multiplier (b : ℝ) (hb : 0 < b) : SchwartzMap V ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    (SchwartzMap.compCLM ℝ
      (g := fun x : V => Real.sqrt (2*b)*‖x‖^2) (by fun_prop)
      (norm_le_quadratic _ (Real.sqrt_pos.mpr (by positivity))) gaussian)

@[simp] lemma multiplier_apply (b : ℝ) (hb : 0 < b) (x : V) :
    multiplier b hb x = (Real.exp (-b*‖x‖^4) : ℂ) := by
  change (Real.exp (-((Real.sqrt (2*b)*‖x‖^2)^2/2)) : ℂ) = _
  congr 2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open Real FourierTransform

def heatKernel (θ : ℝ) (hθ : 0 < θ) : SchwartzMap V ℂ :=
  𝓕⁻ (multiplier (V := V) ((2*Real.pi)^4*θ) (by positivity))

lemma fourier_heatKernel (θ : ℝ) (hθ : 0 < θ) :
    𝓕 (heatKernel (V := V) θ hθ) = multiplier ((2*Real.pi)^4*θ) (by positivity) := by
  exact fourier_fourierInv_eq (multiplier (V := V) ((2*Real.pi)^4*θ) (by positivity))

lemma integral_heatKernel (θ : ℝ) (hθ : 0 < θ) :
    ∫ x : V, heatKernel θ hθ x = 1 := by
  have h := congrArg (fun f : SchwartzMap V ℂ => f 0) (fourier_heatKernel (V := V) θ hθ)
  simpa [SchwartzMap.fourier_coe, Real.fourier_eq, multiplier_apply] using h

lemma heatKernel_decay (θ : ℝ) (hθ : 0 < θ) (N j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V,
      ‖iteratedFDeriv ℝ j (heatKernel (V := V) θ hθ) x‖ ≤ C/(1+‖x‖)^N := by
  let C := 2^N * (Finset.Iic (N,j)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)
    (heatKernel (V := V) θ hθ)
  refine ⟨C,by positivity,fun x => ?_⟩
  apply (le_div_iff₀ (by positivity)).mpr
  rw [mul_comm]
  exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N,j))
    le_rfl le_rfl (heatKernel (V := V) θ hθ) x

lemma heatKernel_invariant (θ : ℝ) (hθ : 0 < θ) (A : V ≃ₗᵢ[ℝ] V) (x : V) :
    heatKernel θ hθ (A x) = heatKernel θ hθ x := by
  have hm : (fun y : V => multiplier ((2*Real.pi)^4*θ) (by positivity) (A y)) =
      (multiplier ((2*Real.pi)^4*θ) (by positivity) : V → ℂ) := by
    ext y
    simp
  unfold heatKernel
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    ← map_neg A, ← Real.fourier_comp_linearIsometry, Function.comp_def, hm,
    ← Real.fourierInv_eq_fourier_neg]

open scoped RealInnerProductSpace Real

lemma fourierInv_comp_smul (f : V → ℂ) (r : ℝ) (hr : 0 < r) (x : V) :
    𝓕⁻ (fun ξ => f (r • ξ)) x = (r ^ Module.finrank ℝ V)⁻¹ • 𝓕⁻ f (r⁻¹ • x) := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  convert Measure.integral_comp_smul_of_nonneg volume
    (fun ξ : V => Real.fourierChar ⟪ξ,r⁻¹ • x⟫ • f ξ) r (hR := hr.le) using 1
  congr 1
  ext ξ
  simp only [real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

lemma heatKernel_scaling (θ : ℝ) (hθ : 0 < θ) (r : ℝ) (hr : 0 < r) (x : V) :
    heatKernel (r^4*θ) (by positivity) x =
      (r ^ Module.finrank ℝ V)⁻¹ • heatKernel θ hθ (r⁻¹ • x) := by
  have hm : (multiplier (V := V) ((2*Real.pi)^4*(r^4*θ)) (by positivity) : V → ℂ) =
      fun ξ => multiplier ((2*Real.pi)^4*θ) (by positivity) (r • ξ) := by
    ext ξ
    simp only [multiplier_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    congr 2
    ring
  simp only [heatKernel, SchwartzMap.fourierInv_coe, hm]
  exact fourierInv_comp_smul _ _ hr _

lemma heatKernel_deriv_scaling (θ : ℝ) (hθ : 0 < θ) (r : ℝ) (hr : 0 < r)
    (j : ℕ) (x : V) :
    iteratedFDeriv ℝ j (heatKernel (V := V) (r^4*θ) (by positivity)) x =
      ((r ^ Module.finrank ℝ V)⁻¹ * (r⁻¹)^j) •
        iteratedFDeriv ℝ j (heatKernel θ hθ) (r⁻¹ • x) := by
  have he : (heatKernel (V := V) (r^4*θ) (by positivity) : V → ℂ) =
      fun y => (r ^ Module.finrank ℝ V)⁻¹ • heatKernel θ hθ (r⁻¹ • y) := by
    ext y
    exact heatKernel_scaling θ hθ r hr y
  rw [he, iteratedFDeriv_const_smul_apply']
  · rw [iteratedFDeriv_comp_const_smul r⁻¹ ((heatKernel θ hθ).smooth j), smul_smul]
  · exact (((heatKernel θ hθ).smooth j).comp (by fun_prop)).contDiffAt

lemma heatKernel_scaled_decay (N j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, ∀ hr : 0 < r, ∀ x : V,
      ‖iteratedFDeriv ℝ j (heatKernel (V := V) (r^4) (by positivity)) x‖ ≤
        C / r^(Module.finrank ℝ V+j) / (1+‖x‖/r)^N := by
  obtain ⟨C,hC,hdec⟩ := heatKernel_decay (V := V) 1 zero_lt_one N j
  refine ⟨C,hC,fun r hr x => ?_⟩
  have hid := heatKernel_deriv_scaling (V := V) 1 zero_lt_one r hr j x
  simp only [mul_one] at hid
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hd := hdec (r⁻¹ • x)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at hd
  calc
    _ ≤ ((r ^ Module.finrank ℝ V)⁻¹ * r⁻¹^j) * (C/(1+r⁻¹*‖x‖)^N) := by gcongr
    _ = _ := by rw [pow_add, inv_pow]; field_simp

def symbol (x : V) : ℝ := (2*Real.pi)^4 * ‖x‖^4

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma symbol_nonneg (x : V) : 0 ≤ symbol x := by unfold symbol; positivity

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma symbol_temperate : Function.HasTemperateGrowth (symbol (V := V)) := by
  have he : symbol (V := V) = fun x : V => (2*Real.pi)^4 * (‖x‖^2)^2 := by
    ext x
    unfold symbol
    ring
  rw [he]
  fun_prop

def kernel (t : ℝ) (x : V) : ℂ :=
  𝓕⁻ (fun ξ : V => (Real.exp (-t*symbol ξ) : ℂ)) x

lemma heatKernel_eq_kernel (t : ℝ) (ht : 0 < t) :
    (heatKernel (V := V) t ht : V → ℂ) = kernel t := by
  simp only [heatKernel, SchwartzMap.fourierInv_coe]
  congr 1
  ext ξ
  simp only [multiplier_apply, symbol]
  congr 2
  ring

lemma kernel_hasDerivAt (t : ℝ) (ht : 0 < t) (x : V) :
    HasDerivAt (fun s => kernel s x)
      (𝓕⁻ (fun ξ : V => (-symbol ξ) • (Real.exp (-t*symbol ξ) : ℂ)) x) t := by
  let F := fun s : ℝ => fun ξ : V => Real.fourierChar ⟪ξ,x⟫ • (Real.exp (-s*symbol ξ) : ℂ)
  let F' := fun s : ℝ => fun ξ : V =>
    Real.fourierChar ⟪ξ,x⟫ • ((-symbol ξ) • (Real.exp (-s*symbol ξ) : ℂ))
  let W := SchwartzMap.smulLeftCLM ℂ (symbol (V := V))
    (multiplier (V := V) ((2*Real.pi)^4*(t/2)) (by positivity))
  have hW (ξ : V) : ‖W ξ‖ = symbol ξ * Real.exp (-(t/2)*symbol ξ) := by
    simp only [W, SchwartzMap.smulLeftCLM_apply_apply symbol_temperate,
      multiplier_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (symbol_nonneg ξ), abs_of_pos (Real.exp_pos _)]
    congr 2
    unfold symbol
    ring
  have htemp : Continuous (symbol (V := V)) := symbol_temperate.1.continuous
  have hFi : Integrable (F t) := by
    have hm : (fun ξ => (Real.exp (-t*symbol ξ) : ℂ)) =
        (multiplier (V := V) ((2*Real.pi)^4*t) (by positivity) : V → ℂ) := by
      ext ξ
      rw [multiplier_apply]
      congr 2
      unfold symbol
      ring
    have hi : Integrable (multiplier (V := V) ((2*Real.pi)^4*t) (by positivity)) volume :=
      (multiplier (V := V) ((2*Real.pi)^4*t) (by positivity)).integrable
    convert (Real.fourierIntegral_convergent_iff (-x)).mpr hi using 1
    ext ξ
    rw [← congrFun hm ξ]
    simp only [F, inner_neg_right, neg_neg]
  have hder : ∀ ξ : V, ∀ s : ℝ, HasDerivAt (fun u => F u ξ) (F' s ξ) s := by
    intro ξ s
    have h : HasDerivAt (fun u : ℝ => (Real.exp (-u*symbol ξ) : ℂ))
        ((-symbol ξ) • (Real.exp (-s*symbol ξ) : ℂ)) s := by
      convert (((hasDerivAt_id s).neg.mul_const (symbol ξ)).exp).ofReal_comp using 1 <;>
        simp [Complex.real_smul, mul_comm]
    simpa only [F, F'] using h.fun_const_smul (Real.fourierChar ⟪ξ,x⟫)
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun ξ : V => ‖W ξ‖)
    (s := Ioi (t/2)) (Ioi_mem_nhds (show t/2 < t by linarith))
    (Filter.Eventually.of_forall (fun s =>
      (show Continuous (F s) by dsimp [F]; fun_prop).aestronglyMeasurable)) hFi
    (show AEStronglyMeasurable (F' t) volume from
      (show Continuous (F' t) by dsimp [F']; fun_prop).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun ξ s hs => by
      change ‖Real.fourierChar ⟪ξ,x⟫ • ((-symbol ξ) •
        (Real.exp (-s*symbol ξ) : ℂ))‖ ≤ ‖W ξ‖
      simp only [Circle.norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_neg, abs_of_nonneg (symbol_nonneg ξ), abs_of_pos (Real.exp_pos _), hW]
      apply mul_le_mul_of_nonneg_left _ (symbol_nonneg ξ)
      apply Real.exp_le_exp.mpr
      have hs' : t/2 ≤ s := hs.le
      nlinarith [symbol_nonneg ξ])) W.integrable.norm
    (Filter.Eventually.of_forall (fun ξ s _ => hder ξ s))
  simpa only [kernel, Real.fourierInv_eq, F, F'] using hh.2

open Laplacian

lemma biharmonic_eq_fourierMultiplier (f : SchwartzMap V ℂ) :
    Δ (Δ f) = SchwartzMap.fourierMultiplierCLM ℂ (symbol (V := V)) f := by
  have hg : Function.HasTemperateGrowth (fun ξ : V => ‖ξ‖^2) := by fun_prop
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM (Δ f),
    SchwartzMap.laplacian_eq_fourierMultiplierCLM f, map_smul, smul_smul,
    SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply hg hg]
  have he : symbol (V := V) =
      ((-(2*Real.pi)^2)* (-(2*Real.pi)^2)) •
        ((fun ξ : V => ‖ξ‖^2) * (fun ξ : V => ‖ξ‖^2)) := by
    ext ξ
    simp only [symbol, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  rw [he, SchwartzMap.fourierMultiplierCLM_smul (hg.mul hg)]
  rfl

lemma kernel_heat_equation (t : ℝ) (ht : 0 < t) (x : V) :
    HasDerivAt (fun s => kernel s x) (-((Δ (Δ (heatKernel (V := V) t ht))) x)) t := by
  have hd := kernel_hasDerivAt t ht x
  have he : (fun ξ : V => (-symbol ξ) • (Real.exp (-t*symbol ξ) : ℂ)) =
      ((-SchwartzMap.smulLeftCLM ℂ (symbol (V := V))
        (multiplier (V := V) ((2*Real.pi)^4*t) (by positivity)) : SchwartzMap V ℂ) : V → ℂ) := by
    ext ξ
    simp only [neg_apply, SchwartzMap.smulLeftCLM_apply_apply symbol_temperate,
      multiplier_apply, neg_smul]
    congr 2
    congr 1
    unfold symbol
    ring_nf
  rw [he, ← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_neg] at hd
  rw [biharmonic_eq_fourierMultiplier, SchwartzMap.fourierMultiplierCLM_apply,
    fourier_heatKernel]
  exact hd

lemma kernel_eq_scaled (t : ℝ) (ht : 0 < t) (x : V) :
    kernel t x = ((Real.sqrt (Real.sqrt t)) ^ Module.finrank ℝ V)⁻¹ •
      heatKernel 1 zero_lt_one ((Real.sqrt (Real.sqrt t))⁻¹ • x) := by
  have hr : 0 < Real.sqrt (Real.sqrt t) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ht)
  have he : (Real.sqrt (Real.sqrt t))^4 = t := by
    calc
      _ = ((Real.sqrt (Real.sqrt t))^2)^2 := by ring
      _ = t := by rw [Real.sq_sqrt (Real.sqrt_nonneg t), Real.sq_sqrt ht.le]
  have hs := heatKernel_scaling (V := V) 1 zero_lt_one _ hr x
  simp only [mul_one, he] at hs
  rw [← heatKernel_eq_kernel t ht]
  exact hs

lemma kernel_contDiffAt (q : ℝ × V) (hq : 0 < q.1) :
    ContDiffAt ℝ ∞ (fun p : ℝ × V => kernel p.1 p.2) q := by
  have hr : ContDiffAt ℝ ∞ (fun p : ℝ × V => Real.sqrt (Real.sqrt p.1)) q :=
    (contDiffAt_fst.sqrt (ne_of_gt hq)).sqrt (ne_of_gt (Real.sqrt_pos.mpr hq))
  have hpos : 0 < Real.sqrt (Real.sqrt q.1) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hq)
  have hs : ContDiffAt ℝ ∞ (fun p : ℝ × V =>
      ((Real.sqrt (Real.sqrt p.1)) ^ Module.finrank ℝ V)⁻¹ •
        heatKernel 1 zero_lt_one ((Real.sqrt (Real.sqrt p.1))⁻¹ • p.2)) q :=
    ((hr.pow _).inv (pow_ne_zero _ hpos.ne')).smul
      (((heatKernel (V := V) 1 zero_lt_one).smooth ⊤).contDiffAt.comp q
        ((hr.inv hpos.ne').smul contDiffAt_snd))
  apply hs.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds hq)] with p hp
  exact kernel_eq_scaled _ hp _

lemma integral_norm_heatKernel (t : ℝ) (ht : 0 < t) :
    ∫ x : V, ‖heatKernel t ht x‖ = ∫ x : V, ‖heatKernel 1 zero_lt_one x‖ := by
  let r := Real.sqrt (Real.sqrt t)
  have hr : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ht)
  have he : (fun x : V => ‖heatKernel t ht x‖) =
      fun x => (r ^ Module.finrank ℝ V)⁻¹ * ‖heatKernel 1 zero_lt_one (r⁻¹ • x)‖ := by
    ext x
    rw [congrFun (heatKernel_eq_kernel t ht) x, kernel_eq_scaled t ht x,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [he, integral_const_mul,
    MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x : V => ‖heatKernel 1 zero_lt_one x‖) hr.le]
  simp [hr.ne']

end BiharmonicKernel

open scoped Topology ZeroAtInfty
open Set Filter MeasureTheory

namespace C0Convolution

variable {V : Type*} [NormedAddCommGroup V]

def translate (y : V) (f : C₀(V, ℂ)) : C₀(V, ℂ) :=
  f.comp (Homeomorph.subRight y).toCocompactMap

@[simp] lemma translate_apply (y : V) (f : C₀(V, ℂ)) (x : V) :
    translate y f x = f (x-y) := rfl

@[simp] lemma translate_zero (f : C₀(V, ℂ)) : translate 0 f = f := by
  ext x
  simp

@[simp] lemma translate_add (y : V) (f g : C₀(V, ℂ)) :
    translate y (f+g) = translate y f + translate y g := rfl

@[simp] lemma translate_smul (y : V) (c : ℂ) (f : C₀(V, ℂ)) :
    translate y (c • f) = c • translate y f := rfl

lemma norm_le_iff (f : C₀(V, ℂ)) {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ x : V, ‖f x‖ ≤ C :=
  BoundedContinuousFunction.norm_le hC

lemma apply_norm_le (f : C₀(V, ℂ)) (x : V) : ‖f x‖ ≤ ‖f‖ :=
  f.toBCF.norm_coe_le_norm x

@[simp] lemma norm_translate (y : V) (f : C₀(V, ℂ)) : ‖translate y f‖ = ‖f‖ := by
  apply le_antisymm
  · exact (norm_le_iff _ (norm_nonneg _)).mpr (fun x => apply_norm_le f (x-y))
  · apply (norm_le_iff _ (norm_nonneg _)).mpr
    intro x
    simpa using apply_norm_le (translate y f) (x+y)

lemma continuous_translate (f : C₀(V, ℂ)) : Continuous (fun y : V => translate y f) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hf⟩ := Metric.uniformContinuous_iff.mp (ZeroAtInftyContinuousMap.uniformContinuous f) (ε/2) (by positivity)
  refine ⟨δ,hδ,fun z hz => ?_⟩
  apply lt_of_le_of_lt _ (show ε/2 < ε by linarith)
  change dist (translate z f).toBCF (translate y f).toBCF ≤ ε/2
  apply (BoundedContinuousFunction.dist_le (by positivity)).mpr
  intro x
  change dist (f (x-z)) (f (x-y)) ≤ ε/2
  apply (hf ?_).le
  simpa only [dist_sub_left] using hz

def eval (x : V) : C₀(V, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by simpa using apply_norm_le f x)

@[simp] lemma eval_apply (x : V) (f : C₀(V, ℂ)) : eval x f = f x := rfl

variable [MeasureSpace V] [BorelSpace V] [SecondCountableTopology V]

lemma integrable_translated (k : V → ℂ) (hk : Integrable k) (f : C₀(V, ℂ)) :
    Integrable (fun y : V => k y • translate y f) := by
  apply (hk.norm.mul_const ‖f‖).mono'
  · exact hk.aestronglyMeasurable.smul (continuous_translate f).aestronglyMeasurable
  · filter_upwards with y
    simp only [norm_smul, norm_translate, le_refl]

def convolve (k : V → ℂ) (f : C₀(V, ℂ)) : C₀(V, ℂ) :=
  ∫ y : V, k y • translate y f

lemma convolve_apply (k : V → ℂ) (hk : Integrable k) (f : C₀(V, ℂ)) (x : V) :
    convolve k f x = ∫ y : V, k y * f (x-y) := by
  have h := (eval x).integral_comp_comm (integrable_translated k hk f)
  simpa [convolve] using h.symm

omit [BorelSpace V] [SecondCountableTopology V] in
lemma norm_convolve_le (k : V → ℂ) (f : C₀(V, ℂ)) :
    ‖convolve k f‖ ≤ (∫ y : V, ‖k y‖) * ‖f‖ := by
  calc
    _ ≤ ∫ y : V, ‖k y • translate y f‖ := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_smul, norm_translate, integral_mul_const]

lemma convolve_add (k : V → ℂ) (hk : Integrable k) (f g : C₀(V, ℂ)) :
    convolve k (f+g) = convolve k f + convolve k g := by
  have he (y : V) : k y • translate y (f+g) =
      k y • translate y f + k y • translate y g := by
    ext x
    exact mul_add (k y) (f (x-y)) (g (x-y))
  simp only [convolve, he]
  exact integral_add (integrable_translated k hk f) (integrable_translated k hk g)

omit [BorelSpace V] [SecondCountableTopology V] in
lemma convolve_smul (k : V → ℂ) (c : ℂ) (f : C₀(V, ℂ)) :
    convolve k (c • f) = c • convolve k f := by
  simp only [convolve, translate_smul, smul_comm (k _) c, integral_smul]

def convolveCLM (k : V → ℂ) (hk : Integrable k) : C₀(V, ℂ) →L[ℂ] C₀(V, ℂ) :=
  LinearMap.mkContinuous
    { toFun := convolve k
      map_add' := convolve_add k hk
      map_smul' := convolve_smul k }
    (∫ y : V, ‖k y‖) (norm_convolve_le k)

lemma norm_convolveCLM_le (k : V → ℂ) (hk : Integrable k) :
    ‖convolveCLM k hk‖ ≤ ∫ y : V, ‖k y‖ := by
  exact LinearMap.mkContinuous_norm_le _ (integral_nonneg (fun _ => norm_nonneg _)) _

variable [NormedSpace ℝ V]

lemma integrable_scaled_translated (k : V → ℂ) (hk : Integrable k)
    (r : ℝ) (f : C₀(V, ℂ)) :
    Integrable (fun y : V => k y • translate (r • y) f) := by
  apply (hk.norm.mul_const ‖f‖).mono'
  · exact hk.aestronglyMeasurable.smul
      ((continuous_translate f).comp (continuous_const.smul continuous_id)).aestronglyMeasurable
  · filter_upwards with y
    simp only [norm_smul, norm_translate, le_refl]

def scaleConvolve (k : V → ℂ) (r : ℝ) (f : C₀(V, ℂ)) : C₀(V, ℂ) :=
  ∫ y : V, k y • translate (r • y) f

lemma continuous_scaleConvolve (k : V → ℂ) (hk : Integrable k) (f : C₀(V, ℂ)) :
    Continuous (fun r : ℝ => scaleConvolve k r f) := by
  apply continuous_of_dominated (bound := fun y => ‖k y‖ * ‖f‖)
  · exact fun r => (integrable_scaled_translated k hk r f).aestronglyMeasurable
  · intro r
    filter_upwards with y
    simp only [norm_smul, norm_translate, le_refl]
  · exact hk.norm.mul_const ‖f‖
  · filter_upwards with y
    exact (continuous_const : Continuous (fun _ : ℝ => k y)).smul
      ((continuous_translate f).comp
        (continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => y))))

omit [BorelSpace V] [SecondCountableTopology V] in
lemma scaleConvolve_zero (k : V → ℂ) (f : C₀(V, ℂ)) :
    scaleConvolve k 0 f = (∫ y : V, k y) • f := by
  simp only [scaleConvolve, zero_smul, translate_zero, integral_smul_const]

lemma scaleConvolve_tendsto (k : V → ℂ) (hk : Integrable k)
    (hmass : ∫ y : V, k y = 1) (f : C₀(V, ℂ)) :
    Tendsto (fun r : ℝ => scaleConvolve k r f) (𝓝 0) (𝓝 f) := by
  simpa only [scaleConvolve_zero, hmass, one_smul] using
    (continuous_scaleConvolve k hk f).tendsto 0

variable [FiniteDimensional ℝ V] [Measure.IsAddHaarMeasure (volume : Measure V)]

omit [SecondCountableTopology V] in
lemma convolve_scaled (k : V → ℂ) (r : ℝ) (hr : 0 < r) (f : C₀(V, ℂ)) :
    convolve (fun y : V => (r ^ Module.finrank ℝ V)⁻¹ • k (r⁻¹ • y)) f =
      scaleConvolve k r f := by
  have he (y : V) :
      ((r ^ Module.finrank ℝ V)⁻¹ • k (r⁻¹ • y)) • translate y f =
      (r ^ Module.finrank ℝ V)⁻¹ •
        (k (r⁻¹ • y) • translate (r • (r⁻¹ • y)) f) := by
    rw [smul_inv_smul₀ hr.ne']
    ext x
    exact smul_mul_assoc _ _ _
  simp only [convolve, he, integral_smul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume
    (fun y : V => k y • translate (r • y) f) hr.le]
  rw [inv_smul_smul₀ (pow_ne_zero _ hr.ne')]
  rfl

open scoped Convolution

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Measure.IsAddHaarMeasure (volume : Measure V)] in
lemma convolve_coe (k : V → ℂ) (hk : Integrable k) (f : C₀(V, ℂ)) :
    (convolve k f : V → ℂ) = k ⋆[ContinuousLinearMap.mul ℂ ℂ] (f : V → ℂ) := by
  ext x
  exact convolve_apply k hk f x

lemma convolve_assoc (k l : V → ℂ) (hk : Integrable k) (hl : Integrable l)
    (hkc : Continuous k) (hlc : Continuous l) (f : C₀(V, ℂ)) :
    convolve (k ⋆[ContinuousLinearMap.mul ℂ ℂ] l) f = convolve k (convolve l f) := by
  apply DFunLike.coe_injective
  rw [convolve_coe _ (hk.integrable_convolution _ hl) f,
    convolve_coe k hk, convolve_coe l hl]
  ext x
  apply convolution_assoc' (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ) (fun _ _ _ => mul_assoc _ _ _)
    (hk.ae_convolution_exists _ hl)
  · filter_upwards with z
    change Integrable (fun y => l y * f (z-y))
    exact (eval z).integrable_comp (integrable_translated l hl f)
  · apply ((hk.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hl).norm.mul_const ‖f‖).mono'
    · exact (show Continuous (fun p : V × V => k p.2 * (l (p.1-p.2) * f (x-p.1))) by
        fun_prop).aestronglyMeasurable
    · filter_upwards with p
      simp only [Function.uncurry, ContinuousLinearMap.mul_apply', norm_mul]
      calc
        _ = (‖k p.2‖ * ‖l (p.1-p.2)‖) * ‖f (x-p.1)‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (apply_norm_le f _) (by positivity)

end C0Convolution

namespace BiharmonicKernel
open scoped FourierTransform ZeroAtInfty
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma heatKernel_semigroup (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (heatKernel (V := V) s hs) (heatKernel t ht) =
        heatKernel (s+t) (by positivity) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap V ℂ)).injective
  ext ξ
  simp only [FourierTransform.fourierEquiv_apply, SchwartzMap.fourier_convolution,
    fourier_heatKernel, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply', multiplier_apply]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

def evolution (t : ℝ) (f : C₀(V, ℂ)) : C₀(V, ℂ) :=
  C0Convolution.scaleConvolve (heatKernel 1 zero_lt_one)
    (Real.sqrt (Real.sqrt t)) f

lemma evolution_zero (f : C₀(V, ℂ)) : evolution 0 f = f := by
  simp only [evolution, Real.sqrt_zero, C0Convolution.scaleConvolve_zero,
    integral_heatKernel, one_smul]

lemma evolution_continuous (f : C₀(V, ℂ)) : Continuous (fun t : ℝ => evolution t f) := by
  exact (C0Convolution.continuous_scaleConvolve
    (heatKernel 1 zero_lt_one) (heatKernel (V := V) 1 zero_lt_one).integrable f).comp
      (Real.continuous_sqrt.comp Real.continuous_sqrt)

lemma evolution_initial_trace (f : C₀(V, ℂ)) :
    Tendsto (fun t : ℝ => evolution t f) (𝓝[>] 0) (𝓝 f) := by
  simpa only [ContinuousWithinAt, evolution_zero] using ((evolution_continuous f).continuousAt (x := 0)).continuousWithinAt (s := Ioi 0)

lemma evolution_eq_convolve (t : ℝ) (ht : 0 < t) (f : C₀(V, ℂ)) :
    evolution t f = C0Convolution.convolve (heatKernel t ht) f := by
  have he : (heatKernel (V := V) t ht : V → ℂ) =
      fun x => ((Real.sqrt (Real.sqrt t)) ^ Module.finrank ℝ V)⁻¹ •
        heatKernel 1 zero_lt_one ((Real.sqrt (Real.sqrt t))⁻¹ • x) := by
    ext x
    rw [congrFun (heatKernel_eq_kernel t ht) x, kernel_eq_scaled t ht x]
  rw [he, C0Convolution.convolve_scaled _ _
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ht))]
  rfl

lemma evolution_apply (t : ℝ) (ht : 0 < t) (f : C₀(V, ℂ)) (x : V) :
    evolution t f x = ∫ y : V, heatKernel t ht y * f (x-y) := by
  rw [evolution_eq_convolve t ht f,
    C0Convolution.convolve_apply _ (heatKernel t ht).integrable]

lemma evolution_norm_le (t : ℝ) (ht : 0 < t) (f : C₀(V, ℂ)) :
    ‖evolution t f‖ ≤ (∫ x : V, ‖heatKernel 1 zero_lt_one x‖) * ‖f‖ := by
  rw [evolution_eq_convolve t ht f]
  simpa only [integral_norm_heatKernel] using
    C0Convolution.norm_convolve_le (heatKernel t ht) f

open scoped Convolution
lemma evolution_semigroup (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (f : C₀(V, ℂ)) :
    evolution (s+t) f = evolution s (evolution t f) := by
  rw [evolution_eq_convolve _ (add_pos hs ht), evolution_eq_convolve s hs,
    evolution_eq_convolve t ht,
    ← C0Convolution.convolve_assoc _ _ (heatKernel s hs).integrable
      (heatKernel t ht).integrable (heatKernel s hs).continuous (heatKernel t ht).continuous]
  congr 1
  ext x
  have he := congrArg (fun h : SchwartzMap V ℂ => h x) (heatKernel_semigroup s t hs ht)
  rw [SchwartzMap.convolution_apply] at he
  exact he.symm

end BiharmonicKernel

open scoped SchwartzMap Topology ZeroAtInfty Convolution ContDiff BoundedContinuousFunction
open Set Filter MeasureTheory

namespace SchwartzConvolution
section ShiftedMajorant

universe u

variable {V E F A : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma shifted_majorant (g : SchwartzMap V E) (x₀ : V) :
    ∃ b : V → ℝ, Integrable b ∧ ∀ x ∈ Metric.ball x₀ 1, ∀ y,
      ‖g (x-y)‖ ≤ b y := by
  let N := Module.finrank ℝ V + 1
  let C := 2^N * (Finset.Iic (N,0)).sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) g
  have hC : 0 ≤ C := by positivity
  have hdec (z : V) : (1+‖z‖)^N * ‖g z‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N,0))
        le_rfl le_rfl g z
  refine ⟨fun y => (2^N*C)/(1+‖x₀-y‖)^N, ?_, ?_⟩
  · have hi : Integrable (fun z : V => (1+‖z‖) ^ (-(N : ℝ))) :=
      integrable_one_add_norm (by dsimp [N]; norm_num)
    simpa only [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+‖x₀-_‖),
      Real.rpow_natCast, div_eq_mul_inv] using (hi.comp_sub_left x₀).const_mul (2^N*C)
  · intro x hx y
    have hd : ‖x₀-x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hx
    have hn : ‖x₀-y‖ ≤ ‖x₀-x‖ + ‖x-y‖ := by simpa only [sub_add_sub_cancel] using norm_add_le (x₀-x) (x-y)
    have hs : 1+‖x₀-y‖ ≤ 2*(1+‖x-y‖) := by nlinarith [norm_nonneg (x-y)]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      ‖g (x-y)‖ * (1+‖x₀-y‖)^N ≤ ‖g (x-y)‖ * (2*(1+‖x-y‖))^N := by gcongr
      _ = 2^N * ((1+‖x-y‖)^N * ‖g (x-y)‖) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdec (x-y)) (by positivity)

variable [NormedAddCommGroup A] [NormedSpace ℝ A]

lemma integrable_integrand (L : A →L[ℝ] E →L[ℝ] F)
    (f : V →ᵇ A) (g : SchwartzMap V E) (x : V) :
    Integrable (fun y => L (f y) (g (x-y))) := by
  refine ((g.integrable.norm.comp_sub_left x).const_mul (‖L‖*‖f‖)).mono'
    (f.continuous.aestronglyMeasurable.convolution_integrand_snd L
      g.continuous.aestronglyMeasurable x) (Eventually.of_forall fun y => ?_)
  exact (L.le_opNorm₂ (f y) (g (x-y))).trans (by
    gcongr
    exact f.norm_coe_le_norm y)

lemma hasFDerivAt_convolution (L : A →L[ℝ] E →L[ℝ] F)
    (f : V →ᵇ A) (g : SchwartzMap V E) (x₀ : V) :
    HasFDerivAt (f ⋆[L] g)
      ((f ⋆[L.precompR V] SchwartzMap.fderivCLM ℝ V E g) x₀) x₀ := by
  let g' := SchwartzMap.fderivCLM ℝ V E g
  obtain ⟨b, hb, hbound⟩ := shifted_majorant g' x₀
  have hderiv (x y : V) : HasFDerivAt (fun x => g (x-y)) (g' (x-y)) x := by
    simpa [g', SchwartzMap.fderivCLM_apply, Function.comp_def, Pi.sub_apply] using
      (g.hasFDerivAt (x-y)).comp x ((hasFDerivAt_id x).sub (hasFDerivAt_const y x))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds x₀ zero_lt_one)
  · exact Eventually.of_forall fun x => (integrable_integrand L f g x).aestronglyMeasurable
  · exact integrable_integrand L f g x₀
  · exact (integrable_integrand (L.precompR V) f g' x₀).aestronglyMeasurable
  · filter_upwards with y x hx
    change ‖(L (f y)).comp (g' (x-y))‖ ≤ _
    calc
      ‖(L (f y)).comp (g' (x-y))‖ ≤ ‖L (f y)‖ * ‖g' (x-y)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖L‖ * ‖f‖) * ‖g' (x-y)‖ := by
        gcongr
        exact (L.le_opNorm (f y)).trans (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg L))
      _ ≤ (‖L‖ * ‖f‖) * b y := mul_le_mul_of_nonneg_left (hbound x hx y) (by positivity)
  · exact hb.const_mul (‖L‖ * ‖f‖)
  · filter_upwards with y x _
    exact (L (f y)).hasFDerivAt.comp x (hderiv x y)

lemma contDiff_convolution_nat (n : ℕ) (L : A →L[ℝ] E →L[ℝ] F)
    (f : V →ᵇ A) (g : SchwartzMap V E) :
    ContDiff ℝ n (f ⋆[L] g) := by
  induction n generalizing E F with
  | zero =>
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_convolution L f g x).continuousAt
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
      exact ⟨f ⋆[L.precompR V] SchwartzMap.fderivCLM ℝ V E g,
        ih (L.precompR V) (SchwartzMap.fderivCLM ℝ V E g), hasFDerivAt_convolution L f g⟩

lemma contDiff_convolution (L : A →L[ℝ] E →L[ℝ] F)
    (f : V →ᵇ A) (g : SchwartzMap V E) :
    ContDiff ℝ ∞ (f ⋆[L] g) :=
  contDiff_infty.mpr fun n => contDiff_convolution_nat n L f g

lemma fderiv_convolution (L : A →L[ℝ] E →L[ℝ] F)
    (f : V →ᵇ A) (g : SchwartzMap V E) :
    fderiv ℝ (f ⋆[L] g) = f ⋆[L.precompR V] SchwartzMap.fderivCLM ℝ V E g := by
  funext x
  exact (hasFDerivAt_convolution L f g x).fderiv

lemma fderiv_convolution_apply (L : A →L[ℝ] E →L[ℝ] F)
    (f : V →ᵇ A) (g : SchwartzMap V E) (x v : V) :
    fderiv ℝ (f ⋆[L] g) x v = ∫ y, L (f y) (fderiv ℝ g (x-y) v) := by
  rw [fderiv_convolution, MeasureTheory.convolution_def,
    ContinuousLinearMap.integral_apply (integrable_integrand (L.precompR V) f
      (SchwartzMap.fderivCLM ℝ V E g) x)]
  rfl

lemma second_fderiv_convolution_apply (L : A →L[ℝ] E →L[ℝ] F)
    (f : V →ᵇ A) (g : SchwartzMap V E) (x v w : V) :
    fderiv ℝ (fderiv ℝ (f ⋆[L] g)) x v w =
      ∫ y, L (f y) (fderiv ℝ (fderiv ℝ g) (x-y) v w) := by
  rw [fderiv_convolution, fderiv_convolution_apply]
  rw [ContinuousLinearMap.integral_apply]
  · rfl
  · exact integrable_integrand (L.precompR V) f
      (SchwartzMap.evalCLM ℝ V (V →L[ℝ] E) v
        (SchwartzMap.fderivCLM ℝ V (V →L[ℝ] E) (SchwartzMap.fderivCLM ℝ V E g))) x

end ShiftedMajorant

open scoped Laplacian
universe u
variable {V E F A : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

lemma laplacian_convolution (L : A →L[ℝ] E →L[ℝ] F)
    (f : V →ᵇ A) (g : SchwartzMap V E) :
    Δ (f ⋆[L] g) = f ⋆[L] (Δ g : SchwartzMap V E) := by
  funext x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    second_fderiv_convolution_apply]
  rw [MeasureTheory.convolution_def]
  simp_rw [SchwartzMap.laplacian_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_sum]
  rw [integral_finsetSum]
  · rfl
  · intro i _
    exact integrable_integrand L f
      (SchwartzMap.evalCLM ℝ V E ((stdOrthonormalBasis ℝ V) i)
        (SchwartzMap.evalCLM ℝ V (V →L[ℝ] E) ((stdOrthonormalBasis ℝ V) i)
          (SchwartzMap.fderivCLM ℝ V (V →L[ℝ] E) (SchwartzMap.fderivCLM ℝ V E g)))) x

end SchwartzConvolution

open Set Filter MeasureTheory
open scoped SchwartzMap Topology

namespace SchwartzConvolution
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scaled_majorant (g : SchwartzMap V E) (a b : ℝ) (ha : 0 < a) (K : ℕ) :
    ∃ B : V → ℝ, Integrable B ∧ ∀ c ∈ Icc a b, ∀ x,
      ‖(c⁻¹)^K • g (c⁻¹ • x)‖ ≤ B x := by
  let N := Module.finrank ℝ V + 1
  let M := max b 1
  let C := 2^N * (Finset.Iic (N,0)).sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) g
  have hC : 0 ≤ C := by positivity
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdec (z : V) : (1+‖z‖)^N * ‖g z‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N,0)) le_rfl le_rfl g z
  refine ⟨fun x => ((a⁻¹)^K*(M^N*C))/(1+‖x‖)^N, ?_, ?_⟩
  · have hi : Integrable (fun x : V => (1+‖x‖)^(-(N : ℝ))) :=
      integrable_one_add_norm (by dsimp [N]; norm_num)
    simpa only [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+‖(_ : V)‖),
      Real.rpow_natCast, div_eq_mul_inv] using hi.const_mul ((a⁻¹)^K*(M^N*C))
  · intro c hc x
    have hcpos : 0 < c := ha.trans_le hc.1
    have hcM : c ≤ M := hc.2.trans (le_max_left _ _)
    have hnx : ‖x‖ = c * ‖c⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos),
        ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
    have hs : 1+‖x‖ ≤ M*(1+‖c⁻¹ • x‖) := by
      rw [hnx, mul_add, mul_one]
      exact add_le_add (le_max_right b 1) (mul_le_mul_of_nonneg_right hcM (norm_nonneg _))
    have hg : ‖g (c⁻¹ • x)‖ * (1+‖x‖)^N ≤ M^N*C := by
      calc
        _ ≤ ‖g (c⁻¹ • x)‖ * (M * (1+‖c⁻¹ • x‖))^N := by gcongr
        _ = M^N * ((1+‖c⁻¹ • x‖)^N * ‖g (c⁻¹ • x)‖) := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hdec _) (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = (c⁻¹)^K * (‖g (c⁻¹ • x)‖ * (1+‖x‖)^N) := by ring
      _ ≤ (a⁻¹)^K * (‖g (c⁻¹ • x)‖ * (1+‖x‖)^N) := by
        gcongr
        exact hc.1
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)

end SchwartzConvolution

namespace LaplacianScaling
open scoped Laplacian ContDiff
variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma laplacian_scaled (f : V → E) (hf : ContDiff ℝ 2 f) (a c : ℝ) :
    Δ (fun x => a • f (c • x)) = fun x => (a*c^2) • Δ f (c • x) := by
  have hs : ContDiff ℝ 2 (fun x : V => f (c • x)) := hf.comp (by fun_prop)
  funext x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_const_smul_apply' hs.contDiffAt,
    iteratedFDeriv_comp_const_smul c hf]
  simp only [smul_apply, smul_smul, ← Finset.smul_sum,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]

end LaplacianScaling

namespace BiharmonicKernel
section LaplacianKernelScaling
open scoped SchwartzMap FourierTransform ZeroAtInfty Convolution Laplacian ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma laplacian_kernel_scaling (t : ℝ) (ht : 0 < t) (r : ℝ) (hr : 0 < r) :
    ((Δ (heatKernel (V := V) (r^4*t) (by positivity)) : SchwartzMap V ℂ) : V → ℂ) =
      fun x => ((r ^ Module.finrank ℝ V)⁻¹ * (r⁻¹)^2) •
        (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) (r⁻¹ • x) := by
  have he : (heatKernel (V := V) (r^4*t) (by positivity) : V → ℂ) =
      fun x => (r ^ Module.finrank ℝ V)⁻¹ • heatKernel (V := V) t ht (r⁻¹ • x) := by
    funext x
    exact heatKernel_scaling t ht r hr x
  have hs := LaplacianScaling.laplacian_scaled (heatKernel (V := V) t ht)
    ((heatKernel (V := V) t ht).smooth 2) (r ^ Module.finrank ℝ V)⁻¹ r⁻¹
  funext x
  simpa only [← he, ← SchwartzMap.laplacian_apply] using congrFun hs x

lemma biharmonic_kernel_scaling (t : ℝ) (ht : 0 < t) (r : ℝ) (hr : 0 < r) :
    ((Δ (Δ (heatKernel (V := V) (r^4*t) (by positivity)) : SchwartzMap V ℂ) : SchwartzMap V ℂ) : V → ℂ) =
      fun x => (r⁻¹)^(Module.finrank ℝ V+4) •
        (Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) (r⁻¹ • x) := by
  have he := laplacian_kernel_scaling (V := V) t ht r hr
  have hs := LaplacianScaling.laplacian_scaled ((Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : V → ℂ)
    ((Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ).smooth 2)
      ((r ^ Module.finrank ℝ V)⁻¹ * (r⁻¹)^2) r⁻¹
  funext x
  have hx := congrFun hs x
  rw [← he] at hx
  simp only [← SchwartzMap.laplacian_apply] at hx
  rw [hx, inv_pow, pow_add]
  congr 1
  ring

lemma evolution_coe_convolution (t : ℝ) (ht : 0 < t) (f : C₀(V, ℂ)) :
    (evolution t f : V → ℂ) = f.toBCF ⋆[ContinuousLinearMap.mul ℝ ℂ] heatKernel (V := V) t ht := by
  funext x
  rw [evolution_apply t ht, convolution_def]
  rw [← integral_sub_left_eq_self (fun y : V => heatKernel (V := V) t ht y * f (x-y)) volume x]
  simp only [sub_sub_self, ContinuousLinearMap.mul_apply']
  congr 1
  funext y
  exact mul_comm _ _

lemma evolution_smooth (t : ℝ) (ht : 0 < t) (f : C₀(V, ℂ)) :
    ContDiff ℝ ∞ (evolution t f : V → ℂ) := by
  rw [evolution_coe_convolution t ht]
  exact SchwartzConvolution.contDiff_convolution (ContinuousLinearMap.mul ℝ ℂ) f.toBCF (heatKernel (V := V) t ht)

lemma evolution_biharmonic (t : ℝ) (ht : 0 < t) (f : C₀(V, ℂ)) :
    Δ (Δ (evolution t f : V → ℂ)) =
      (f.toBCF ⋆[ContinuousLinearMap.mul ℝ ℂ] (Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ)) := by
  rw [evolution_coe_convolution t ht, SchwartzConvolution.laplacian_convolution,
    SchwartzConvolution.laplacian_convolution]

lemma kernel_deriv_majorant (t : ℝ) (ht : 0 < t) :
    ∃ B : V → ℝ, Integrable B ∧ ∀ s ∈ Ioo (t/2) (2*t), ∀ x : V,
      ‖deriv (fun u => kernel u x) s‖ ≤ B x := by
  let r : ℝ → ℝ := fun s => Real.sqrt (Real.sqrt s)
  let g : SchwartzMap V ℂ := Δ (Δ (heatKernel (V := V) 1 zero_lt_one) : SchwartzMap V ℂ)
  have hr (s : ℝ) (hs : 0 < s) : 0 < r s :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hs)
  have hr4 (s : ℝ) (hs : 0 < s) : r s ^ 4 = s := by
    dsimp [r]
    calc
      _ = ((Real.sqrt (Real.sqrt s))^2)^2 := by ring
      _ = s := by rw [Real.sq_sqrt (Real.sqrt_nonneg s), Real.sq_sqrt hs.le]
  obtain ⟨B,hB,hbound⟩ := SchwartzConvolution.scaled_majorant g (r (t/2)) (r (2*t))
    (hr _ (by positivity)) (Module.finrank ℝ V+4)
  refine ⟨B,hB,fun s hs x => ?_⟩
  have hspos : 0 < s := lt_trans (by positivity) hs.1
  rw [(kernel_heat_equation s hspos x).deriv, norm_neg]
  have he := congrFun (biharmonic_kernel_scaling (V := V) 1 zero_lt_one (r s) (hr s hspos)) x
  simp only [mul_one, hr4 s hspos] at he
  rw [he]
  apply hbound (r s) ⟨?_, ?_⟩ x
  · exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hs.1.le)
  · exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hs.2.le)

lemma evolution_hasDerivAt (t : ℝ) (ht : 0 < t) (f : C₀(V, ℂ)) :
    HasDerivAt (fun s => evolution s f)
      (-C0Convolution.convolve
        (Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) f) t := by
  let F := fun s : ℝ => fun y : V => kernel s y • C0Convolution.translate y f
  let F' := fun s : ℝ => fun y : V =>
    deriv (fun u => kernel u y) s • C0Convolution.translate y f
  have hK (s : ℝ) (hs : 0 < s) : kernel (V := V) s = heatKernel s hs :=
    (heatKernel_eq_kernel s hs).symm
  have hD (s : ℝ) (hs : 0 < s) : (fun y : V => deriv (fun u => kernel u y) s) =
      (-(Δ (Δ (heatKernel (V := V) s hs) : SchwartzMap V ℂ) : SchwartzMap V ℂ) : V → ℂ) := by
    funext y
    exact (kernel_heat_equation s hs y).deriv
  have hFi (s : ℝ) (hs : 0 < s) : Integrable (F s) := by
    dsimp [F]
    rw [hK s hs]
    exact C0Convolution.integrable_translated _ (heatKernel s hs).integrable f
  have hF'i (s : ℝ) (hs : 0 < s) : Integrable (F' s) := by
    change Integrable (fun y => (fun y : V => deriv (fun u => kernel u y) s) y • _)
    rw [hD s hs]
    exact C0Convolution.integrable_translated _
      (-(Δ (Δ (heatKernel (V := V) s hs) : SchwartzMap V ℂ) : SchwartzMap V ℂ)).integrable f
  obtain ⟨B,hB,hbound⟩ := kernel_deriv_majorant (V := V) t ht
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun y => B y * ‖f‖)
    (s := Ioo (t/2) (2*t)) (Ioo_mem_nhds (by linarith) (by linarith))
    (by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact (hFi s hs).aestronglyMeasurable)
    (hFi t ht) (hF'i t ht).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y s hs => by
      simp only [F', norm_smul, C0Convolution.norm_translate]
      exact mul_le_mul_of_nonneg_right (hbound s hs y) (norm_nonneg f)))
    (hB.mul_const ‖f‖)
    (Filter.Eventually.of_forall (fun y s hs => by
      dsimp only [F, F']
      exact ((kernel_heat_equation s (lt_trans (by positivity) hs.1) y).differentiableAt.hasDerivAt).smul_const (C0Convolution.translate y f)))
  have hval : (∫ y, F' t y) = -C0Convolution.convolve
      (Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) f := by
    change (∫ y, (fun y : V => deriv (fun u => kernel u y) t) y • _) = _
    rw [hD t ht]
    change (∫ y, -((Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) y) • C0Convolution.translate y f) =
      -(∫ y, (Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) y • C0Convolution.translate y f)
    have he (y : V) :
        -((Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) y) • C0Convolution.translate y f =
        -((Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) y • C0Convolution.translate y f) :=
      neg_smul ((Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) y) (C0Convolution.translate y f)
    simp_rw [he]
    exact integral_neg _
  rw [hval] at hd
  apply hd.2.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  rw [evolution_eq_convolve s hs]
  change C0Convolution.convolve _ _ = ∫ y, kernel s y • _
  rw [hK s hs]
  rfl

lemma evolution_heat_equation (t : ℝ) (ht : 0 < t) (f : C₀(V, ℂ)) (x : V) :
    HasDerivAt (fun s => evolution s f x)
      (- (Δ (Δ (evolution t f : V → ℂ) : V → ℂ) : V → ℂ) x) t := by
  have hd := ((C0Convolution.eval x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (evolution_hasDerivAt t ht f)
  change HasDerivAt (fun s => evolution s f x)
    (-C0Convolution.convolve
      (Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) f x) t at hd
  convert hd using 1
  congr 1
  rw [evolution_biharmonic, convolution_def, C0Convolution.convolve_apply _
    (Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable]
  rw [← integral_sub_left_eq_self
    (fun y : V => (Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) y * f (x-y)) volume x]
  simp only [sub_sub_self, ContinuousLinearMap.mul_apply']
  congr 1
  funext y
  exact mul_comm _ _

end LaplacianKernelScaling

open scoped SchwartzMap ZeroAtInfty
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma kernel_majorant (a b : ℝ) (ha : 0 < a) :
    ∃ B : V → ℝ, Integrable B ∧ ∀ t ∈ Icc a b, ∀ x : V, ‖kernel t x‖ ≤ B x := by
  let r := fun t : ℝ => Real.sqrt (Real.sqrt t)
  obtain ⟨B,hB,hbound⟩ := SchwartzConvolution.scaled_majorant
    (heatKernel (V := V) 1 zero_lt_one) (r a) (r b)
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ha)) (Module.finrank ℝ V)
  refine ⟨B,hB,fun t ht x => ?_⟩
  rw [kernel_eq_scaled t (ha.trans_le ht.1) x, ← inv_pow]
  exact hbound (r t) ⟨Real.sqrt_le_sqrt (Real.sqrt_le_sqrt ht.1),
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt ht.2)⟩ x

lemma continuous_kernel_comp {X : Type*} [TopologicalSpace X]
    (a : X → ℝ) (v : X → V) (ha : Continuous a) (hv : Continuous v)
    (hpos : ∀ x, 0 < a x) : Continuous (fun x => kernel (a x) (v x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ContinuousAt.comp (f := fun u => (a u,v u))
    (kernel_contDiffAt (a x,v x) (hpos x)).continuousAt
    (ha.continuousAt.prodMk hv.continuousAt)

end BiharmonicKernel

namespace FrozenParametrix
open scoped SchwartzMap ZeroAtInfty
open BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def value (a : V → ℝ) (r : ℝ) (f : C₀(V, ℂ)) (x : V) : ℂ :=
  ∫ y : V, kernel (a (x-r • y)) y * f (x-r • y)

lemma integrable_value (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (r : ℝ) (f : C₀(V, ℂ)) (x : V) :
    Integrable (fun y : V => kernel (a (x-r • y)) y * f (x-r • y)) := by
  obtain ⟨B,hB,hbound⟩ := kernel_majorant (V := V) α β hα
  apply (hB.mul_const ‖f‖).mono'
  · exact ((continuous_kernel_comp (fun y : V => a (x-r • y)) id
      (ha.comp (by fun_prop)) continuous_id (fun y => hα.trans_le (hab _).1)).mul
      (f.continuous.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul (hbound _ (hab _) y) (C0Convolution.apply_norm_le f _)
      (norm_nonneg _) ((norm_nonneg (kernel (a 0) y)).trans (hbound (a 0) (hab 0) y))

lemma continuous_value (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (f : C₀(V, ℂ)) :
    Continuous (fun p : ℝ × V => value a p.1 f p.2) := by
  obtain ⟨B,hB,hbound⟩ := kernel_majorant (V := V) α β hα
  change Continuous (fun p : ℝ × V => ∫ y : V, kernel (a (p.2-p.1 • y)) y * f (p.2-p.1 • y))
  apply continuous_of_dominated (bound := fun y => B y * ‖f‖)
  · intro p
    exact (integrable_value a ha α β hα hab p.1 f p.2).aestronglyMeasurable
  · intro p
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul (hbound _ (hab _) y) (C0Convolution.apply_norm_le f _)
      (norm_nonneg _) ((norm_nonneg (kernel (a 0) y)).trans (hbound (a 0) (hab 0) y))
  · exact hB.mul_const ‖f‖
  · filter_upwards with y
    exact (continuous_kernel_comp (fun p : ℝ × V => a (p.2-p.1 • y)) (fun _ => y)
      (ha.comp (by fun_prop)) continuous_const (fun p => hα.trans_le (hab _).1)).mul
        (f.continuous.comp (by fun_prop))

lemma zero_at_infty_value (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (r : ℝ) (f : C₀(V, ℂ)) :
    Tendsto (value a r f) (cocompact V) (𝓝 0) := by
  have : (cocompact V).IsCountablyGenerated := by
    rw [← comap_dist_left_atTop_eq_cocompact (0 : V)]
    infer_instance
  obtain ⟨B,hB,hbound⟩ := kernel_majorant (V := V) α β hα
  have hlim (y : V) : Tendsto (fun x : V => kernel (a (x-r • y)) y * f (x-r • y))
      (cocompact V) (𝓝 0) := by
    have hf : Tendsto (fun x : V => f (x-r • y)) (cocompact V) (𝓝 0) :=
      zero_at_infty (C0Convolution.translate (r • y) f)
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun x => norm_nonneg _) (fun x => ?_)
      (by simpa using hf.norm.const_mul (B y))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound _ (hab _) y) (norm_nonneg _)
  have hi := tendsto_integral_filter_of_dominated_convergence
    (fun y => B y * ‖f‖)
    (Filter.Eventually.of_forall (fun x =>
      (integrable_value a ha α β hα hab r f x).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun x => Filter.Eventually.of_forall (fun y => by
      rw [norm_mul]
      exact mul_le_mul (hbound _ (hab _) y) (C0Convolution.apply_norm_le f _)
        (norm_nonneg _) ((norm_nonneg (kernel (a 0) y)).trans (hbound (a 0) (hab 0) y)))))
    (hB.mul_const ‖f‖) (Filter.Eventually.of_forall hlim)
  change Tendsto (fun x : V => ∫ y : V, kernel (a (x-r • y)) y * f (x-r • y)) _ _
  simpa only [integral_zero] using hi

def frozen (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (r : ℝ) (f : C₀(V, ℂ)) : C₀(V, ℂ) where
  toFun := value a r f
  continuous_toFun := by
    change Continuous (fun x : V => value a r f x)
    exact Continuous.comp (f := fun x : V => (r,x))
      (continuous_value a ha α β hα hab f) (continuous_const.prodMk continuous_id)
  zero_at_infty' := zero_at_infty_value a ha α β hα hab r f

end FrozenParametrix

open scoped Topology ZeroAtInfty BoundedContinuousFunction
open Set Filter MeasureTheory
namespace C0Multiplier
variable {V : Type*} [TopologicalSpace V]

def mul (g : V →ᵇ ℂ) (f : C₀(V,ℂ)) : C₀(V,ℂ) where
  toFun x := g x * f x
  continuous_toFun := g.continuous.mul f.continuous
  zero_at_infty' := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun x => norm_nonneg _) (fun x => ?_)
      (by simpa using (zero_at_infty f).norm.const_mul ‖g‖)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _)

@[simp] lemma mul_apply (g : V →ᵇ ℂ) (f : C₀(V,ℂ)) (x : V) :
    mul g f x = g x * f x := rfl

lemma norm_mul_le (g : V →ᵇ ℂ) (f : C₀(V,ℂ)) : ‖mul g f‖ ≤ ‖g‖ * ‖f‖ := by
  change ‖(mul g f).toBCF‖ ≤ _
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change ‖g x * f x‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (g.norm_coe_le_norm x) (f.toBCF.norm_coe_le_norm x)
    (norm_nonneg _) (norm_nonneg _)

def mulCLM (f : C₀(V,ℂ)) : (V →ᵇ ℂ) →L[ℂ] C₀(V,ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun g => mul g f
      map_add' := fun g h => by ext x; dsimp [mul]; ring
      map_smul' := fun c g => by ext x; dsimp [mul]; ring }
    ‖f‖ (fun g => by
      change ‖mul g f‖ ≤ ‖f‖ * ‖g‖
      rw [mul_comm]
      exact norm_mul_le g f)

lemma continuous_mul (f : C₀(V,ℂ)) : Continuous (fun g : V →ᵇ ℂ => mul g f) :=
  (mulCLM f).continuous

end C0Multiplier

namespace C0Convolution
open scoped ZeroAtInfty
variable {V : Type*} [NormedAddCommGroup V]

@[simp] lemma translate_sub (y : V) (f g : C₀(V,ℂ)) :
    translate y (f-g) = translate y f - translate y g := rfl

lemma continuous_translate_comp {X : Type*} [TopologicalSpace X]
    (y : X → V) (f : X → C₀(V,ℂ)) (hy : Continuous y) (hf : Continuous f) :
    Continuous (fun x => translate (y x) (f x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hb := ((continuous_translate (f x)).comp hy).tendsto x
  apply hb.congr_dist
  change Tendsto (fun z => dist (translate (y z) (f x)) (translate (y z) (f z))) (𝓝 x) (𝓝 0)
  have he (z : X) : dist (translate (y z) (f x)) (translate (y z) (f z)) =
      dist (f x) (f z) := by
    rw [dist_eq_norm, ← translate_sub, norm_translate, ← dist_eq_norm]
  simp_rw [he]
  simpa only [dist_self] using
    (tendsto_const_nhds (x := f x) (f := 𝓝 x)).dist (hf.tendsto x)
end C0Convolution

namespace FrozenParametrix
open scoped SchwartzMap ZeroAtInfty BoundedContinuousFunction
open BiharmonicKernel C0Convolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def kernelFamily (α β : ℝ) (hα : 0 < α) (y : V) : C(Icc α β,ℂ) where
  toFun t := kernel t.val y
  continuous_toFun := continuous_kernel_comp Subtype.val (fun _ => y)
    continuous_subtype_val continuous_const (fun t => hα.trans_le t.property.1)

lemma continuous_kernelFamily (α β : ℝ) (hα : 0 < α) :
    Continuous (kernelFamily (V := V) α β hα) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_kernel_comp (fun p : V × Icc α β => p.2.val) Prod.fst
    (continuous_subtype_val.comp continuous_snd) continuous_fst
    (fun p => hα.trans_le p.2.property.1)

def sourceMultiplier (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (y : V) : V →ᵇ ℂ :=
  (BoundedContinuousFunction.mkOfCompact (kernelFamily α β hα y)).compContinuous
    ⟨fun x => ⟨a x,hab x⟩, ha.subtype_mk _⟩

lemma continuous_sourceMultiplier (a : V → ℝ) (ha : Continuous a) (α β : ℝ)
    (hα : 0 < α) (hab : ∀ x, a x ∈ Icc α β) :
    Continuous (sourceMultiplier a ha α β hα hab) := by
  exact (BoundedContinuousFunction.continuous_compContinuous
    ⟨fun x => ⟨a x,hab x⟩, ha.subtype_mk _⟩).comp
    ((ContinuousMap.isometryEquivBoundedOfCompact (Icc α β) ℂ).continuous.comp
      (continuous_kernelFamily (V := V) α β hα))

def sourceData (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (f : C₀(V,ℂ)) (y : V) : C₀(V,ℂ) :=
  C0Multiplier.mul (sourceMultiplier a ha α β hα hab y) f

lemma continuous_sourceData (a : V → ℝ) (ha : Continuous a) (α β : ℝ)
    (hα : 0 < α) (hab : ∀ x, a x ∈ Icc α β) (f : C₀(V,ℂ)) :
    Continuous (sourceData a ha α β hα hab f) :=
  (C0Multiplier.continuous_mul f).comp (continuous_sourceMultiplier a ha α β hα hab)

@[simp] lemma sourceData_apply (a : V → ℝ) (ha : Continuous a) (α β : ℝ)
    (hα : 0 < α) (hab : ∀ x, a x ∈ Icc α β) (f : C₀(V,ℂ)) (y x : V) :
    sourceData a ha α β hα hab f y x = kernel (a x) y * f x := rfl

lemma sourceData_norm_le (a : V → ℝ) (ha : Continuous a) (α β : ℝ)
    (hα : 0 < α) (hab : ∀ x, a x ∈ Icc α β) (f : C₀(V,ℂ)) (y : V)
    (B : ℝ) (hB : ∀ t ∈ Icc α β, ‖kernel t y‖ ≤ B) :
    ‖sourceData a ha α β hα hab f y‖ ≤ B * ‖f‖ := by
  have hBn : 0 ≤ B := (norm_nonneg (kernel (a 0) y)).trans (hB (a 0) (hab 0))
  apply (C0Convolution.norm_le_iff _ (mul_nonneg hBn (norm_nonneg f))).mpr
  intro x
  rw [sourceData_apply, norm_mul]
  exact mul_le_mul (hB (a x) (hab x)) (apply_norm_le f x) (norm_nonneg _) hBn


lemma integrable_translated_sourceData (a : V → ℝ) (ha : Continuous a) (α β : ℝ)
    (hα : 0 < α) (hab : ∀ x, a x ∈ Icc α β) (r : ℝ) (f : C₀(V,ℂ)) :
    Integrable (fun y : V => C0Convolution.translate (r • y) (sourceData a ha α β hα hab f y)) := by
  obtain ⟨B,hB,hbound⟩ := kernel_majorant (V := V) α β hα
  apply (hB.mul_const ‖f‖).mono'
  · exact (continuous_translate_comp (fun y : V => r • y)
      (sourceData a ha α β hα hab f) (by fun_prop)
      (continuous_sourceData a ha α β hα hab f)).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_translate]
    exact sourceData_norm_le a ha α β hα hab f y (B y) (fun t ht => hbound t ht y)

lemma frozen_eq_integral (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (r : ℝ) (f : C₀(V,ℂ)) :
    frozen a ha α β hα hab r f =
      ∫ y : V, C0Convolution.translate (r • y) (sourceData a ha α β hα hab f y) := by
  ext x
  change value a r f x = (eval x) (∫ y : V, C0Convolution.translate (r • y)
    (sourceData a ha α β hα hab f y))
  rw [← (eval x).integral_comp_comm (integrable_translated_sourceData a ha α β hα hab r f)]
  rfl

lemma continuous_frozen (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (f : C₀(V,ℂ)) :
    Continuous (fun r : ℝ => frozen a ha α β hα hab r f) := by
  simp_rw [frozen_eq_integral]
  obtain ⟨B,hB,hbound⟩ := kernel_majorant (V := V) α β hα
  apply continuous_of_dominated (bound := fun y => B y * ‖f‖)
  · intro r
    exact (integrable_translated_sourceData a ha α β hα hab r f).aestronglyMeasurable
  · intro r
    filter_upwards with y
    rw [norm_translate]
    exact sourceData_norm_le a ha α β hα hab f y (B y) (fun t ht => hbound t ht y)
  · exact hB.mul_const ‖f‖
  · filter_upwards with y
    exact (continuous_translate (sourceData a ha α β hα hab f y)).comp
      (continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => y)))

@[simp] lemma frozen_zero (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (f : C₀(V,ℂ)) :
    frozen a ha α β hα hab 0 f = f := by
  ext x
  change (∫ y : V, kernel (a (x-0 • y)) y * f (x-0 • y)) = f x
  simp only [zero_smul, sub_zero, integral_mul_const]
  rw [← heatKernel_eq_kernel (a x) (hα.trans_le (hab x).1), integral_heatKernel, one_mul]

lemma frozen_tendsto_identity (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (f : C₀(V,ℂ)) :
    Tendsto (fun r : ℝ => frozen a ha α β hα hab r f) (𝓝 0) (𝓝 f) := by
  simpa only [frozen_zero] using (continuous_frozen a ha α β hα hab f).tendsto 0


lemma norm_frozen_le (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (r : ℝ) (f : C₀(V,ℂ)) (B : V → ℝ)
    (hB : Integrable B) (hbound : ∀ t ∈ Icc α β, ∀ y : V, ‖kernel t y‖ ≤ B y) :
    ‖frozen a ha α β hα hab r f‖ ≤ (∫ y : V, B y) * ‖f‖ := by
  rw [frozen_eq_integral, ← integral_mul_const]
  apply norm_integral_le_of_norm_le (hB.mul_const ‖f‖)
  filter_upwards with y
  rw [norm_translate]
  exact sourceData_norm_le a ha α β hα hab f y (B y) (fun t ht => hbound t ht y)

lemma frozen_add (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (r : ℝ) (f g : C₀(V,ℂ)) :
    frozen a ha α β hα hab r (f+g) = frozen a ha α β hα hab r f +
      frozen a ha α β hα hab r g := by
  ext x
  change (∫ y : V, kernel (a (x-r • y)) y * (f (x-r • y)+g (x-r • y))) =
    (∫ y : V, kernel (a (x-r • y)) y * f (x-r • y)) +
    (∫ y : V, kernel (a (x-r • y)) y * g (x-r • y))
  simp_rw [mul_add]
  exact integral_add (integrable_value a ha α β hα hab r f x)
    (integrable_value a ha α β hα hab r g x)

lemma frozen_smul (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (r : ℝ) (c : ℂ) (f : C₀(V,ℂ)) :
    frozen a ha α β hα hab r (c • f) = c • frozen a ha α β hα hab r f := by
  ext x
  change (∫ y : V, kernel (a (x-r • y)) y * (c * f (x-r • y))) =
    c * (∫ y : V, kernel (a (x-r • y)) y * f (x-r • y))
  simp_rw [mul_left_comm (kernel _ _) c, integral_const_mul]

lemma exists_uniform_norm_bound (α β : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : V → ℝ) (ha : Continuous a)
      (hab : ∀ x, a x ∈ Icc α β) (r : ℝ) (f : C₀(V,ℂ)),
      ‖frozen a ha α β hα hab r f‖ ≤ C * ‖f‖ := by
  obtain ⟨B,hB,hbound⟩ := kernel_majorant (V := V) α β hα
  refine ⟨∫ y : V, |B y|, integral_nonneg (fun y => abs_nonneg _), ?_⟩
  intro a ha hab r f
  exact norm_frozen_le a ha α β hα hab r f (fun y => |B y|) hB.abs
    (fun t ht y => (hbound t ht y).trans (le_abs_self _))

lemma frozen_apply_unscaled (a : V → ℝ) (ha : Continuous a) (α β : ℝ) (hα : 0 < α)
    (hab : ∀ x, a x ∈ Icc α β) (r : ℝ) (hr : 0 < r) (f : C₀(V,ℂ)) (x : V) :
    frozen a ha α β hα hab r f x =
      ∫ y : V, kernel (r^4*a y) (x-y) * f y := by
  have hscale (t : ℝ) (ht : 0 < t) (w : V) :
      kernel (r^4*t) w = (r^Module.finrank ℝ V)⁻¹ • kernel t (r⁻¹ • w) := by
    rw [← heatKernel_eq_kernel (r^4*t) (by positivity), ← heatKernel_eq_kernel t ht]
    exact heatKernel_scaling t ht r hr w
  rw [← integral_sub_left_eq_self
    (fun y : V => kernel (r^4*a y) (x-y) * f y) volume x]
  simp only [sub_sub_self]
  simp_rw [hscale _ (hα.trans_le (hab _).1), smul_mul_assoc]
  rw [integral_smul]
  let F := fun y : V => kernel (a (x-r • y)) y * f (x-r • y)
  have he : (fun y : V => kernel (a (x-y)) (r⁻¹ • y) * f (x-y)) =
      fun y : V => F (r⁻¹ • y) := by
    funext y
    dsimp [F]
    rw [smul_inv_smul₀ hr.ne']
  rw [he, Measure.integral_comp_inv_smul_of_nonneg volume F hr.le,
    inv_smul_smul₀ (pow_ne_zero _ hr.ne')]
  rfl

end FrozenParametrix

open Set Filter MeasureTheory
open scoped SchwartzMap Topology

namespace SchwartzConvolution
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scaled_weighted_majorant (g : SchwartzMap V E) (a b : ℝ) (ha : 0 < a) (K L : ℕ) :
    ∃ B : V → ℝ, Integrable B ∧ Integrable (fun x => (1+‖x‖)^L * B x) ∧
      (∀ x, 0 ≤ B x) ∧ ∀ c ∈ Icc a b, ∀ x,
      ‖(c⁻¹)^K • g (c⁻¹ • x)‖ ≤ B x := by
  let N := Module.finrank ℝ V + 1 + L
  let M := max b 1
  let C := 2^N * (Finset.Iic (N,0)).sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) g
  have hC : 0 ≤ C := by positivity
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdec (z : V) : (1+‖z‖)^N * ‖g z‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N,0)) le_rfl le_rfl g z
  refine ⟨fun x => ((a⁻¹)^K*(M^N*C))/(1+‖x‖)^N, ?_, ?_, ?_, ?_⟩
  · have hi : Integrable (fun x : V => (1+‖x‖)^(-(N : ℝ))) :=
      integrable_one_add_norm (by dsimp [N]; push_cast; linarith)
    simpa only [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+‖(_ : V)‖),
      Real.rpow_natCast, div_eq_mul_inv] using hi.const_mul ((a⁻¹)^K*(M^N*C))
  · have hi : Integrable (fun x : V => (1+‖x‖)^(-(Module.finrank ℝ V + 1 : ℝ))) :=
      integrable_one_add_norm (by linarith)
    have he (x : V) : (1+‖x‖)^L * (((a⁻¹)^K*(M^N*C))/(1+‖x‖)^N) =
        ((a⁻¹)^K*(M^N*C)) * (1+‖x‖)^(-(Module.finrank ℝ V + 1 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), ← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast]
      dsimp [N]
      rw [pow_add]
      field_simp
      rw [pow_add]
      ring
    simp_rw [he]
    exact hi.const_mul _
  · intro x
    positivity
  · intro c hc x
    have hcpos : 0 < c := ha.trans_le hc.1
    have hcM : c ≤ M := hc.2.trans (le_max_left _ _)
    have hnx : ‖x‖ = c * ‖c⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos),
        ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
    have hs : 1+‖x‖ ≤ M*(1+‖c⁻¹ • x‖) := by
      rw [hnx, mul_add, mul_one]
      exact add_le_add (le_max_right b 1) (mul_le_mul_of_nonneg_right hcM (norm_nonneg _))
    have hg : ‖g (c⁻¹ • x)‖ * (1+‖x‖)^N ≤ M^N*C := by
      calc
        _ ≤ ‖g (c⁻¹ • x)‖ * (M * (1+‖c⁻¹ • x‖))^N := by gcongr
        _ = M^N * ((1+‖c⁻¹ • x‖)^N * ‖g (c⁻¹ • x)‖) := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hdec _) (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ = (c⁻¹)^K * (‖g (c⁻¹ • x)‖ * (1+‖x‖)^N) := by ring
      _ ≤ (a⁻¹)^K * (‖g (c⁻¹ • x)‖ * (1+‖x‖)^N) := by
        gcongr
        exact hc.1
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)

end SchwartzConvolution

namespace BiharmonicKernel
open scoped SchwartzMap Laplacian ContDiff Topology
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def bilapKernel (t : ℝ) (x : V) : ℂ := Δ (Δ (kernel (V := V) t)) x

lemma bilapKernel_eq_schwartz (t : ℝ) (ht : 0 < t) (x : V) :
    bilapKernel t x = (Δ (Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : SchwartzMap V ℂ) x := by
  have he : ((Δ (heatKernel (V := V) t ht) : SchwartzMap V ℂ) : V → ℂ) =
      Δ (kernel (V := V) t) := by
    funext y
    rw [SchwartzMap.laplacian_apply, heatKernel_eq_kernel t ht]
  rw [SchwartzMap.laplacian_apply, he]
  rfl

lemma bilapKernel_eq_scaled (t : ℝ) (ht : 0 < t) (x : V) :
    bilapKernel t x = ((Real.sqrt (Real.sqrt t))⁻¹)^(Module.finrank ℝ V+4) •
      (Δ (Δ (heatKernel (V := V) 1 zero_lt_one) : SchwartzMap V ℂ) : SchwartzMap V ℂ)
        ((Real.sqrt (Real.sqrt t))⁻¹ • x) := by
  let r := Real.sqrt (Real.sqrt t)
  have hr : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ht)
  have he : r^4 = t := by
    dsimp [r]
    calc
      _ = ((Real.sqrt (Real.sqrt t))^2)^2 := by ring
      _ = t := by rw [Real.sq_sqrt (Real.sqrt_nonneg t), Real.sq_sqrt ht.le]
  have hs := congrFun (biharmonic_kernel_scaling (V := V) 1 zero_lt_one r hr) x
  simp only [mul_one, he] at hs
  rw [bilapKernel_eq_schwartz t ht]
  exact hs

lemma bilapKernel_contDiffAt (q : ℝ × V) (hq : 0 < q.1) :
    ContDiffAt ℝ ∞ (fun p : ℝ × V => bilapKernel p.1 p.2) q := by
  have hr : ContDiffAt ℝ ∞ (fun p : ℝ × V => Real.sqrt (Real.sqrt p.1)) q :=
    (contDiffAt_fst.sqrt (ne_of_gt hq)).sqrt (ne_of_gt (Real.sqrt_pos.mpr hq))
  have hpos : 0 < Real.sqrt (Real.sqrt q.1) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hq)
  let g : SchwartzMap V ℂ := Δ (Δ (heatKernel (V := V) 1 zero_lt_one) : SchwartzMap V ℂ)
  have hs : ContDiffAt ℝ ∞ (fun p : ℝ × V =>
      ((Real.sqrt (Real.sqrt p.1))⁻¹)^(Module.finrank ℝ V+4) •
        g ((Real.sqrt (Real.sqrt p.1))⁻¹ • p.2)) q :=
    ((hr.inv hpos.ne').pow _).smul
      ((g.smooth ⊤).contDiffAt.comp q ((hr.inv hpos.ne').smul contDiffAt_snd))
  apply hs.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds hq)] with p hp
  exact bilapKernel_eq_scaled _ hp _

lemma continuous_bilapKernel_comp {X : Type*} [TopologicalSpace X]
    (a : X → ℝ) (v : X → V) (ha : Continuous a) (hv : Continuous v)
    (hpos : ∀ x, 0 < a x) : Continuous (fun x => bilapKernel (a x) (v x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ContinuousAt.comp (f := fun u => (a u,v u))
    (bilapKernel_contDiffAt (a x,v x) (hpos x)).continuousAt
    (ha.continuousAt.prodMk hv.continuousAt)

lemma bilapKernel_weighted_majorant (a b : ℝ) (ha : 0 < a) :
    ∃ B : V → ℝ, Integrable B ∧ Integrable (fun x => (1+‖x‖) * B x) ∧
      (∀ x, 0 ≤ B x) ∧ ∀ t ∈ Icc a b, ∀ x : V, ‖bilapKernel t x‖ ≤ B x := by
  let r := fun t : ℝ => Real.sqrt (Real.sqrt t)
  obtain ⟨B,hB,hBw,hBn,hbound⟩ := SchwartzConvolution.scaled_weighted_majorant
    (Δ (Δ (heatKernel (V := V) 1 zero_lt_one) : SchwartzMap V ℂ) : SchwartzMap V ℂ)
    (r a) (r b) (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ha)) (Module.finrank ℝ V+4) 1
  refine ⟨B,hB,by simpa only [pow_one] using hBw,hBn,fun t ht x => ?_⟩
  rw [bilapKernel_eq_scaled t (ha.trans_le ht.1) x]
  exact hbound (r t) ⟨Real.sqrt_le_sqrt (Real.sqrt_le_sqrt ht.1),
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt ht.2)⟩ x

end BiharmonicKernel

namespace C0Multiplier
variable {V : Type*} [TopologicalSpace V]

def mulLeftCLM (g : V →ᵇ ℂ) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  LinearMap.mkContinuous
    { toFun := mul g
      map_add' := fun f h => by ext x; dsimp [mul]; ring
      map_smul' := fun c f => by ext x; dsimp [mul]; ring }
    ‖g‖ (norm_mul_le g)

lemma continuous_mul_left (g : V →ᵇ ℂ) : Continuous (mul g) :=
  (mulLeftCLM g).continuous
end C0Multiplier

namespace FrozenFamily
open C0Convolution
variable {V P : Type*} [NormedAddCommGroup V]
  [TopologicalSpace P] [CompactSpace P]

def family (g : C(P × V,ℂ)) (y : V) : C(P,ℂ) :=
  ⟨fun t => g (t,y), g.continuous.comp (by fun_prop)⟩

omit [CompactSpace P] in
lemma continuous_family (g : C(P × V,ℂ)) : Continuous (family g) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact g.continuous.comp (by fun_prop)

def multiplier (g : C(P × V,ℂ)) (a : C(V,P)) (y : V) : V →ᵇ ℂ :=
  (BoundedContinuousFunction.mkOfCompact (family g y)).compContinuous a

lemma continuous_multiplier (g : C(P × V,ℂ)) (a : C(V,P)) :
    Continuous (multiplier g a) :=
  (BoundedContinuousFunction.continuous_compContinuous a).comp
    ((ContinuousMap.isometryEquivBoundedOfCompact P ℂ).continuous.comp (continuous_family g))

def data (g : C(P × V,ℂ)) (a : C(V,P)) (f : C₀(V,ℂ)) (y : V) : C₀(V,ℂ) :=
  C0Multiplier.mul (multiplier g a y) f

@[simp] lemma data_apply (g : C(P × V,ℂ)) (a : C(V,P)) (f : C₀(V,ℂ)) (y x : V) :
    data g a f y x = g (a x,y) * f x := rfl

lemma continuous_data (g : C(P × V,ℂ)) (a : C(V,P)) (f : C₀(V,ℂ)) :
    Continuous (data g a f) :=
  (C0Multiplier.continuous_mul f).comp (continuous_multiplier g a)

lemma norm_data_le (g : C(P × V,ℂ)) (a : C(V,P)) (f : C₀(V,ℂ)) (y : V)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ p, ‖g (p,y)‖ ≤ B) :
    ‖data g a f y‖ ≤ B * ‖f‖ := by
  apply (norm_le_iff _ (mul_nonneg hB (norm_nonneg f))).mpr
  intro x
  rw [data_apply, norm_mul]
  exact mul_le_mul (hbound _) (apply_norm_le f x) (norm_nonneg _) hB

variable [NormedSpace ℝ V]

def residualData (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (f : C₀(V,ℂ)) (y : V) : C₀(V,ℂ) :=
  C0Multiplier.mul c₁ (C0Convolution.translate (r • y) (data g a f y)) -
    C0Convolution.translate (r • y) (data g a (C0Multiplier.mul c₀ f) y)

lemma residualData_apply (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (f : C₀(V,ℂ)) (y x : V) :
    residualData g a c₀ c₁ r f y x =
      (c₁ x - c₀ (x-r • y)) * g (a (x-r • y),y) * f (x-r • y) := by
  change c₁ x * (g (a (x-r • y),y) * f (x-r • y)) -
    g (a (x-r • y),y) * (c₀ (x-r • y) * f (x-r • y)) = _
  ring

lemma continuous_residualData (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (f : C₀(V,ℂ)) : Continuous (residualData g a c₀ c₁ r f) :=
  ((C0Multiplier.continuous_mul_left c₁).comp
    (continuous_translate_comp (fun y : V => r • y) (data g a f)
      (by fun_prop) (continuous_data g a f))).sub
    (continuous_translate_comp (fun y : V => r • y) (data g a (C0Multiplier.mul c₀ f))
      (by fun_prop) (continuous_data g a (C0Multiplier.mul c₀ f)))

lemma norm_residualData_le (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (hr : 0 ≤ r) (f : C₀(V,ℂ)) (y : V)
    (B L δ : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hbound : ∀ p, ‖g (p,y)‖ ≤ B)
    (hLip : ∀ x z, ‖c₁ x-c₀ z‖ ≤ L*(‖x-z‖+δ)) :
    ‖residualData g a c₀ c₁ r f y‖ ≤ L*(r*‖y‖+δ)*B*‖f‖ := by
  apply (norm_le_iff _ (by positivity)).mpr
  intro x
  rw [residualData_apply, norm_mul, norm_mul]
  have hc : ‖c₁ x-c₀ (x-r • y)‖ ≤ L*(r*‖y‖+δ) := by
    simpa only [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] using
      hLip x (x-r • y)
  exact mul_le_mul (mul_le_mul hc (hbound _) (norm_nonneg _) (by positivity))
    (apply_norm_le f _) (norm_nonneg _) (by positivity)

variable [MeasureSpace V] [BorelSpace V] [SecondCountableTopology V]

lemma integrable_residualData (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (f : C₀(V,ℂ)) (B : V → ℝ) (hB : Integrable B)
    (hBn : ∀ y, 0 ≤ B y) (hbound : ∀ p y, ‖g (p,y)‖ ≤ B y) :
    Integrable (residualData g a c₀ c₁ r f) := by
  apply (hB.const_mul ((‖c₁‖+‖c₀‖)*‖f‖)).mono'
  · exact (continuous_residualData g a c₀ c₁ r f).aestronglyMeasurable
  · filter_upwards with y
    have hBy := hBn y
    apply (norm_le_iff _ (by positivity)).mpr
    intro x
    rw [residualData_apply, norm_mul, norm_mul]
    have hc : ‖c₁ x-c₀ (x-r • y)‖ ≤ ‖c₁‖+‖c₀‖ :=
      (norm_sub_le _ _).trans (add_le_add (c₁.norm_coe_le_norm _) (c₀.norm_coe_le_norm _))
    calc
      _ ≤ (‖c₁‖+‖c₀‖)*B y*‖f‖ :=
        mul_le_mul (mul_le_mul hc (hbound _ y) (norm_nonneg _) (by positivity))
          (apply_norm_le f _) (norm_nonneg _) (by positivity)
      _ = _ := by ring

def residual (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (f : C₀(V,ℂ)) : C₀(V,ℂ) :=
  ∫ y : V, residualData g a c₀ c₁ r f y

lemma residual_apply (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (f : C₀(V,ℂ)) (B : V → ℝ) (hB : Integrable B)
    (hBn : ∀ y, 0 ≤ B y) (hbound : ∀ p y, ‖g (p,y)‖ ≤ B y) (x : V) :
    residual g a c₀ c₁ r f x =
      ∫ y : V, (c₁ x-c₀ (x-r • y))*g (a (x-r • y),y)*f (x-r • y) := by
  change (eval x) (∫ y : V, residualData g a c₀ c₁ r f y) = _
  rw [← (eval x).integral_comp_comm (integrable_residualData g a c₀ c₁ r f B hB hBn hbound)]
  simp only [eval_apply, residualData_apply]

omit [BorelSpace V] [SecondCountableTopology V] in
lemma norm_residual_le (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (hr : 0 ≤ r) (f : C₀(V,ℂ)) (B : V → ℝ)
    (hB : Integrable B) (hBw : Integrable (fun y => ‖y‖*B y))
    (hBn : ∀ y, 0 ≤ B y) (hbound : ∀ p y, ‖g (p,y)‖ ≤ B y)
    (L δ : ℝ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hLip : ∀ x z, ‖c₁ x-c₀ z‖ ≤ L*(‖x-z‖+δ)) :
    ‖residual g a c₀ c₁ r f‖ ≤
      L*(r*(∫ y : V, ‖y‖*B y)+δ*(∫ y : V, B y))*‖f‖ := by
  have hi : Integrable (fun y : V => L*(r*‖y‖+δ)*B y*‖f‖) := by
    convert ((hBw.const_mul r).add (hB.const_mul δ)).const_mul L |>.mul_const ‖f‖ using 1
    ext y
    simp only [Pi.add_apply]
    ring
  calc
    _ ≤ ∫ y : V, L*(r*‖y‖+δ)*B y*‖f‖ := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards with y
      exact norm_residualData_le g a c₀ c₁ r hr f y (B y) L δ (hBn y) hL hδ
        (fun p => hbound p y) hLip
    _ = _ := by
      have he (y : V) : L*(r*‖y‖+δ)*B y*‖f‖ =
          L*(r*(‖y‖*B y)+δ*B y)*‖f‖ := by ring
      simp_rw [he]
      rw [integral_mul_const, integral_const_mul, integral_add (hBw.const_mul r) (hB.const_mul δ),
        integral_const_mul, integral_const_mul]

end FrozenFamily

namespace BiharmonicKernel
open scoped SchwartzMap Laplacian
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma bilapKernel_scaling (t : ℝ) (ht : 0 < t) (r : ℝ) (hr : 0 < r) (x : V) :
    bilapKernel (r^4*t) x = (r⁻¹)^(Module.finrank ℝ V+4) •
      bilapKernel t (r⁻¹ • x) := by
  rw [bilapKernel_eq_schwartz _ (by positivity), bilapKernel_eq_schwartz _ ht]
  exact congrFun (biharmonic_kernel_scaling t ht r hr) x
end BiharmonicKernel

namespace FrozenParametrix
open scoped ZeroAtInfty BoundedContinuousFunction
open BiharmonicKernel C0Convolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def bilapFamily (α β : ℝ) (hα : 0 < α) : C(Icc α β × V,ℂ) :=
  ⟨fun p => bilapKernel p.1.val p.2,
    continuous_bilapKernel_comp (fun p : Icc α β × V => p.1.val) Prod.snd
      (continuous_subtype_val.comp continuous_fst) continuous_snd
      (fun p => hα.trans_le p.1.property.1)⟩

def coefficient {α β : ℝ} (a : C(V,Icc α β)) : V →ᵇ ℂ :=
  (BoundedContinuousFunction.mkOfCompact
    (⟨fun t : Icc α β => (t.val : ℂ), by fun_prop⟩ : C(Icc α β,ℂ))).compContinuous a

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] lemma coefficient_apply {α β : ℝ} (a : C(V,Icc α β)) (x : V) :
    coefficient a x = ((a x).val : ℂ) := rfl

def principalResidual {α β : ℝ} (hα : 0 < α) (a₀ a₁ : C(V,Icc α β))
    (r : ℝ) (f : C₀(V,ℂ)) : C₀(V,ℂ) :=
  (r⁻¹)^4 • FrozenFamily.residual (bilapFamily α β hα) a₀
    (coefficient a₀) (coefficient a₁) r f

lemma principalResidual_apply_scaled {α β : ℝ} (hα : 0 < α) (a₀ a₁ : C(V,Icc α β))
    (r : ℝ) (f : C₀(V,ℂ)) (x : V) :
    principalResidual hα a₀ a₁ r f x = (r⁻¹)^4 •
      ∫ y : V, (((a₁ x).val-(a₀ (x-r • y)).val : ℝ) : ℂ) *
        bilapKernel (a₀ (x-r • y)).val y * f (x-r • y) := by
  obtain ⟨B,hB,_,hBn,hbound⟩ := bilapKernel_weighted_majorant (V := V) α β hα
  change (r⁻¹)^4 • FrozenFamily.residual (bilapFamily α β hα) a₀
    (coefficient a₀) (coefficient a₁) r f x = _
  rw [FrozenFamily.residual_apply _ _ _ _ _ _ B hB hBn
    (fun p y => hbound p.val p.property y)]
  simp only [coefficient_apply, Complex.ofReal_sub]
  rfl

lemma principalResidual_apply_unscaled {α β : ℝ} (hα : 0 < α) (a₀ a₁ : C(V,Icc α β))
    (r : ℝ) (hr : 0 < r) (f : C₀(V,ℂ)) (x : V) :
    principalResidual hα a₀ a₁ r f x =
      ∫ y : V, (((a₁ x).val-(a₀ y).val : ℝ) : ℂ) *
        bilapKernel (r^4*(a₀ y).val) (x-y) * f y := by
  rw [principalResidual_apply_scaled]
  rw [← integral_sub_left_eq_self
    (fun y : V => (((a₁ x).val-(a₀ y).val : ℝ) : ℂ) *
      bilapKernel (r^4*(a₀ y).val) (x-y) * f y) volume x]
  simp only [sub_sub_self]
  simp_rw [bilapKernel_scaling _ (hα.trans_le (a₀ _).property.1) r hr,
    mul_smul_comm, smul_mul_assoc]
  rw [integral_smul]
  let F := fun y : V => (((a₁ x).val-(a₀ (x-r • y)).val : ℝ) : ℂ) *
    bilapKernel (a₀ (x-r • y)).val y * f (x-r • y)
  have he : (fun y : V => (((a₁ x).val-(a₀ (x-y)).val : ℝ) : ℂ) *
      bilapKernel (a₀ (x-y)).val (r⁻¹ • y) * f (x-y)) =
        fun y : V => F (r⁻¹ • y) := by
    funext y
    dsimp [F]
    rw [smul_inv_smul₀ hr.ne']
  rw [he, Measure.integral_comp_inv_smul_of_nonneg volume F hr.le, smul_smul]
  congr 1
  rw [pow_add, mul_right_comm, ← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, one_mul]

lemma norm_principalResidual_le {α β : ℝ} (hα : 0 < α) (a₀ a₁ : C(V,Icc α β))
    (r : ℝ) (hr : 0 ≤ r) (f : C₀(V,ℂ)) (B : V → ℝ)
    (hB : Integrable B) (hBw : Integrable (fun y => ‖y‖*B y))
    (hBn : ∀ y, 0 ≤ B y)
    (hbound : ∀ t ∈ Icc α β, ∀ y : V, ‖bilapKernel t y‖ ≤ B y)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x z, |(a₁ x).val-(a₀ z).val| ≤ L*(‖x-z‖+r^4)) :
    ‖principalResidual hα a₀ a₁ r f‖ ≤
      (r⁻¹)^4 * (L*(r*(∫ y : V, ‖y‖*B y)+r^4*(∫ y : V, B y))*‖f‖) := by
  rw [principalResidual, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply FrozenFamily.norm_residual_le _ _ _ _ r hr f B hB hBw hBn
    (fun p y => hbound p.val p.property y) L (r^4) hL (by positivity)
  intro x z
  simpa only [coefficient_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    using hLip x z

lemma exists_uniform_principalResidual_bound (α β : ℝ) (hα : 0 < α) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a₀ a₁ : C(V,Icc α β)) (r : ℝ), 0 < r → r ≤ 1 →
      (∀ x z, |(a₁ x).val-(a₀ z).val| ≤ L*(‖x-z‖+r^4)) →
      ∀ f : C₀(V,ℂ), ‖principalResidual hα a₀ a₁ r f‖ ≤ C*(r⁻¹)^3*‖f‖ := by
  obtain ⟨B,hB,hBw,hBn,hbound⟩ := bilapKernel_weighted_majorant (V := V) α β hα
  have hBw' : Integrable (fun y : V => ‖y‖*B y) := by
    have hi : Integrable (fun y : V => (1+‖y‖)*B y-B y) := hBw.sub hB
    have he : (fun y : V => (1+‖y‖)*B y-B y) = (fun y : V => ‖y‖*B y) := by
      funext y
      ring
    rwa [he] at hi
  let M₀ := ∫ y : V, B y
  let M₁ := ∫ y : V, ‖y‖*B y
  have hM₀ : 0 ≤ M₀ := integral_nonneg hBn
  have hM₁ : 0 ≤ M₁ := integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (hBn y))
  refine ⟨L*(M₁+M₀),by positivity,fun a₀ a₁ r hr hr1 hLip f => ?_⟩
  apply (norm_principalResidual_le hα a₀ a₁ r hr.le f B hB hBw' hBn hbound L hL hLip).trans
  have hrinv : 1 ≤ (r⁻¹)^3 := one_le_pow₀ (by exact (one_le_inv₀ hr).mpr hr1)
  have he : (r⁻¹)^4 * (L*(r*M₁+r^4*M₀)*‖f‖) =
      L*((r⁻¹)^3*M₁+M₀)*‖f‖ := by
    field_simp
  change (r⁻¹)^4 * (L*(r*M₁+r^4*M₀)*‖f‖) ≤ _
  rw [he]
  calc
    _ ≤ L*((r⁻¹)^3*M₁+(r⁻¹)^3*M₀)*‖f‖ := by gcongr; exact le_mul_of_one_le_left hM₀ hrinv
    _ = _ := by ring

end FrozenParametrix

open Set Filter MeasureTheory
open scoped Topology ZeroAtInfty BoundedContinuousFunction

namespace CompactComposition
variable {V P F : Type*} [TopologicalSpace V] [PseudoMetricSpace P] [CompactSpace P]
  [PseudoMetricSpace F]

def compose (g : C(P,F)) (a : V →ᵇ P) : V →ᵇ F :=
  (BoundedContinuousFunction.mkOfCompact g).compContinuous a.toContinuousMap

@[simp] lemma compose_apply (g : C(P,F)) (a : V →ᵇ P) (x : V) :
    compose g a x = g (a x) := rfl

lemma continuous_compose : Continuous (fun p : C(P,F) × (V →ᵇ P) => compose p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g₀,a₀⟩
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hg⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous g₀.continuous) (ε/4) (by positivity)
  refine ⟨min (ε/4) δ, lt_min (by positivity) hδ, ?_⟩
  rintro ⟨g,a⟩ hp
  change max (dist g g₀) (dist a a₀) < min (ε/4) δ at hp
  have hgdist : dist g g₀ < ε/4 := (le_max_left _ _).trans_lt (lt_of_lt_of_le hp (min_le_left _ _))
  have hadist : dist a a₀ < δ := (le_max_right _ _).trans_lt (lt_of_lt_of_le hp (min_le_right _ _))
  apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (show (0 : ℝ) ≤ ε/2 by positivity)).mpr ?_) (by linarith)
  intro x
  calc
    dist (g (a x)) (g₀ (a₀ x)) ≤ dist (g (a x)) (g₀ (a x)) + dist (g₀ (a x)) (g₀ (a₀ x)) := dist_triangle _ _ _
    _ ≤ ε/2 := by
      have h₁ := (ContinuousMap.dist_apply_le_dist (f := g) (g := g₀) (a x)).trans_lt hgdist
      have h₂ := hg ((BoundedContinuousFunction.dist_coe_le_dist (f := a) (g := a₀) x).trans_lt hadist)
      linarith
end CompactComposition

namespace C0Multiplier
variable {V : Type*} [TopologicalSpace V]

lemma continuous_mul_joint : Continuous (fun p : (V →ᵇ ℂ) × C₀(V,ℂ) => mul p.1 p.2) := by
  apply ZeroAtInftyContinuousMap.isometry_toBCF.isUniformInducing.isInducing.continuous_iff.mpr
  change Continuous (fun p : (V →ᵇ ℂ) × C₀(V,ℂ) => p.1*p.2.toBCF)
  exact continuous_fst.mul (ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp continuous_snd)

end C0Multiplier

namespace FrozenFamily
open C0Convolution
variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [PseudoMetricSpace P] [CompactSpace P]

omit [NormedSpace ℝ V] in
lemma continuous_multiplier_comp {X : Type*} [TopologicalSpace X]
    (g : C(P × V,ℂ)) (a : X → V →ᵇ P) (y : X → V)
    (ha : Continuous a) (hy : Continuous y) :
    Continuous (fun x => multiplier g (a x).toContinuousMap (y x)) := by
  exact CompactComposition.continuous_compose.comp
    (((continuous_family g).comp hy).prodMk ha)

omit [NormedSpace ℝ V] in
lemma continuous_data_comp {X : Type*} [TopologicalSpace X]
    (g : C(P × V,ℂ)) (a : X → V →ᵇ P) (f : X → C₀(V,ℂ)) (y : X → V)
    (ha : Continuous a) (hf : Continuous f) (hy : Continuous y) :
    Continuous (fun x => data g (a x).toContinuousMap (f x) (y x)) :=
  C0Multiplier.continuous_mul_joint.comp ((continuous_multiplier_comp g a y ha hy).prodMk hf)

lemma continuous_residualData_comp {X : Type*} [TopologicalSpace X]
    (g : C(P × V,ℂ)) (a : X → V →ᵇ P) (c₀ c₁ : X → V →ᵇ ℂ)
    (r : X → ℝ) (f : X → C₀(V,ℂ)) (y : X → V)
    (ha : Continuous a) (h₀ : Continuous c₀) (h₁ : Continuous c₁)
    (hr : Continuous r) (hf : Continuous f) (hy : Continuous y) :
    Continuous (fun x => residualData g (a x).toContinuousMap (c₀ x) (c₁ x) (r x) (f x) (y x)) := by
  apply Continuous.sub
  · exact C0Multiplier.continuous_mul_joint.comp (h₁.prodMk
      (continuous_translate_comp _ _ (hr.smul hy) (continuous_data_comp g a f y ha hf hy)))
  · exact continuous_translate_comp _ _ (hr.smul hy) (continuous_data_comp g a
      (fun x => C0Multiplier.mul (c₀ x) (f x)) y ha
      (C0Multiplier.continuous_mul_joint.comp (h₀.prodMk hf)) hy)

variable [MeasureSpace V] [BorelSpace V] [SecondCountableTopology V]

omit [MeasureSpace V] [BorelSpace V] [SecondCountableTopology V] in
lemma norm_residualData_le_uniform (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (f : C₀(V,ℂ)) (y : V) (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hbound : ∀ p, ‖g (p,y)‖ ≤ B) (hc : ‖c₀‖+‖c₁‖ ≤ M) :
    ‖residualData g a c₀ c₁ r f y‖ ≤ M*‖f‖*B := by
  apply (norm_le_iff _ (by positivity)).mpr
  intro x
  rw [residualData_apply, norm_mul, norm_mul]
  have hn : ‖c₁ x-c₀ (x-r • y)‖ ≤ M :=
    (norm_sub_le _ _).trans <| (add_le_add (c₁.norm_coe_le_norm _) (c₀.norm_coe_le_norm _)).trans (by linarith)
  calc
    _ ≤ M*B*‖f‖ := mul_le_mul (mul_le_mul hn (hbound _) (norm_nonneg _) hM)
      (apply_norm_le f _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma continuous_residual_comp {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (g : C(P × V,ℂ)) (a : X → V →ᵇ P) (c₀ c₁ : X → V →ᵇ ℂ)
    (r : X → ℝ) (f : C₀(V,ℂ)) (ha : Continuous a) (h₀ : Continuous c₀) (h₁ : Continuous c₁)
    (hr : Continuous r) (B : V → ℝ) (hB : Integrable B) (hBn : ∀ y, 0 ≤ B y)
    (hbound : ∀ p y, ‖g (p,y)‖ ≤ B y) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ x, ‖c₀ x‖+‖c₁ x‖ ≤ M) :
    Continuous (fun x => residual g (a x).toContinuousMap (c₀ x) (c₁ x) (r x) f) := by
  apply continuous_of_dominated
    (fun x => (integrable_residualData g (a x).toContinuousMap (c₀ x) (c₁ x) (r x) f B hB hBn hbound).aestronglyMeasurable)
    (fun x => Eventually.of_forall (fun y => norm_residualData_le_uniform g (a x).toContinuousMap
      (c₀ x) (c₁ x) (r x) f y (B y) M (hBn y) hM (fun p => hbound p y) (hc x)))
    (hB.const_mul (M*‖f‖))
  exact Eventually.of_forall (fun y => continuous_residualData_comp g a c₀ c₁ r
    (fun _ => f) (fun _ => y) ha h₀ h₁ hr continuous_const continuous_const)

lemma residual_add (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (f h : C₀(V,ℂ)) (B : V → ℝ) (hB : Integrable B)
    (hBn : ∀ y, 0 ≤ B y) (hbound : ∀ p y, ‖g (p,y)‖ ≤ B y) :
    residual g a c₀ c₁ r (f+h) = residual g a c₀ c₁ r f + residual g a c₀ c₁ r h := by
  have he : residualData g a c₀ c₁ r (f+h) =
      fun y => residualData g a c₀ c₁ r f y + residualData g a c₀ c₁ r h y := by
    funext y
    ext x
    simp only [residualData_apply, ZeroAtInftyContinuousMap.add_apply]
    ring
  rw [residual, he, integral_add
    (integrable_residualData g a c₀ c₁ r f B hB hBn hbound)
    (integrable_residualData g a c₀ c₁ r h B hB hBn hbound)]
  rfl

omit [BorelSpace V] [SecondCountableTopology V] in
lemma residual_smul (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (c : ℂ) (f : C₀(V,ℂ)) :
    residual g a c₀ c₁ r (c • f) = c • residual g a c₀ c₁ r f := by
  have he : residualData g a c₀ c₁ r (c • f) = fun y => c • residualData g a c₀ c₁ r f y := by
    funext y
    ext x
    simp only [residualData_apply, ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
    ring
  rw [residual, he, integral_smul]
  rfl

omit [BorelSpace V] [SecondCountableTopology V] in
lemma norm_residual_le_uniform (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (f : C₀(V,ℂ)) (B : V → ℝ) (hB : Integrable B)
    (hBn : ∀ y, 0 ≤ B y) (hbound : ∀ p y, ‖g (p,y)‖ ≤ B y) :
    ‖residual g a c₀ c₁ r f‖ ≤ ((‖c₀‖+‖c₁‖)*(∫ y, B y))*‖f‖ := by
  calc
    _ ≤ ∫ y, (‖c₀‖+‖c₁‖)*‖f‖*B y := norm_integral_le_of_norm_le
      (hB.const_mul _) (Eventually.of_forall (fun y => norm_residualData_le_uniform g a c₀ c₁ r f y
        (B y) (‖c₀‖+‖c₁‖) (hBn y) (by positivity) (fun p => hbound p y) le_rfl))
    _ = _ := by rw [integral_const_mul]; ring

def residualCLM (g : C(P × V,ℂ)) (a : C(V,P)) (c₀ c₁ : V →ᵇ ℂ)
    (r : ℝ) (B : V → ℝ) (hB : Integrable B) (hBn : ∀ y, 0 ≤ B y)
    (hbound : ∀ p y, ‖g (p,y)‖ ≤ B y) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  LinearMap.mkContinuous
    { toFun := residual g a c₀ c₁ r
      map_add' := fun f h => residual_add g a c₀ c₁ r f h B hB hBn hbound
      map_smul' := fun c f => residual_smul g a c₀ c₁ r c f }
    ((‖c₀‖+‖c₁‖)*(∫ y, B y))
    (fun f => norm_residual_le_uniform g a c₀ c₁ r f B hB hBn hbound)

end FrozenFamily

namespace FrozenParametrix
open scoped SchwartzMap ZeroAtInfty BoundedContinuousFunction
open BiharmonicKernel C0Convolution
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def frozenOp {α β : ℝ} (hα : 0 < α) (a : C(V,Icc α β)) (r : ℝ) (f : C₀(V,ℂ)) : C₀(V,ℂ) :=
  frozen (fun x => (a x).val) (continuous_subtype_val.comp a.continuous) α β hα
    (fun x => (a x).property) r f

lemma kernel_majorant_nonneg (α β : ℝ) (hα : 0 < α) :
    ∃ B : V → ℝ, Integrable B ∧ (∀ y, 0 ≤ B y) ∧
      ∀ t ∈ Icc α β, ∀ y : V, ‖kernel t y‖ ≤ B y := by
  obtain ⟨B,hB,hbound⟩ := kernel_majorant (V := V) α β hα
  exact ⟨fun y => |B y|, hB.norm, fun y => abs_nonneg _,
    fun t ht y => (hbound t ht y).trans (le_abs_self _)⟩

def kernelMajorant (α β : ℝ) (hα : 0 < α) : V → ℝ :=
  (kernel_majorant_nonneg (V := V) α β hα).choose
lemma kernelMajorant_spec (α β : ℝ) (hα : 0 < α) :
    Integrable (kernelMajorant (V := V) α β hα) ∧
    (∀ y, 0 ≤ kernelMajorant (V := V) α β hα y) ∧
    ∀ t ∈ Icc α β, ∀ y : V, ‖kernel t y‖ ≤ kernelMajorant α β hα y :=
  (kernel_majorant_nonneg (V := V) α β hα).choose_spec

def frozenCLM {α β : ℝ} (hα : 0 < α) (a : C(V,Icc α β)) (r : ℝ) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  LinearMap.mkContinuous
    { toFun := frozenOp hα a r
      map_add' := fun f g => frozen_add (fun x => (a x).val) (continuous_subtype_val.comp a.continuous) α β hα (fun x => (a x).property) r f g
      map_smul' := fun c f => frozen_smul (fun x => (a x).val) (continuous_subtype_val.comp a.continuous) α β hα (fun x => (a x).property) r c f }
    (∫ y : V, kernelMajorant α β hα y)
    (fun f => norm_frozen_le (fun x => (a x).val) (continuous_subtype_val.comp a.continuous) α β hα (fun x => (a x).property) r f _
      (kernelMajorant_spec α β hα).1 (kernelMajorant_spec α β hα).2.2)

@[simp] lemma frozenCLM_apply {α β : ℝ} (hα : 0 < α) (a : C(V,Icc α β)) (r : ℝ) (f : C₀(V,ℂ)) :
    frozenCLM hα a r f = frozenOp hα a r f := rfl

lemma norm_frozenCLM_le {α β : ℝ} (hα : 0 < α) (a : C(V,Icc α β)) (r : ℝ) :
    ‖frozenCLM hα a r‖ ≤ ∫ y : V, kernelMajorant α β hα y := by
  apply ContinuousLinearMap.opNorm_le_bound (frozenCLM hα a r)
    (integral_nonneg (kernelMajorant_spec α β hα).2.1)
  intro f
  exact norm_frozen_le (fun x => (a x).val) (continuous_subtype_val.comp a.continuous) α β hα (fun x => (a x).property) r f _
    (kernelMajorant_spec α β hα).1 (kernelMajorant_spec α β hα).2.2

def kernelFamilyCM (α β : ℝ) (hα : 0 < α) : C(Icc α β × V,ℂ) :=
  ⟨fun p => kernel p.1.val p.2,
    continuous_kernel_comp (fun p : Icc α β × V => p.1.val) Prod.snd
      (continuous_subtype_val.comp continuous_fst) continuous_snd
      (fun p => hα.trans_le p.1.property.1)⟩

lemma continuous_frozenOp_comp {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {α β : ℝ} (hα : 0 < α) (a : X → V →ᵇ Icc α β) (r : X → ℝ)
    (ha : Continuous a) (hr : Continuous r) (f : C₀(V,ℂ)) :
    Continuous (fun x => frozenOp hα (a x).toContinuousMap (r x) f) := by
  have he (x : X) : frozenOp hα (a x).toContinuousMap (r x) f =
      ∫ y : V, C0Convolution.translate (r x • y) (FrozenFamily.data (kernelFamilyCM α β hα) (a x).toContinuousMap f y) :=
    frozen_eq_integral (fun z => (a x z).val) (continuous_subtype_val.comp (a x).continuous) α β hα (fun z => (a x z).property) (r x) f
  simp_rw [he]
  apply continuous_of_dominated (bound := fun y => kernelMajorant α β hα y*‖f‖)
  · intro x
    exact (integrable_translated_sourceData (fun z => (a x z).val) (continuous_subtype_val.comp (a x).continuous) α β hα (fun z => (a x z).property) (r x) f).aestronglyMeasurable
  · intro x
    filter_upwards with y
    rw [norm_translate]
    exact FrozenFamily.norm_data_le (kernelFamilyCM α β hα) (a x).toContinuousMap f y (kernelMajorant α β hα y) ((kernelMajorant_spec α β hα).2.1 y)
      (fun p => (kernelMajorant_spec α β hα).2.2 p.val p.property y)
  · exact (kernelMajorant_spec α β hα).1.mul_const ‖f‖
  · exact Eventually.of_forall (fun y => continuous_translate_comp _ _
      (hr.smul continuous_const) (FrozenFamily.continuous_data_comp (kernelFamilyCM α β hα)
        a (fun _ => f) (fun _ => y) ha continuous_const continuous_const))

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma continuous_coefficient_comp {X : Type*} [TopologicalSpace X] {α β : ℝ}
    (a : X → V →ᵇ Icc α β) (ha : Continuous a) :
    Continuous (fun x => coefficient (a x).toContinuousMap) := by
  exact CompactComposition.continuous_compose.comp (continuous_const.prodMk ha)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma norm_coefficient_le {α β : ℝ} (a : C(V,Icc α β)) :
    ‖coefficient a‖ ≤ max |α| |β| := by
  apply (BoundedContinuousFunction.norm_le (le_trans (abs_nonneg α) (le_max_left _ _))).mpr
  intro x
  simp only [coefficient_apply, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  exact ⟨(neg_le_neg (le_max_left |α| |β|)).trans ((neg_abs_le α).trans (a x).property.1),
    (a x).property.2.trans ((le_abs_self β).trans (le_max_right _ _))⟩

def bilapMajorant (α β : ℝ) (hα : 0 < α) : V → ℝ :=
  (bilapKernel_weighted_majorant (V := V) α β hα).choose
lemma bilapMajorant_spec (α β : ℝ) (hα : 0 < α) :
    Integrable (bilapMajorant (V := V) α β hα) ∧
    Integrable (fun y : V => (1+‖y‖)*bilapMajorant α β hα y) ∧
    (∀ y, 0 ≤ bilapMajorant (V := V) α β hα y) ∧
    ∀ t ∈ Icc α β, ∀ y : V, ‖bilapKernel t y‖ ≤ bilapMajorant α β hα y :=
  (bilapKernel_weighted_majorant (V := V) α β hα).choose_spec

def principalCLM {α β : ℝ} (hα : 0 < α) (a₀ a₁ : C(V,Icc α β)) (r : ℝ) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  (r⁻¹)^4 • FrozenFamily.residualCLM (bilapFamily α β hα) a₀
    (coefficient a₀) (coefficient a₁) r (bilapMajorant α β hα)
    (bilapMajorant_spec α β hα).1 (bilapMajorant_spec α β hα).2.2.1
    (fun p y => (bilapMajorant_spec α β hα).2.2.2 p.val p.property y)

@[simp] lemma principalCLM_apply {α β : ℝ} (hα : 0 < α) (a₀ a₁ : C(V,Icc α β)) (r : ℝ) (f : C₀(V,ℂ)) :
    principalCLM hα a₀ a₁ r f = principalResidual hα a₀ a₁ r f := rfl

lemma continuous_principalCLM_apply {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {α β : ℝ} (hα : 0 < α) (a₀ a₁ : X → V →ᵇ Icc α β) (r : X → ℝ)
    (h₀ : Continuous a₀) (h₁ : Continuous a₁) (hr : Continuous r) (hr0 : ∀ x, r x ≠ 0) (f : C₀(V,ℂ)) :
    Continuous (fun x => principalCLM hα (a₀ x).toContinuousMap (a₁ x).toContinuousMap (r x) f) := by
  change Continuous (fun x => (r x)⁻¹^4 • FrozenFamily.residual (bilapFamily α β hα)
    (a₀ x).toContinuousMap (coefficient (a₀ x).toContinuousMap) (coefficient (a₁ x).toContinuousMap) (r x) f)
  apply ((hr.inv₀ hr0).pow 4).smul
  apply FrozenFamily.continuous_residual_comp _ a₀ _ _ r f h₀
    (continuous_coefficient_comp a₀ h₀) (continuous_coefficient_comp a₁ h₁) hr
    (bilapMajorant α β hα) (bilapMajorant_spec α β hα).1 (bilapMajorant_spec α β hα).2.2.1
    (fun p y => (bilapMajorant_spec α β hα).2.2.2 p.val p.property y)
    (2*max |α| |β|) (by positivity)
  intro x
  linarith [norm_coefficient_le (a₀ x).toContinuousMap, norm_coefficient_le (a₁ x).toContinuousMap]


def fullResidualCLM {α β : ℝ} (hα : 0 < α) (a₀ a₁ : C(V,Icc α β)) (b : V →ᵇ ℂ)
    (r : ℝ) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  principalCLM hα a₀ a₁ r + (C0Multiplier.mulLeftCLM b).comp (frozenCLM hα a₀ r)

lemma fullResidualCLM_apply {α β : ℝ} (hα : 0 < α) (a₀ a₁ : C(V,Icc α β)) (b : V →ᵇ ℂ)
    (r : ℝ) (f : C₀(V,ℂ)) :
    fullResidualCLM hα a₀ a₁ b r f = principalResidual hα a₀ a₁ r f + C0Multiplier.mul b (frozenOp hα a₀ r f) := rfl

lemma continuous_fullResidualCLM_apply {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {α β : ℝ} (hα : 0 < α) (a₀ a₁ : X → V →ᵇ Icc α β) (b : X → V →ᵇ ℂ) (r : X → ℝ)
    (h₀ : Continuous a₀) (h₁ : Continuous a₁) (hb : Continuous b)
    (hr : Continuous r) (hr0 : ∀ x, r x ≠ 0) (f : C₀(V,ℂ)) :
    Continuous (fun x => fullResidualCLM hα (a₀ x).toContinuousMap (a₁ x).toContinuousMap (b x) (r x) f) := by
  simp_rw [fullResidualCLM_apply]
  exact (continuous_principalCLM_apply hα a₀ a₁ r h₀ h₁ hr hr0 f).add
    (C0Multiplier.continuous_mul_joint.comp (hb.prodMk (continuous_frozenOp_comp hα a₀ r h₀ hr f)))

lemma exists_uniform_fullResidual_bound (α β : ℝ) (hα : 0 < α) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a₀ a₁ : C(V,Icc α β)) (b : V →ᵇ ℂ) (r : ℝ),
      0 < r → r ≤ 1 → ‖b‖ ≤ B →
      (∀ x z, |(a₁ x).val-(a₀ z).val| ≤ L*(‖x-z‖+r^4)) →
      ‖fullResidualCLM hα a₀ a₁ b r‖ ≤ C*(r⁻¹)^3 := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_principalResidual_bound (V := V) α β hα L hL
  let M := ∫ y : V, kernelMajorant α β hα y
  have hM : 0 ≤ M := integral_nonneg (kernelMajorant_spec α β hα).2.1
  refine ⟨C+B*M,by positivity,fun a₀ a₁ b r hr hr1 hb hLip => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [fullResidualCLM_apply]
  have hrinv : 1 ≤ (r⁻¹)^3 := one_le_pow₀ ((one_le_inv₀ hr).mpr hr1)
  have hK : ‖frozenOp hα a₀ r f‖ ≤ M*‖f‖ := by
    exact norm_frozen_le (fun x => (a₀ x).val) (continuous_subtype_val.comp a₀.continuous)
      α β hα (fun x => (a₀ x).property) r f _
      (kernelMajorant_spec α β hα).1 (kernelMajorant_spec α β hα).2.2
  calc
    _ ≤ ‖principalResidual hα a₀ a₁ r f‖+‖C0Multiplier.mul b (frozenOp hα a₀ r f)‖ := norm_add_le _ _
    _ ≤ C*(r⁻¹)^3*‖f‖+B*(M*‖f‖) := add_le_add (hbound a₀ a₁ r hr hr1 hLip f)
      ((C0Multiplier.norm_mul_le b _).trans (mul_le_mul hb hK (norm_nonneg _) hB))
    _ ≤ C*(r⁻¹)^3*‖f‖+B*(M*‖f‖)*(r⁻¹)^3 :=
      add_le_add le_rfl (le_mul_of_one_le_right (show 0 ≤ B*(M*‖f‖) by positivity) hrinv)
    _ = _ := by ring

end FrozenParametrix

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace StrongWeightedVolterra

abbrev UnitTime := Ioo (0 : ℝ) 1
abbrev Time (T : ℝ) := Ioc (0 : ℝ) T

instance : MeasureSpace UnitTime := Measure.Subtype.measureSpace

def weight (u : UnitTime) : ℝ := u.val ^ (-3/4 : ℝ) * (1-u.val)^(-3/4 : ℝ)

lemma weight_nonneg (u : UnitTime) : 0 ≤ weight u := by
  exact mul_nonneg (Real.rpow_nonneg u.property.1.le _) (Real.rpow_nonneg (by linarith [u.property.2]) _)

lemma continuous_weight : Continuous weight := by
  apply Continuous.mul
  · exact continuous_subtype_val.rpow_const (fun u => Or.inl u.property.1.ne')
  · exact (continuous_const.sub continuous_subtype_val).rpow_const
      (fun u => Or.inl (sub_pos.mpr u.property.2).ne')

lemma integrable_weight : Integrable weight := by
  have hb := (Complex.betaIntegral_convergent
    (u := (1/4 : ℂ)) (v := (1/4 : ℂ)) (by norm_num) (by norm_num)).norm.1
  have hi := hb.mono_set Ioo_subset_Ioc_self
  have he : EqOn (fun x : ℝ => ‖(x : ℂ)^((1/4 : ℂ)-1) *
      (1-(x : ℂ))^((1/4 : ℂ)-1)‖)
      (fun x : ℝ => x^(-3/4 : ℝ)*(1-x)^(-3/4 : ℝ)) (Ioo 0 1) := by
    intro x hx
    dsimp only
    rw [norm_mul]
    have hq : (1/4 : ℂ)-1 = ((-3/4 : ℝ) : ℂ) := by norm_num
    rw [hq, show (1 : ℂ)-(x : ℂ) = ((1-x : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_real, Complex.norm_cpow_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hx.1, abs_of_pos (sub_pos.mpr hx.2)]
  have hw := hi.congr_fun he measurableSet_Ioo
  exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp hw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {T : ℝ}

def lag (t : Time T) (u : UnitTime) : Time T :=
  ⟨t.val*u.val, mul_pos t.property.1 u.property.1,
    (mul_le_of_le_one_right t.property.1.le u.property.2.le).trans t.property.2⟩

lemma continuous_lag : Continuous (fun p : Time T × UnitTime => lag p.1 p.2) := by
  exact (continuous_subtype_val.comp continuous_fst |>.mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

structure Kernel (T : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where
  toFun : Time T × UnitTime → E →L[ℂ] E
  continuous_apply : Continuous (fun p : (Time T × UnitTime) × E => toFun p.1 p.2)

instance : CoeFun (Kernel T E) (fun _ => Time T × UnitTime → E →L[ℂ] E) := ⟨Kernel.toFun⟩

lemma continuous_apply_of_strong {X : Type*} [TopologicalSpace X]
    (A : X → E →L[ℂ] E) (hA : ∀ f, Continuous (fun x => A x f))
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ x, ‖A x‖ ≤ C) :
    Continuous (fun p : X × E => A p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨x,f⟩
  have hb := ((hA f).comp continuous_fst).tendsto (x,f)
  apply hb.congr_dist
  apply squeeze_zero (fun p => dist_nonneg) (fun p => ?_)
    (show Tendsto (fun p : X × E => C*dist f p.2) (𝓝 (x,f)) (𝓝 0) from
      by
        have hd : Continuous (fun p : X × E => C*dist f p.2) := by fun_prop
        simpa using hd.tendsto (x,f))
  dsimp only [Function.comp_apply]
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact (A p.1).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _))

def Kernel.ofStrong (A : Time T × UnitTime → E →L[ℂ] E)
    (hA : ∀ f, Continuous (fun p => A p f)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p, ‖A p‖ ≤ C) : Kernel T E :=
  ⟨A, continuous_apply_of_strong A hA C hC hbound⟩

variable (N : Kernel T E) (C : ℝ)
    (hC : 0 ≤ C) (hN : ∀ p, ‖N p‖ ≤ C)

def data (j : Time T →ᵇ E) (t : Time T) (u : UnitTime) : E :=
  weight u • N (t,u) (j (lag t u))

lemma continuous_data (j : Time T →ᵇ E) :
    Continuous (fun p : Time T × UnitTime => data N j p.1 p.2) := by
  exact (continuous_weight.comp continuous_snd).smul
    (N.continuous_apply.comp (continuous_id.prodMk (j.continuous.comp continuous_lag)))

include hC hN

lemma norm_data_le (j : Time T →ᵇ E) (t : Time T) (u : UnitTime) :
    ‖data N j t u‖ ≤ weight u * (C*‖j‖) := by
  rw [data, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg u)]
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg u)
  exact (N (t,u)).le_opNorm _ |>.trans (mul_le_mul (hN _) (j.norm_coe_le_norm _)
    (norm_nonneg _) hC)

lemma integrable_data (j : Time T →ᵇ E) (t : Time T) : Integrable (data N j t) := by
  exact (integrable_weight.mul_const (C*‖j‖)).mono'
    ((continuous_data N j).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Eventually.of_forall (norm_data_le N C hC hN j t))

lemma continuous_integral_data (j : Time T →ᵇ E) :
    Continuous (fun t => ∫ u : UnitTime, data N j t u) := by
  apply continuous_of_dominated
    (fun t => (integrable_data N C hC hN j t).aestronglyMeasurable)
    (fun t => Eventually.of_forall (norm_data_le N C hC hN j t))
    (integrable_weight.mul_const (C*‖j‖))
  exact Eventually.of_forall (fun u =>
    (continuous_data N j).comp (continuous_id.prodMk continuous_const))

lemma norm_integral_data_le (j : Time T →ᵇ E) (t : Time T) :
    ‖∫ u : UnitTime, data N j t u‖ ≤ (∫ u : UnitTime, weight u)*C*‖j‖ := by
  calc
    _ ≤ ∫ u : UnitTime, weight u*(C*‖j‖) :=
      norm_integral_le_of_norm_le (integrable_weight.mul_const _) <|
        Eventually.of_forall (norm_data_le N C hC hN j t)
    _ = _ := by rw [integral_mul_const]; ring

omit hC hN in
def value (j : Time T →ᵇ E) (t : Time T) : E :=
  t.val^(1/4 : ℝ) • ∫ u : UnitTime, data N j t u

lemma continuous_value (j : Time T →ᵇ E) : Continuous (value N j) :=
  (continuous_subtype_val.rpow_const (fun t => Or.inl t.property.1.ne')).smul
    (continuous_integral_data N C hC hN j)

lemma norm_value_le (hT : 0 ≤ T) (j : Time T →ᵇ E) (t : Time T) :
    ‖value N j t‖ ≤ (T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C)*‖j‖ := by
  rw [value, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg t.property.1.le _)]
  calc
    _ ≤ T^(1/4 : ℝ) * ((∫ u : UnitTime, weight u)*C*‖j‖) :=
      mul_le_mul (Real.rpow_le_rpow t.property.1.le t.property.2 (by norm_num))
        (norm_integral_data_le N C hC hN j t) (norm_nonneg _)
        (Real.rpow_nonneg hT _)
    _ = _ := by ring

def operator (hT : 0 ≤ T) (j : Time T →ᵇ E) : Time T →ᵇ E :=
  .mkOfBound ⟨value N j, continuous_value N C hC hN j⟩
    (2*((T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C)*‖j‖)) (by
      intro x y
      exact (dist_le_norm_add_norm _ _).trans <| by
        dsimp
        linarith [norm_value_le N C hC hN hT j x, norm_value_le N C hC hN hT j y])

@[simp] lemma operator_apply (hT : 0 ≤ T) (j : Time T →ᵇ E) (t : Time T) :
    operator N C hC hN hT j t = value N j t := rfl

lemma norm_operator_le (hT : 0 ≤ T) (j : Time T →ᵇ E) :
    ‖operator N C hC hN hT j‖ ≤ (T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C)*‖j‖ := by
  apply (BoundedContinuousFunction.norm_le (by
    apply mul_nonneg _ (norm_nonneg _)
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hT _) (integral_nonneg weight_nonneg)) hC)).mpr
  exact norm_value_le N C hC hN hT j

lemma operator_add (hT : 0 ≤ T) (j k : Time T →ᵇ E) :
    operator N C hC hN hT (j+k) = operator N C hC hN hT j + operator N C hC hN hT k := by
  ext t
  simp only [operator_apply, BoundedContinuousFunction.add_apply, value]
  have hd : (fun u => data N (j+k) t u) = (fun u => data N j t u+data N k t u) := by
    funext u
    simp [data, map_add, smul_add]
  rw [hd, integral_add (integrable_data N C hC hN j t) (integrable_data N C hC hN k t), smul_add]

lemma operator_smul (hT : 0 ≤ T) (c : ℂ) (j : Time T →ᵇ E) :
    operator N C hC hN hT (c • j) = c • operator N C hC hN hT j := by
  ext t
  simp only [operator_apply, BoundedContinuousFunction.smul_apply, value]
  have hd : (fun u => data N (c • j) t u) = (fun u => c • data N j t u) := by
    funext u
    simp only [data, BoundedContinuousFunction.smul_apply, map_smul]
    exact smul_comm _ _ _
  rw [hd, integral_smul, smul_comm]

def operatorCLM (hT : 0 ≤ T) : (Time T →ᵇ E) →L[ℂ] (Time T →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := operator N C hC hN hT
      map_add' := operator_add N C hC hN hT
      map_smul' := operator_smul N C hC hN hT }
    (T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C)
    (norm_operator_le N C hC hN hT)

lemma norm_operatorCLM_le (hT : 0 ≤ T) :
    ‖operatorCLM N C hC hN hT‖ ≤ T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hT _) (integral_nonneg weight_nonneg)) hC)
  exact norm_operator_le N C hC hN hT

theorem exists_unique_solution [CompleteSpace E] (hT : 0 ≤ T)
    (hsmall : T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C < 1) (g : Time T →ᵇ E) :
    ∃! j : Time T →ᵇ E, j + operator N C hC hN hT j = g := by
  let A := operatorCLM N C hC hN hT
  have hA : ‖A‖ < 1 := (norm_operatorCLM_le N C hC hN hT).trans_lt hsmall
  let f : (Time T →ᵇ E) → (Time T →ᵇ E) := fun j => g-A j
  have hf : ContractingWith ‖A‖₊ f := by
    refine ⟨hA, LipschitzWith.of_dist_le_mul (fun j k => ?_)⟩
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(g-A j)-(g-A k)‖ ≤ ‖A‖*‖j-k‖
    rw [sub_sub_sub_cancel_left, ← A.map_sub, norm_sub_rev j k]
    exact A.le_opNorm (k-j)
  refine ⟨hf.fixedPoint, ?_, fun j hj => ?_⟩
  · have hx := hf.fixedPoint_isFixedPt
    change g-A hf.fixedPoint = hf.fixedPoint at hx
    change hf.fixedPoint + A hf.fixedPoint = g
    exact (eq_sub_iff_add_eq.mp hx.symm)
  · apply hf.fixedPoint_unique
    change g-A j = j
    change j + A j = g at hj
    exact (eq_sub_iff_add_eq.mpr hj).symm

lemma norm_solution_le (hT : 0 ≤ T)
    (hsmall : T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C < 1)
    (g j : Time T →ᵇ E) (hj : j+operator N C hC hN hT j=g) :
    ‖j‖ ≤ ‖g‖/(1-T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C) := by
  have hpos := sub_pos.mpr hsmall
  apply (le_div_iff₀ hpos).mpr
  have hb := norm_operator_le N C hC hN hT j
  have hjg : j = g-operator N C hC hN hT j := eq_sub_iff_add_eq.mpr hj
  have hn := norm_sub_le g (operator N C hC hN hT j)
  rw [← hjg] at hn
  nlinarith

omit hC hN in

def unweighted (j : Time T →ᵇ E) (r : ℝ) : E :=
  if hr : r ∈ Time T then r^(-3/4 : ℝ) • j ⟨r,hr⟩ else 0

omit hC hN in
lemma unweighted_lag (j : Time T →ᵇ E) (t : Time T) (u : UnitTime) :
    unweighted j (t.val*u.val) = (t.val*u.val)^(-3/4 : ℝ) • j (lag t u) := by
  have hr : t.val*u.val ∈ Time T := (lag t u).property
  rw [unweighted, dite_eq_left hr]
  rfl

omit hC hN in
def normalizedArg (t : Time T) (r : ℝ) (hr : r ∈ Ioo 0 t.val) : UnitTime :=
  ⟨r/t.val, div_pos hr.1 t.property.1, (div_lt_one t.property.1).mpr hr.2⟩

omit hC hN in

def kernel (t : Time T) (r : ℝ) : E →L[ℂ] E :=
  if hr : r ∈ Ioo 0 t.val then
    (t.val-r)^(-3/4 : ℝ) • N (t,normalizedArg t r hr) else 0

omit hC hN in
lemma normalizedArg_lag (t : Time T) (u : UnitTime)
    (hr : t.val*u.val ∈ Ioo 0 t.val) : normalizedArg t (t.val*u.val) hr = u := by
  apply Subtype.ext
  change t.val*u.val/t.val = u.val
  field_simp [t.property.1.ne']

omit hC hN in
lemma kernel_lag (t : Time T) (u : UnitTime) :
    kernel N t (t.val*u.val) = (t.val*(1-u.val))^(-3/4 : ℝ) • N (t,u) := by
  have hr : t.val*u.val ∈ Ioo 0 t.val :=
    ⟨mul_pos t.property.1 u.property.1, mul_lt_of_lt_one_right t.property.1 u.property.2⟩
  rw [kernel, dite_eq_left hr, normalizedArg_lag]
  congr 2
  ring

omit hC hN in
lemma rescaling_scalar (t u : ℝ) (ht : 0 < t) (hu : 0 < u) (hu1 : u < 1) :
    t^(3/4 : ℝ)*t*((t*(1-u))^(-3/4 : ℝ)*(t*u)^(-3/4 : ℝ)) =
      t^(1/4 : ℝ)*(u^(-3/4 : ℝ)*(1-u)^(-3/4 : ℝ)) := by
  rw [Real.mul_rpow ht.le (sub_pos.mpr hu1).le, Real.mul_rpow ht.le hu.le]
  have hprod : t^(3/4 : ℝ)*t*t^(-3/4 : ℝ)*t^(-3/4 : ℝ) = t^(1/4 : ℝ) := by
    calc
      _ = t^(3/4 : ℝ)*t^(1 : ℝ)*t^(-3/4 : ℝ)*t^(-3/4 : ℝ) := by rw [Real.rpow_one]
      _ = t^((3/4:ℝ)+1+(-3/4)+(-3/4)) := by rw [Real.rpow_add ht, Real.rpow_add ht, Real.rpow_add ht]
      _ = _ := by norm_num
  calc
    _ = (t^(3/4 : ℝ)*t*t^(-3/4 : ℝ)*t^(-3/4 : ℝ))*
      (u^(-3/4 : ℝ)*(1-u)^(-3/4 : ℝ)) := by ring
    _ = _ := by rw [hprod]

omit hC hN in

lemma value_eq_volterra (j : Time T →ᵇ E) (t : Time T) :
    value N j t = t.val^(3/4 : ℝ) •
      ∫ r in 0..t.val, kernel N t r (unweighted j r) := by
  let F : ℝ → E := fun r => kernel N t r (unweighted j r)
  have hc := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) F t.val
  simp only [mul_zero, mul_one] at hc
  change value N j t = t.val^(3/4 : ℝ) • ∫ r in 0..t.val, F r
  rw [← hc, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, ← integral_subtype measurableSet_Ioo]
  rw [← integral_smul, ← integral_smul]
  unfold value
  rw [← integral_smul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  dsimp [F]
  rw [kernel_lag, unweighted_lag, smul_apply, ContinuousLinearMap.map_smul_of_tower]
  simp only [data, smul_smul]
  congr 1
  simpa only [weight, mul_assoc] using
    (rescaling_scalar t.val u.val t.property.1 u.property.1 u.property.2).symm

omit hC hN in
lemma unweighted_at_time (j : Time T →ᵇ E) (t : Time T) :
    unweighted j t.val = t.val^(-3/4 : ℝ) • j t := by
  rw [unweighted, dite_eq_left t.property]

omit hC hN in
lemma kernel_unweighted_lag (j : Time T →ᵇ E) (t : Time T) (u : UnitTime) :
    kernel N t (t.val*u.val) (unweighted j (t.val*u.val)) =
      (t.val^(-3/4 : ℝ)*t.val^(-3/4 : ℝ)) • data N j t u := by
  rw [kernel_lag, unweighted_lag, smul_apply, ContinuousLinearMap.map_smul_of_tower]
  simp only [data, smul_smul]
  congr 1
  rw [Real.mul_rpow t.property.1.le (sub_pos.mpr u.property.2).le,
    Real.mul_rpow t.property.1.le u.property.1.le, weight]
  ring

lemma intervalIntegrable_kernel_unweighted (j : Time T →ᵇ E) (t : Time T) :
    IntervalIntegrable (fun r => kernel N t r (unweighted j r)) volume 0 t.val := by
  have hi : Integrable (fun u : UnitTime =>
      kernel N t (t.val*u.val) (unweighted j (t.val*u.val))) := by
    simp_rw [kernel_unweighted_lag]
    exact (integrable_data N C hC hN j t).smul _
  have hs : IntegrableOn (fun u : ℝ =>
      kernel N t (t.val*u) (unweighted j (t.val*u))) (Ioo 0 1) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mpr hi
  have hii := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr hs
  apply (IntervalIntegrable.comp_mul_left_iff (a := 0) (b := t.val) t.property.1.ne').mp
  simpa only [zero_div, div_self t.property.1.ne'] using hii

lemma unweighted_solves (hT : 0 ≤ T) (g j : Time T →ᵇ E)
    (hj : j+operator N C hC hN hT j=g) (t : Time T) :
    unweighted j t.val + ∫ r in 0..t.val, kernel N t r (unweighted j r) =
      unweighted g t.val := by
  have ht : t.val^(-3/4 : ℝ)*t.val^(3/4 : ℝ)=1 := by
    rw [← Real.rpow_add t.property.1]
    norm_num
  have he : j t+value N j t=g t := congrArg (fun k : Time T →ᵇ E => k t) hj
  rw [unweighted_at_time, unweighted_at_time]
  calc
    _ = t.val^(-3/4 : ℝ) • (j t+value N j t) := by
      rw [smul_add, value_eq_volterra, smul_smul, ht, one_smul]
    _ = _ := by rw [he]

theorem exists_unweighted_solution [CompleteSpace E] (hT : 0 ≤ T)
    (hsmall : T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C < 1)
    (g : Time T →ᵇ E) :
    ∃ j : Time T →ᵇ E,
      (∀ t : Time T, IntervalIntegrable (fun r => kernel N t r (unweighted j r)) volume 0 t.val) ∧
      (∀ t : Time T, unweighted j t.val +
        ∫ r in 0..t.val, kernel N t r (unweighted j r) = unweighted g t.val) ∧
      (∀ t : Time T, ‖unweighted j t.val‖ ≤ t.val^(-3/4 : ℝ) *
        (‖g‖/(1-T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C))) := by
  obtain ⟨j,hj,_⟩ := exists_unique_solution N C hC hN hT hsmall g
  refine ⟨j, intervalIntegrable_kernel_unweighted N C hC hN j,
    unweighted_solves N C hC hN hT g j hj, fun t => ?_⟩
  rw [unweighted_at_time, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg t.property.1.le _)]
  exact mul_le_mul_of_nonneg_left
    ((j.norm_coe_le_norm t).trans (norm_solution_le N C hC hN hT hsmall g j hj))
    (Real.rpow_nonneg t.property.1.le _)

end StrongWeightedVolterra

open Set Filter
open scoped Topology
namespace ParabolicRadius

def radius (q : ℝ) : ℝ := q^(1/4 : ℝ)

lemma pos {q : ℝ} (hq : 0 < q) : 0 < radius q := Real.rpow_pos_of_pos hq _
lemma nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ radius q := Real.rpow_nonneg hq _
lemma pow_four {q : ℝ} (hq : 0 ≤ q) : radius q ^ 4 = q := by
  rw [radius, ← Real.rpow_natCast, ← Real.rpow_mul hq]
  norm_num
lemma pow_three {q : ℝ} (hq : 0 ≤ q) : radius q ^ 3 = q^(3/4 : ℝ) := by
  rw [radius, ← Real.rpow_natCast, ← Real.rpow_mul hq]
  norm_num
lemma inv_pow_three {q : ℝ} (hq : 0 ≤ q) : (radius q)⁻¹ ^ 3 = q^(-3/4 : ℝ) := by
  rw [inv_pow, pow_three hq, ← Real.rpow_neg hq]
  congr 1
  norm_num
lemma le_one {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) : radius q ≤ 1 :=
  Real.rpow_le_one hq hq1 (by positivity)
lemma continuous_comp {X : Type*} [TopologicalSpace X] (q : X → ℝ)
    (hq : Continuous q) : Continuous (fun x => radius (q x)) :=
  hq.rpow_const (fun _ => Or.inr (by positivity))
lemma normalized_cancel {q : ℝ} (hq : 0 < q) :
    q^(-3/4 : ℝ)*radius q^3=1 := by
  rw [pow_three hq.le, ← Real.rpow_add hq]
  norm_num
end ParabolicRadius

namespace ParametrixVolterra
section Slab
open scoped ZeroAtInfty BoundedContinuousFunction
open FrozenParametrix C0Convolution
open StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}

abbrev Slab (T : ℝ) := Icc (0 : ℝ) T

def now (t : Time T) : Slab T := ⟨t.val,t.property.1.le,t.property.2⟩
def before (p : Time T × UnitTime) : Slab T := now (lag p.1 p.2)
def elapsed (p : Time T × UnitTime) : ℝ := p.1.val*(1-p.2.val)

lemma continuous_now : Continuous (now : Time T → Slab T) := continuous_subtype_val.subtype_mk _
lemma continuous_before : Continuous (before : Time T × UnitTime → Slab T) :=
  continuous_now.comp continuous_lag
lemma continuous_elapsed : Continuous (elapsed : Time T × UnitTime → ℝ) := by
  unfold elapsed
  fun_prop
lemma elapsed_pos (p : Time T × UnitTime) : 0 < elapsed p :=
  mul_pos p.1.property.1 (sub_pos.mpr p.2.property.2)
lemma elapsed_le (p : Time T × UnitTime) : elapsed p ≤ T := by
  have hu : 1-p.2.val ≤ 1 := by linarith [p.2.property.1]
  exact (mul_le_of_le_one_right p.1.property.1.le hu).trans p.1.property.2
lemma elapsed_eq_sub (p : Time T × UnitTime) : elapsed p = (now p.1).val-(before p).val := by
  dsimp [elapsed, now, before, lag]
  ring

variable (hα : 0 < α) (A : C(Slab T, V →ᵇ Icc α β)) (b : C(Slab T, V →ᵇ ℂ))

def actualResidual (t : Time T) (s : Slab T) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  fullResidualCLM hα (A s).toContinuousMap (A (now t)).toContinuousMap (b (now t))
    (ParabolicRadius.radius (t.val-s.val))

def normalized (p : Time T × UnitTime) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  ParabolicRadius.radius (elapsed p)^3 • actualResidual hα A b p.1 (before p)

lemma continuous_actualResidual_before (f : C₀(V,ℂ)) :
    Continuous (fun p : Time T × UnitTime => actualResidual hα A b p.1 (before p) f) := by
  have he (p : Time T × UnitTime) : p.1.val-(before p).val=elapsed p := (elapsed_eq_sub p).symm
  unfold actualResidual
  simp_rw [he]
  apply continuous_fullResidualCLM_apply hα
    (fun p => A (before p)) (fun p => A (now p.1)) (fun p => b (now p.1))
    (fun p => ParabolicRadius.radius (elapsed p))
    (A.continuous.comp continuous_before) (A.continuous.comp (continuous_now.comp continuous_fst))
    (b.continuous.comp (continuous_now.comp continuous_fst))
    (ParabolicRadius.continuous_comp _ continuous_elapsed)
  exact fun p => (ParabolicRadius.pos (elapsed_pos p)).ne'

lemma continuous_normalized_apply (f : C₀(V,ℂ)) :
    Continuous (fun p : Time T × UnitTime => normalized hα A b p f) := by
  change Continuous (fun p => ParabolicRadius.radius (elapsed p)^3 • actualResidual hα A b p.1 (before p) f)
  exact ((ParabolicRadius.continuous_comp _ continuous_elapsed).pow 3).smul
    (continuous_actualResidual_before hα A b f)

lemma exists_normalized_bound (hT : T ≤ 1) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Time T × UnitTime, ‖normalized hα A b p‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_fullResidual_bound (V := V) α β hα L B hL hB
  refine ⟨C,hC,fun p => ?_⟩
  let r := ParabolicRadius.radius (elapsed p)
  have hr : 0 < r := ParabolicRadius.pos (elapsed_pos p)
  have hr1 : r ≤ 1 := ParabolicRadius.le_one (elapsed_pos p).le ((elapsed_le p).trans hT)
  have hgap : |(now p.1).val-(before p).val| = r^4 := by
    rw [← elapsed_eq_sub, abs_of_pos (elapsed_pos p), ParabolicRadius.pow_four (elapsed_pos p).le]
  have hR : ‖actualResidual hα A b p.1 (before p)‖ ≤ C*(r⁻¹)^3 := by
    unfold actualResidual
    rw [show p.1.val-(before p).val = elapsed p from (elapsed_eq_sub p).symm]
    apply hbound _ _ _ r hr hr1 (hb _)
    intro x z
    simpa only [hgap, BoundedContinuousFunction.coe_toContinuousMap] using hLip (now p.1) (before p) x z
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  change ‖r^3 • actualResidual hα A b p.1 (before p) f‖ ≤ C*‖f‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr.le _)]
  calc
    _ ≤ r^3*(C*(r⁻¹)^3*‖f‖) := mul_le_mul_of_nonneg_left
      ((actualResidual hα A b p.1 (before p)).le_opNorm f |>.trans
        (mul_le_mul_of_nonneg_right hR (norm_nonneg f))) (pow_nonneg hr.le _)
    _ = C*‖f‖ := by field_simp

theorem exists_correction (hT₀ : 0 ≤ T) (hT : T ≤ 1) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*C < 1 →
        ∀ g : Time T →ᵇ C₀(V,ℂ), ∃ j : Time T →ᵇ C₀(V,ℂ),
          ∀ t : Time T, j t +
            t.val^(1/4 : ℝ) • ∫ u : UnitTime,
              weight u • normalized hα A b (t,u) (j (lag t u)) = g t) := by
  obtain ⟨C,hC,hbound⟩ := exists_normalized_bound hα A b hT L B hL hB hb hLip
  refine ⟨C,hC,fun hsmall g => ?_⟩
  let N : Kernel T C₀(V,ℂ) := Kernel.ofStrong (normalized hα A b)
    (continuous_normalized_apply hα A b) C hC hbound
  obtain ⟨j,hj,_⟩ := exists_unique_solution N C hC hbound hT₀ hsmall g
  refine ⟨j,fun t => ?_⟩
  exact congrArg (fun f : Time T →ᵇ C₀(V,ℂ) => f t) hj


lemma exists_actualResidual_bound (hT : T ≤ 1) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : Time T) (s : Slab T), s.val<t.val →
      ‖actualResidual hα A b t s‖ ≤ C*(t.val-s.val)^(-3/4 : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_fullResidual_bound (V := V) α β hα L B hL hB
  refine ⟨C,hC,fun t s hst => ?_⟩
  have hq : 0 < t.val-s.val := sub_pos.mpr hst
  have hq1 : t.val-s.val ≤ 1 := by linarith [t.property.2, s.property.1]
  have he : |(now t).val-s.val| = ParabolicRadius.radius (t.val-s.val)^4 := by
    rw [ParabolicRadius.pow_four hq.le]
    exact abs_of_pos hq
  unfold actualResidual
  rw [← ParabolicRadius.inv_pow_three hq.le]
  apply hbound _ _ _ _ (ParabolicRadius.pos hq) (ParabolicRadius.le_one hq.le hq1) (hb _)
  intro x z
  simpa only [he, BoundedContinuousFunction.coe_toContinuousMap] using hLip (now t) s x z

def initial (hT₀ : 0 ≤ T) : Slab T := ⟨0,le_rfl,hT₀⟩

lemma continuous_initialResidual (hT₀ : 0 ≤ T) (d : C₀(V,ℂ)) :
    Continuous (fun t : Time T => actualResidual hα A b t (initial hT₀) d) := by
  unfold actualResidual initial
  simp only [sub_zero]
  apply continuous_fullResidualCLM_apply hα
    (fun _ => A ⟨0,le_rfl,hT₀⟩) (fun t => A (now t)) (fun t => b (now t))
    (fun t => ParabolicRadius.radius t.val)
    continuous_const (A.continuous.comp continuous_now) (b.continuous.comp continuous_now)
    (ParabolicRadius.continuous_comp _ continuous_subtype_val)
  exact fun t => (ParabolicRadius.pos t.property.1).ne'

def sourceRHS (hT₀ : 0 ≤ T) (d : C₀(V,ℂ)) (l : Time T →ᵇ C₀(V,ℂ)) (t : Time T) : C₀(V,ℂ) :=
  t.val^(3/4 : ℝ) • (l t-actualResidual hα A b t (initial hT₀) d)

lemma continuous_sourceRHS (hT₀ : 0 ≤ T) (d : C₀(V,ℂ)) (l : Time T →ᵇ C₀(V,ℂ)) :
    Continuous (sourceRHS hα A b hT₀ d l) :=
  (continuous_subtype_val.rpow_const (fun t => Or.inl t.property.1.ne')).smul
    (l.continuous.sub (continuous_initialResidual hα A b hT₀ d))

lemma norm_sourceRHS_le (hT₀ : 0 ≤ T) (hT : T ≤ 1) (C : ℝ) (_hC : 0 ≤ C)
    (hR : ∀ t : Time T, ‖actualResidual hα A b t (initial hT₀)‖ ≤ C*t.val^(-3/4 : ℝ))
    (d : C₀(V,ℂ)) (l : Time T →ᵇ C₀(V,ℂ)) (t : Time T) :
    ‖sourceRHS hα A b hT₀ d l t‖ ≤ ‖l‖+C*‖d‖ := by
  have ht : 0 ≤ t.val^(3/4 : ℝ) := Real.rpow_nonneg t.property.1.le _
  have ht1 : t.val^(3/4 : ℝ) ≤ 1 := Real.rpow_le_one t.property.1.le (t.property.2.trans hT) (by positivity)
  have hc : t.val^(3/4 : ℝ)*t.val^(-3/4 : ℝ)=1 := by
    rw [← Real.rpow_add t.property.1]
    norm_num
  rw [sourceRHS, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  calc
    _ ≤ t.val^(3/4 : ℝ)*(‖l‖+C*t.val^(-3/4 : ℝ)*‖d‖) :=
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans <|
        add_le_add (l.norm_coe_le_norm t) ((actualResidual hα A b t (initial hT₀)).le_opNorm d |>.trans
          (mul_le_mul_of_nonneg_right (hR t) (norm_nonneg d)))) ht
    _ = t.val^(3/4 : ℝ)*‖l‖+C*‖d‖*(t.val^(3/4 : ℝ)*t.val^(-3/4 : ℝ)) := by ring
    _ = t.val^(3/4 : ℝ)*‖l‖+C*‖d‖ := by rw [hc,mul_one]
    _ ≤ ‖l‖+C*‖d‖ := add_le_add (mul_le_of_le_one_left (norm_nonneg l) ht1) le_rfl

def weightedSource (hT₀ : 0 ≤ T) (hT : T ≤ 1) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ t : Time T, ‖actualResidual hα A b t (initial hT₀)‖ ≤ C*t.val^(-3/4 : ℝ))
    (d : C₀(V,ℂ)) (l : Time T →ᵇ C₀(V,ℂ)) : Time T →ᵇ C₀(V,ℂ) :=
  .mkOfBound ⟨sourceRHS hα A b hT₀ d l, continuous_sourceRHS hα A b hT₀ d l⟩
    (2*(‖l‖+C*‖d‖)) (by
      intro t s
      exact (dist_le_norm_add_norm _ _).trans <| by
        dsimp
        linarith [norm_sourceRHS_le hα A b hT₀ hT C hC hR d l t,
          norm_sourceRHS_le hα A b hT₀ hT C hC hR d l s])

lemma unweighted_weightedSource (hT₀ : 0 ≤ T) (hT : T ≤ 1) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ t : Time T, ‖actualResidual hα A b t (initial hT₀)‖ ≤ C*t.val^(-3/4 : ℝ))
    (d : C₀(V,ℂ)) (l : Time T →ᵇ C₀(V,ℂ)) (t : Time T) :
    unweighted (weightedSource hα A b hT₀ hT C hC hR d l) t.val =
      l t-actualResidual hα A b t (initial hT₀) d := by
  rw [unweighted_at_time]
  change t.val^(-3/4 : ℝ) • (t.val^(3/4 : ℝ) •
    (l t-actualResidual hα A b t (initial hT₀) d)) = _
  rw [smul_smul, ← Real.rpow_add t.property.1]
  norm_num

def residualKernel (hT₀ : 0 ≤ T) (t : Time T) (r : ℝ) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  if r ∈ Ioo 0 t.val then actualResidual hα A b t (projIcc 0 T hT₀ r) else 0

lemma elapsed_normalizedArg (t : Time T) (r : ℝ) (hr : r ∈ Ioo 0 t.val) :
    elapsed (t,normalizedArg t r hr) = t.val-r := by
  dsimp [elapsed, normalizedArg]
  field_simp [t.property.1.ne']

lemma before_normalizedArg (hT₀ : 0 ≤ T) (t : Time T) (r : ℝ) (hr : r ∈ Ioo 0 t.val) :
    before (t,normalizedArg t r hr) = projIcc 0 T hT₀ r := by
  have hmem : r ∈ Icc 0 T := ⟨hr.1.le,hr.2.le.trans t.property.2⟩
  rw [projIcc_of_mem hT₀ hmem]
  apply Subtype.ext
  dsimp [before,now,lag,normalizedArg]
  field_simp [t.property.1.ne']

lemma kernel_eq_residualKernel (hT₀ : 0 ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p : Time T × UnitTime, ‖normalized hα A b p‖ ≤ C) (t : Time T) (r : ℝ) :
    kernel (Kernel.ofStrong (normalized hα A b) (continuous_normalized_apply hα A b) C hC hN) t r =
      residualKernel hα A b hT₀ t r := by
  classical
  by_cases hr : r ∈ Ioo 0 t.val
  · rw [kernel,dite_eq_left hr,residualKernel,ite_eq_left hr]
    change (t.val-r)^(-3/4 : ℝ) •
      (ParabolicRadius.radius (elapsed (t,normalizedArg t r hr))^3 •
        actualResidual hα A b t (before (t,normalizedArg t r hr))) = _
    rw [elapsed_normalizedArg,before_normalizedArg hT₀]
    apply ContinuousLinearMap.ext
    intro f
    change (t.val-r)^(-3/4 : ℝ) • (ParabolicRadius.radius (t.val-r)^3 •
      actualResidual hα A b t (projIcc 0 T hT₀ r) f) = _
    rw [smul_smul,ParabolicRadius.normalized_cancel (sub_pos.mpr hr.2),one_smul]
  · simp only [kernel,dite_eq_right hr,residualKernel,ite_eq_right hr]

end Slab

open scoped ZeroAtInfty BoundedContinuousFunction
open FrozenParametrix C0Convolution StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}

theorem exists_parametrix_correction (hα : 0 < α)
    (A : C(Slab T, V →ᵇ Icc α β)) (b : C(Slab T, V →ᵇ ℂ))
    (hT₀ : 0 ≤ T) (hT : T ≤ 1) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|)) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*D < 1 →
        ∀ (d : C₀(V,ℂ)) (l : Time T →ᵇ C₀(V,ℂ)), ∃ j : Time T →ᵇ C₀(V,ℂ),
          (∀ t : Time T, IntervalIntegrable
            (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val) ∧
          (∀ t : Time T, unweighted j t.val + ∫ r in 0..t.val,
            residualKernel hα A b hT₀ t r (unweighted j r) =
              l t-actualResidual hα A b t (initial hT₀) d) ∧
          (∀ t : Time T, ‖unweighted j t.val‖ ≤ t.val^(-3/4 : ℝ) *
            ((‖l‖+C*‖d‖)/(1-T^(1/4 : ℝ)*(∫ u : UnitTime, weight u)*D)))) := by
  obtain ⟨C,hC,hR⟩ := exists_actualResidual_bound hα A b hT L B hL hB hb hLip
  obtain ⟨D,hD,hN⟩ := exists_normalized_bound hα A b hT L B hL hB hb hLip
  have hR₀ : ∀ t : Time T, ‖actualResidual hα A b t (initial hT₀)‖ ≤ C*t.val^(-3/4 : ℝ) := by
    intro t
    simpa only [initial, sub_zero] using hR t (initial hT₀) t.property.1
  refine ⟨C,D,hC,hD,fun hsmall d l => ?_⟩
  let N : Kernel T C₀(V,ℂ) := Kernel.ofStrong (normalized hα A b)
    (continuous_normalized_apply hα A b) D hD hN
  let g := weightedSource hα A b hT₀ hT C hC hR₀ d l
  obtain ⟨j,hi,hj,hbound⟩ := exists_unweighted_solution N D hD hN hT₀ hsmall g
  have he : ∀ t r, kernel N t r = residualKernel hα A b hT₀ t r :=
    kernel_eq_residualKernel hα A b hT₀ D hD hN
  simp_rw [he] at hi hj
  have hg : ∀ t : Time T, unweighted g t.val = l t-actualResidual hα A b t (initial hT₀) d :=
    unweighted_weightedSource hα A b hT₀ hT C hC hR₀ d l
  simp_rw [hg] at hj
  refine ⟨j,hi,hj,fun t => (hbound t).trans ?_⟩
  have hgnorm : ‖g‖ ≤ ‖l‖+C*‖d‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    exact norm_sourceRHS_le hα A b hT₀ hT C hC hR₀ d l
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hgnorm (by linarith)) (Real.rpow_nonneg t.property.1.le _)

end ParametrixVolterra

namespace MildVolterra
open StrongWeightedVolterra

def massWeight (u : UnitTime) : ℝ := u.val^(-3/4 : ℝ)
lemma massWeight_nonneg (u : UnitTime) : 0 ≤ massWeight u := Real.rpow_nonneg u.property.1.le _
lemma continuous_massWeight : Continuous massWeight :=
  continuous_subtype_val.rpow_const (fun u => Or.inl u.property.1.ne')
lemma integrable_massWeight : Integrable massWeight := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (r := (-3/4 : ℝ)) (by norm_num)).1.mono_set Ioo_subset_Ioc_self
  exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp hi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {T : ℝ}
variable (K : Kernel T E) (C : ℝ) (hC : 0 ≤ C) (hK : ∀ p, ‖K p‖ ≤ C)

def data (j : Time T →ᵇ E) (t : Time T) (u : UnitTime) : E :=
  massWeight u • K (t,u) (j (lag t u))

lemma continuous_data (j : Time T →ᵇ E) :
    Continuous (fun p : Time T × UnitTime => data K j p.1 p.2) := by
  exact (continuous_massWeight.comp continuous_snd).smul
    (K.continuous_apply.comp (continuous_id.prodMk (j.continuous.comp continuous_lag)))

include hC hK
lemma norm_data_le (j : Time T →ᵇ E) (t : Time T) (u : UnitTime) :
    ‖data K j t u‖ ≤ massWeight u*(C*‖j‖) := by
  rw [data,norm_smul,Real.norm_eq_abs,abs_of_nonneg (massWeight_nonneg u)]
  apply mul_le_mul_of_nonneg_left _ (massWeight_nonneg u)
  exact (K (t,u)).le_opNorm _ |>.trans
    (mul_le_mul (hK _) (j.norm_coe_le_norm _) (norm_nonneg _) hC)

lemma integrable_data (j : Time T →ᵇ E) (t : Time T) : Integrable (data K j t) :=
  (integrable_massWeight.mul_const (C*‖j‖)).mono'
    ((continuous_data K j).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Eventually.of_forall (norm_data_le K C hC hK j t))

lemma continuous_integral_data (j : Time T →ᵇ E) :
    Continuous (fun t => ∫ u : UnitTime, data K j t u) := by
  apply continuous_of_dominated
    (fun t => (integrable_data K C hC hK j t).aestronglyMeasurable)
    (fun t => Eventually.of_forall (norm_data_le K C hC hK j t))
    (integrable_massWeight.mul_const (C*‖j‖))
  exact Eventually.of_forall (fun u =>
    (continuous_data K j).comp (continuous_id.prodMk continuous_const))

lemma norm_integral_data_le (j : Time T →ᵇ E) (t : Time T) :
    ‖∫ u : UnitTime, data K j t u‖ ≤ (∫ u : UnitTime, massWeight u)*C*‖j‖ := by
  calc
    _ ≤ ∫ u : UnitTime, massWeight u*(C*‖j‖) :=
      norm_integral_le_of_norm_le (integrable_massWeight.mul_const _) <|
        Eventually.of_forall (norm_data_le K C hC hK j t)
    _ = _ := by rw [integral_mul_const]; ring

omit hC hK in
def value (j : Time T →ᵇ E) (t : Time T) : E :=
  t.val^(1/4 : ℝ) • ∫ u : UnitTime, data K j t u

lemma continuous_value (j : Time T →ᵇ E) : Continuous (value K j) :=
  (continuous_subtype_val.rpow_const (fun t => Or.inl t.property.1.ne')).smul
    (continuous_integral_data K C hC hK j)

lemma norm_value_le (j : Time T →ᵇ E) (t : Time T) :
    ‖value K j t‖ ≤ t.val^(1/4 : ℝ)*((∫ u : UnitTime, massWeight u)*C*‖j‖) := by
  rw [value,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg t.property.1.le _)]
  exact mul_le_mul_of_nonneg_left (norm_integral_data_le K C hC hK j t)
    (Real.rpow_nonneg t.property.1.le _)

lemma tendsto_value_zero (j : Time T →ᵇ E) :
    Tendsto (value K j) (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun t => norm_nonneg _) (norm_value_le K C hC hK j)
  have ht : Tendsto (fun t : Time T => t.val) (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hp := (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 1/4)).continuousAt.tendsto.comp ht
  simpa using hp.mul_const ((∫ u : UnitTime, massWeight u)*C*‖j‖)

omit hC hK in
def rawKernel (t : Time T) (r : ℝ) : E →L[ℂ] E :=
  if hr : r ∈ Ioo 0 t.val then K (t,normalizedArg t r hr) else 0

omit hC hK in
lemma rawKernel_lag (t : Time T) (u : UnitTime) :
    rawKernel K t (t.val*u.val) = K (t,u) := by
  have hr : t.val*u.val ∈ Ioo 0 t.val :=
    ⟨mul_pos t.property.1 u.property.1, mul_lt_of_lt_one_right t.property.1 u.property.2⟩
  rw [rawKernel,dite_eq_left hr,normalizedArg_lag]

omit hC hK in
lemma rescaling_scalar (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    t*(t*u)^(-3/4 : ℝ) = t^(1/4 : ℝ)*u^(-3/4 : ℝ) := by
  rw [Real.mul_rpow ht.le hu.le]
  have he : t*t^(-3/4 : ℝ) = t^(1/4 : ℝ) := by
    calc
      _ = t^(1 : ℝ)*t^(-3/4 : ℝ) := by rw [Real.rpow_one]
      _ = t^((1:ℝ)+(-3/4)) := (Real.rpow_add ht _ _).symm
      _ = _ := by norm_num
  rw [← mul_assoc,he]

omit hC hK in
lemma value_eq_integral (j : Time T →ᵇ E) (t : Time T) :
    value K j t = ∫ r in 0..t.val, rawKernel K t r (unweighted j r) := by
  let F : ℝ → E := fun r => rawKernel K t r (unweighted j r)
  have hc := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) F t.val
  simp only [mul_zero,mul_one] at hc
  change value K j t = ∫ r in 0..t.val, F r
  rw [← hc,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo,← integral_subtype measurableSet_Ioo,← integral_smul]
  unfold value
  rw [← integral_smul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  dsimp [F]
  rw [rawKernel_lag,unweighted_lag,ContinuousLinearMap.map_smul_of_tower]
  simp only [data,smul_smul,massWeight]
  rw [rescaling_scalar t.val u.val t.property.1 u.property.1]

omit hC hK in
lemma rawKernel_unweighted_lag (j : Time T →ᵇ E) (t : Time T) (u : UnitTime) :
    rawKernel K t (t.val*u.val) (unweighted j (t.val*u.val)) =
      t.val^(-3/4 : ℝ) • data K j t u := by
  rw [rawKernel_lag,unweighted_lag,ContinuousLinearMap.map_smul_of_tower]
  simp only [data,smul_smul,massWeight]
  rw [Real.mul_rpow t.property.1.le u.property.1.le]

lemma intervalIntegrable_rawKernel_unweighted (j : Time T →ᵇ E) (t : Time T) :
    IntervalIntegrable (fun r => rawKernel K t r (unweighted j r)) volume 0 t.val := by
  have hi : Integrable (fun u : UnitTime =>
      rawKernel K t (t.val*u.val) (unweighted j (t.val*u.val))) := by
    simp_rw [rawKernel_unweighted_lag]
    exact (integrable_data K C hC hK j t).smul _
  have hs : IntegrableOn (fun u : ℝ =>
      rawKernel K t (t.val*u) (unweighted j (t.val*u))) (Ioo 0 1) :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mpr hi
  have hii := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr hs
  apply (IntervalIntegrable.comp_mul_left_iff (a := 0) (b := t.val) t.property.1.ne').mp
  simpa only [zero_div,div_self t.property.1.ne'] using hii

end MildVolterra

namespace ParametrixVolterra
open scoped ZeroAtInfty BoundedContinuousFunction
open FrozenParametrix C0Convolution StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}
variable (hα : 0 < α) (A : C(Slab T, V →ᵇ Icc α β))

def actualFrozen (t : Time T) (s : Slab T) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  frozenCLM hα (A s).toContinuousMap (ParabolicRadius.radius (t.val-s.val))

lemma continuous_actualFrozen_before (d : C₀(V,ℂ)) :
    Continuous (fun p : Time T × UnitTime => actualFrozen hα A p.1 (before p) d) := by
  unfold actualFrozen
  simp_rw [show ∀ p : Time T × UnitTime, p.1.val-(before p).val=elapsed p from fun p => (elapsed_eq_sub p).symm]
  exact continuous_frozenOp_comp hα (fun p => A (before p))
    (fun p => ParabolicRadius.radius (elapsed p)) (A.continuous.comp continuous_before)
    (ParabolicRadius.continuous_comp _ continuous_elapsed) d

def frozenBound : ℝ := ∫ y : V, kernelMajorant α β hα y
lemma frozenBound_nonneg : 0 ≤ frozenBound (V := V) (β := β) hα :=
  integral_nonneg (kernelMajorant_spec α β hα).2.1

lemma norm_actualFrozen_le (t : Time T) (s : Slab T) :
    ‖actualFrozen hα A t s‖ ≤ frozenBound (V := V) (β := β) hα :=
  norm_frozenCLM_le hα _ _

def mildKernel : Kernel T C₀(V,ℂ) :=
  Kernel.ofStrong (fun p => actualFrozen hα A p.1 (before p))
    (continuous_actualFrozen_before hα A) (frozenBound (V := V) (β := β) hα)
    (frozenBound_nonneg hα) (fun p => norm_actualFrozen_le hα A p.1 (before p))

lemma norm_mildKernel_le (p : Time T × UnitTime) :
    ‖mildKernel hα A p‖ ≤ frozenBound (V := V) (β := β) hα :=
  norm_actualFrozen_le hα A p.1 (before p)

lemma continuous_frozen_initial (hT₀ : 0 ≤ T) (d : C₀(V,ℂ)) :
    Continuous (fun t : Time T => actualFrozen hα A t (initial hT₀) d) := by
  change Continuous (fun t : Time T => frozenOp hα (A (initial hT₀)).toContinuousMap
    (ParabolicRadius.radius (t.val-0)) d)
  simp only [sub_zero]
  exact continuous_frozenOp_comp hα (fun _ : Time T => A (initial hT₀))
    (fun t : Time T => ParabolicRadius.radius t.val) continuous_const
    (ParabolicRadius.continuous_comp _ continuous_subtype_val) d

lemma tendsto_frozen_initial (hT₀ : 0 ≤ T) (d : C₀(V,ℂ)) :
    Tendsto (fun t : Time T => actualFrozen hα A t (initial hT₀) d)
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 d) := by
  have ht : Tendsto (fun t : Time T => t.val) (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hf : Continuous (fun q : ℝ => frozenOp hα (A (initial hT₀)).toContinuousMap (ParabolicRadius.radius q) d) :=
    continuous_frozenOp_comp hα (fun _ => A (initial hT₀)) ParabolicRadius.radius continuous_const
      (ParabolicRadius.continuous_comp _ continuous_id) d
  have hz : frozenOp hα (A (initial hT₀)).toContinuousMap (ParabolicRadius.radius 0) d = d := by
    rw [show ParabolicRadius.radius 0 = 0 from Real.zero_rpow (by norm_num)]
    exact frozen_zero _ _ _ _ _ _ d
  change Tendsto (fun t : Time T => frozenOp hα (A (initial hT₀)).toContinuousMap
    (ParabolicRadius.radius (t.val-0)) d) _ (𝓝 d)
  simp only [sub_zero]
  have hout := (hf.tendsto 0).comp ht
  rw [hz] at hout
  exact hout

def mild (hT₀ : 0 ≤ T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T) : C₀(V,ℂ) :=
  actualFrozen hα A t (initial hT₀) d + MildVolterra.value (mildKernel hα A) j t

lemma continuous_mild (hT₀ : 0 ≤ T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ)) :
    Continuous (mild hα A hT₀ d j) :=
  (continuous_frozen_initial hα A hT₀ d).add
    (MildVolterra.continuous_value (mildKernel hα A) (frozenBound (V := V) (β := β) hα)
      (frozenBound_nonneg hα) (norm_mildKernel_le hα A) j)

lemma tendsto_mild_initial (hT₀ : 0 ≤ T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ)) :
    Tendsto (mild hα A hT₀ d j) (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 d) := by
  have ht := (tendsto_frozen_initial hα A hT₀ d).add
    (MildVolterra.tendsto_value_zero (mildKernel hα A) (frozenBound (V := V) (β := β) hα)
      (frozenBound_nonneg hα) (norm_mildKernel_le hα A) j)
  unfold mild
  simpa only [add_zero] using ht

def frozenRaw (hT₀ : 0 ≤ T) (t : Time T) (r : ℝ) : C₀(V,ℂ) →L[ℂ] C₀(V,ℂ) :=
  if r ∈ Ioo 0 t.val then actualFrozen hα A t (projIcc 0 T hT₀ r) else 0

lemma rawKernel_eq_frozenRaw (hT₀ : 0 ≤ T) (t : Time T) (r : ℝ) :
    MildVolterra.rawKernel (mildKernel hα A) t r = frozenRaw hα A hT₀ t r := by
  classical
  by_cases hr : r ∈ Ioo 0 t.val
  · rw [MildVolterra.rawKernel,dite_eq_left hr,frozenRaw,ite_eq_left hr]
    change actualFrozen hα A t (before (t,normalizedArg t r hr)) = _
    rw [before_normalizedArg hT₀]
  · simp only [MildVolterra.rawKernel,dite_eq_right hr,frozenRaw,ite_eq_right hr]

lemma intervalIntegrable_frozenRaw (hT₀ : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T) :
    IntervalIntegrable (fun r => frozenRaw hα A hT₀ t r (unweighted j r)) volume 0 t.val := by
  simpa only [rawKernel_eq_frozenRaw hα A hT₀] using
    MildVolterra.intervalIntegrable_rawKernel_unweighted (mildKernel hα A)
      (frozenBound (V := V) (β := β) hα) (frozenBound_nonneg hα) (norm_mildKernel_le hα A) j t

lemma mild_eq_integral (hT₀ : 0 ≤ T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T) :
    mild hα A hT₀ d j t = actualFrozen hα A t (initial hT₀) d +
      ∫ r in 0..t.val, frozenRaw hα A hT₀ t r (unweighted j r) := by
  rw [mild,MildVolterra.value_eq_integral]
  simp_rw [rawKernel_eq_frozenRaw hα A hT₀]

end ParametrixVolterra

open Set Filter MeasureTheory
open scoped SchwartzMap Topology ContDiff BoundedContinuousFunction

namespace ScaledSchwartzConvolution
section ScaledDecay
universe u
variable {V E : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)] in
lemma scaled_decay (g : SchwartzMap V E) (a b : ℝ) (ha : 0 < a) (K N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Icc a b, ∀ z,
      (1+‖z‖)^N * ‖(c⁻¹)^K • g (c⁻¹ • z)‖ ≤ C := by
  let M := max b 1
  let D := 2^N * (Finset.Iic (N,0)).sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) g
  have hD : 0 ≤ D := by positivity
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdec (z : V) : (1+‖z‖)^N * ‖g z‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N,0)) le_rfl le_rfl g z
  refine ⟨(a⁻¹)^K*(M^N*D), by positivity, ?_⟩
  intro c hc z
  have hcpos : 0 < c := ha.trans_le hc.1
  have hcM : c ≤ M := hc.2.trans (le_max_left _ _)
  have hn : ‖z‖ = c * ‖c⁻¹ • z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos),
      ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
  have hs : 1+‖z‖ ≤ M*(1+‖c⁻¹ • z‖) := by
    rw [hn, mul_add, mul_one]
    exact add_le_add (le_max_right b 1) (mul_le_mul_of_nonneg_right hcM (norm_nonneg _))
  have hg : (1+‖z‖)^N * ‖g (c⁻¹ • z)‖ ≤ M^N*D := by
    calc
      _ ≤ (M*(1+‖c⁻¹ • z‖))^N * ‖g (c⁻¹ • z)‖ := by gcongr
      _ = M^N * ((1+‖c⁻¹ • z‖)^N * ‖g (c⁻¹ • z)‖) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdec _) (by positivity)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ = (c⁻¹)^K * ((1+‖z‖)^N * ‖g (c⁻¹ • z)‖) := by ring
    _ ≤ (a⁻¹)^K * ((1+‖z‖)^N * ‖g (c⁻¹ • z)‖) := by gcongr; exact hc.1
    _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)

lemma shifted_majorant (g : SchwartzMap V E) (a b : ℝ) (ha : 0 < a) (K : ℕ) (x₀ : V) :
    ∃ B : V → ℝ, Integrable B ∧ ∀ c ∈ Icc a b, ∀ x ∈ Metric.ball x₀ 1, ∀ y,
      ‖(c⁻¹)^K • g (c⁻¹ • (x-y))‖ ≤ B y := by
  let N := Module.finrank ℝ V + 1
  obtain ⟨C,hC,hdec⟩ := scaled_decay g a b ha K N
  refine ⟨fun y => (2^N*C)/(1+‖x₀-y‖)^N, ?_, ?_⟩
  · have hi : Integrable (fun z : V => (1+‖z‖)^(-(N : ℝ))) :=
      integrable_one_add_norm (by dsimp [N]; norm_num)
    simpa only [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+‖x₀-_‖),
      Real.rpow_natCast, div_eq_mul_inv] using (hi.comp_sub_left x₀).const_mul (2^N*C)
  · intro c hc x hx y
    have hd : ‖x₀-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm,norm_sub_rev] using hx
    have hn : ‖x₀-y‖ ≤ ‖x₀-x‖ + ‖x-y‖ := by simpa only [sub_add_sub_cancel] using norm_add_le (x₀-x) (x-y)
    have hs : 1+‖x₀-y‖ ≤ 2*(1+‖x-y‖) := by nlinarith [norm_nonneg (x-y)]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ ‖(c⁻¹)^K • g (c⁻¹ • (x-y))‖ * (2*(1+‖x-y‖))^N := by gcongr
      _ = 2^N * ((1+‖x-y‖)^N * ‖(c⁻¹)^K • g (c⁻¹ • (x-y))‖) := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdec c hc _) (by positivity)

variable {A F : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {a b : ℝ} (ha : 0 < a) (c : V → ℝ) (hc : Continuous c) (hcb : ∀ y, c y ∈ Icc a b)

def value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A) (g : SchwartzMap V E) (K : ℕ) (x : V) : F :=
  ∫ y, L (f y) ((c y)⁻¹^K • g ((c y)⁻¹ • (x-y)))

include ha hc hcb
lemma integrable_integrand (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) (x : V) :
    Integrable (fun y => L (f y) ((c y)⁻¹^K • g ((c y)⁻¹ • (x-y)))) := by
  obtain ⟨B,hB,hbound⟩ := shifted_majorant g a b ha K x
  have hci : Continuous (fun y => (c y)⁻¹) := hc.inv₀ (fun y => (ha.trans_le (hcb y).1).ne')
  refine (hB.const_mul (‖L‖*‖f‖)).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((L.continuous.comp f.continuous).clm_apply
      ((hci.pow K).smul (g.continuous.comp (hci.smul (continuous_const.sub continuous_id))))).aestronglyMeasurable
  · exact (L.le_opNorm₂ _ _).trans <| mul_le_mul
      (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg L))
      (hbound (c y) (hcb y) x (Metric.mem_ball_self zero_lt_one) y)
      (norm_nonneg _) (by positivity)

lemma hasFDerivAt_value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) (x₀ : V) :
    HasFDerivAt (value c L f g K)
      (value c (L.precompR V) f (SchwartzMap.fderivCLM ℝ V E g) (K+1) x₀) x₀ := by
  let g' := SchwartzMap.fderivCLM ℝ V E g
  obtain ⟨B,hB,hbound⟩ := shifted_majorant g' a b ha (K+1) x₀
  have hd (x y : V) : HasFDerivAt (fun x => (c y)⁻¹^K • g ((c y)⁻¹ • (x-y)))
      ((c y)⁻¹^(K+1) • g' ((c y)⁻¹ • (x-y))) x := by
    have h := ((g.hasFDerivAt ((c y)⁻¹ • (x-y))).comp x
      (((hasFDerivAt_id x).sub (hasFDerivAt_const y x)).const_smul (c y)⁻¹)).const_smul ((c y)⁻¹^K)
    convert h using 1
    · rfl
    · ext v
      simp [g',SchwartzMap.fderivCLM_apply,pow_succ,smul_smul]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds x₀ zero_lt_one)
  · exact Eventually.of_forall fun x => (integrable_integrand ha c hc hcb L f g K x).aestronglyMeasurable
  · exact integrable_integrand ha c hc hcb L f g K x₀
  · exact (integrable_integrand ha c hc hcb (L.precompR V) f g' (K+1) x₀).aestronglyMeasurable
  · filter_upwards with y x hx
    change ‖(L (f y)).comp ((c y)⁻¹^(K+1) • g' ((c y)⁻¹ • (x-y)))‖ ≤ _
    calc
      _ ≤ ‖L (f y)‖ * ‖(c y)⁻¹^(K+1) • g' ((c y)⁻¹ • (x-y))‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖L‖*‖f‖) * ‖(c y)⁻¹^(K+1) • g' ((c y)⁻¹ • (x-y))‖ := by
        gcongr
        exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg L))
      _ ≤ (‖L‖*‖f‖)*B y := mul_le_mul_of_nonneg_left (hbound (c y) (hcb y) x hx y) (by positivity)
  · exact hB.const_mul (‖L‖*‖f‖)
  · filter_upwards with y x _
    exact (L (f y)).hasFDerivAt.comp x (hd x y)

lemma contDiff_value_nat (n : ℕ) (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) : ContDiff ℝ n (value c L f g K) := by
  induction n generalizing E F K with
  | zero =>
      rw [Nat.cast_zero,contDiff_zero]
      exact continuous_iff_continuousAt.mpr (fun x => (hasFDerivAt_value ha c hc hcb L f g K x).continuousAt)
  | succ n ih =>
      rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_hasFDerivAt]
      exact ⟨value c (L.precompR V) f (SchwartzMap.fderivCLM ℝ V E g) (K+1),
        ih (L.precompR V) (SchwartzMap.fderivCLM ℝ V E g) (K+1), hasFDerivAt_value ha c hc hcb L f g K⟩

lemma contDiff_value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) : ContDiff ℝ ∞ (value c L f g K) :=
  contDiff_infty.mpr (fun n => contDiff_value_nat ha c hc hcb n L f g K)

lemma fderiv_value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) :
    fderiv ℝ (value c L f g K) = value c (L.precompR V) f (SchwartzMap.fderivCLM ℝ V E g) (K+1) := by
  funext x
  exact (hasFDerivAt_value ha c hc hcb L f g K x).fderiv

lemma fderiv_value_apply (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) (x v : V) :
    fderiv ℝ (value c L f g K) x v =
      ∫ y, L (f y) ((c y)⁻¹^(K+1) • fderiv ℝ g ((c y)⁻¹ • (x-y)) v) := by
  rw [fderiv_value ha c hc hcb L f g K, value,
    ContinuousLinearMap.integral_apply
      (integrable_integrand ha c hc hcb (L.precompR V) f (SchwartzMap.fderivCLM ℝ V E g) (K+1) x)]
  rfl

lemma second_fderiv_value_apply (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) (x v w : V) :
    fderiv ℝ (fderiv ℝ (value c L f g K)) x v w =
      ∫ y, L (f y) ((c y)⁻¹^(K+2) • fderiv ℝ (fderiv ℝ g) ((c y)⁻¹ • (x-y)) v w) := by
  rw [fderiv_value ha c hc hcb L f g K, fderiv_value_apply ha c hc hcb]
  rw [ContinuousLinearMap.integral_apply]
  · rfl
  · exact integrable_integrand ha c hc hcb (L.precompR V) f
      (SchwartzMap.evalCLM ℝ V (V →L[ℝ] E) v
        (SchwartzMap.fderivCLM ℝ V (V →L[ℝ] E) (SchwartzMap.fderivCLM ℝ V E g))) (K+2) x

end ScaledDecay

open scoped Laplacian
universe u
variable {V E F A : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {a b : ℝ} (ha : 0 < a) (c : V → ℝ) (hc : Continuous c) (hcb : ∀ y, c y ∈ Icc a b)

include ha hc hcb
lemma laplacian_value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) :
    Δ (value c L f g K) = value c L f (Δ g : SchwartzMap V E) (K+2) := by
  funext x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    second_fderiv_value_apply ha c hc hcb]
  rw [value]
  simp_rw [SchwartzMap.laplacian_apply,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.smul_sum, map_sum]
  rw [integral_finsetSum]
  · rfl
  · intro i _
    exact integrable_integrand ha c hc hcb L f
      (SchwartzMap.evalCLM ℝ V E ((stdOrthonormalBasis ℝ V) i)
        (SchwartzMap.evalCLM ℝ V (V →L[ℝ] E) ((stdOrthonormalBasis ℝ V) i)
          (SchwartzMap.fderivCLM ℝ V (V →L[ℝ] E) (SchwartzMap.fderivCLM ℝ V E g)))) (K+2) x

lemma bilaplacian_value (L : A →L[ℝ] E →L[ℝ] F) (f : V →ᵇ A)
    (g : SchwartzMap V E) (K : ℕ) :
    Δ (Δ (value c L f g K)) = value c L f (Δ (Δ g : SchwartzMap V E) : SchwartzMap V E) (K+4) := by
  rw [laplacian_value ha c hc hcb, laplacian_value ha c hc hcb]

end ScaledSchwartzConvolution

namespace FrozenParametrix
open scoped SchwartzMap Laplacian ZeroAtInfty BoundedContinuousFunction
open BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}

def sourceScale (a : C(V,Icc α β)) (q : ℝ) (y : V) : ℝ :=
  Real.sqrt (Real.sqrt (q*(a y).val))

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma continuous_sourceScale (a : C(V,Icc α β)) (q : ℝ) : Continuous (sourceScale a q) :=
  Real.continuous_sqrt.comp (Real.continuous_sqrt.comp
    (continuous_const.mul (continuous_subtype_val.comp a.continuous)))

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma sourceScale_bounds (a : C(V,Icc α β)) (q : ℝ) (hq : 0 ≤ q) (y : V) :
    sourceScale a q y ∈ Icc (Real.sqrt (Real.sqrt (q*α))) (Real.sqrt (Real.sqrt (q*β))) := by
  exact ⟨Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (a y).property.1 hq)),
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (a y).property.2 hq))⟩

def timeValue (a : C(V,Icc α β)) (q : ℝ) (f : C₀(V,ℂ)) (x : V) : ℂ :=
  ∫ y, f y * kernel (q*(a y).val) (x-y)

lemma timeValue_eq_scaled (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) : timeValue a q f =
      ScaledSchwartzConvolution.value (sourceScale a q) (ContinuousLinearMap.mul ℝ ℂ)
        f.toBCF (heatKernel 1 zero_lt_one) (Module.finrank ℝ V) := by
  funext x
  unfold timeValue ScaledSchwartzConvolution.value
  congr 1
  funext y
  rw [kernel_eq_scaled _ (mul_pos hq (hα.trans_le (a y).property.1)), ← inv_pow]
  rfl

lemma timeValue_eq_frozenOp (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) : timeValue a q f = frozenOp hα a (ParabolicRadius.radius q) f := by
  funext x
  rw [frozenOp, frozen_apply_unscaled _ _ _ _ _ _ _ (ParabolicRadius.pos hq)]
  rw [ParabolicRadius.pow_four hq.le]
  unfold timeValue
  congr 1
  funext y
  exact mul_comm _ _

lemma contDiff_timeValue (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) : ContDiff ℝ ∞ (timeValue a q f) := by
  rw [timeValue_eq_scaled hα a q hq f]
  exact ScaledSchwartzConvolution.contDiff_value
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos hq hα))) (sourceScale a q)
    (continuous_sourceScale a q) (sourceScale_bounds a q hq.le)
    (ContinuousLinearMap.mul ℝ ℂ) f.toBCF
    (heatKernel 1 zero_lt_one) (Module.finrank ℝ V)

lemma bilaplacian_timeValue (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (x : V) :
    Δ (Δ (timeValue a q f)) x = ∫ y, f y * bilapKernel (q*(a y).val) (x-y) := by
  rw [timeValue_eq_scaled hα a q hq f,
    ScaledSchwartzConvolution.bilaplacian_value
      (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos hq hα))) (sourceScale a q)
      (continuous_sourceScale a q) (sourceScale_bounds a q hq.le)]
  unfold ScaledSchwartzConvolution.value
  congr 1
  funext y
  rw [bilapKernel_eq_scaled _ (mul_pos hq (hα.trans_le (a y).property.1))]
  rfl

lemma integrable_timeValue_integrand (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (x : V) : Integrable (fun y => f y * kernel (q*(a y).val) (x-y)) := by
  have he (y : V) : kernel (q*(a y).val) (x-y) =
      (sourceScale a q y)⁻¹^(Module.finrank ℝ V) •
        heatKernel (V := V) 1 zero_lt_one ((sourceScale a q y)⁻¹ • (x-y)) := by
    rw [kernel_eq_scaled _ (mul_pos hq (hα.trans_le (a y).property.1)), ← inv_pow]
    rfl
  simp_rw [he]
  exact ScaledSchwartzConvolution.integrable_integrand
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos hq hα))) (sourceScale a q)
    (continuous_sourceScale a q) (sourceScale_bounds a q hq.le)
    (ContinuousLinearMap.mul ℝ ℂ) f.toBCF
    (heatKernel 1 zero_lt_one) (Module.finrank ℝ V) x

lemma integrable_bilapValue_integrand (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (x : V) : Integrable (fun y => f y * bilapKernel (q*(a y).val) (x-y)) := by
  simp_rw [bilapKernel_eq_scaled _ (mul_pos hq (hα.trans_le (a _).property.1))]
  exact ScaledSchwartzConvolution.integrable_integrand
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos hq hα))) (sourceScale a q)
    (continuous_sourceScale a q) (sourceScale_bounds a q hq.le)
    (ContinuousLinearMap.mul ℝ ℂ) f.toBCF
    (Δ (Δ (heatKernel 1 zero_lt_one) : SchwartzMap V ℂ) : SchwartzMap V ℂ)
    (Module.finrank ℝ V+4) x

end FrozenParametrix

namespace BiharmonicKernel
open scoped SchwartzMap Laplacian
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma bilapKernel_shifted_majorant (a b : ℝ) (ha : 0 < a) (x₀ : V) :
    ∃ B : V → ℝ, Integrable B ∧ ∀ t ∈ Icc a b, ∀ x ∈ Metric.ball x₀ 1, ∀ y,
      ‖bilapKernel t (x-y)‖ ≤ B y := by
  obtain ⟨B,hB,hbound⟩ := ScaledSchwartzConvolution.shifted_majorant
    (Δ (Δ (heatKernel (V := V) 1 zero_lt_one) : SchwartzMap V ℂ) : SchwartzMap V ℂ)
    (Real.sqrt (Real.sqrt a)) (Real.sqrt (Real.sqrt b))
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ha)) (Module.finrank ℝ V+4) x₀
  refine ⟨B,hB,fun t ht x hx y => ?_⟩
  rw [bilapKernel_eq_scaled t (ha.trans_le ht.1)]
  exact hbound _ ⟨Real.sqrt_le_sqrt (Real.sqrt_le_sqrt ht.1),
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt ht.2)⟩ x hx y

lemma hasDerivAt_kernel_bilap (t : ℝ) (ht : 0 < t) (x : V) :
    HasDerivAt (fun s => kernel s x) (-bilapKernel t x) t := by
  rw [bilapKernel_eq_schwartz t ht]
  exact kernel_heat_equation t ht x

end BiharmonicKernel

namespace FrozenParametrix
open scoped SchwartzMap Laplacian ZeroAtInfty BoundedContinuousFunction
open BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}

lemma hasDerivAt_timeValue (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (x : V) :
    HasDerivAt (fun s => timeValue a s f x)
      (-(∫ y, ((a y).val : ℂ)*f y*bilapKernel (q*(a y).val) (x-y))) q := by
  let F := fun s : ℝ => fun y : V => f y * kernel (s*(a y).val) (x-y)
  let F' := fun s : ℝ => fun y : V => f y * ((a y).val • (-bilapKernel (s*(a y).val) (x-y)))
  have hay (y : V) : 0 < (a y).val := hα.trans_le (a y).property.1
  have hβ : 0 < β := (hay 0).trans_le (a 0).property.2
  have hFi (s : ℝ) (hs : 0 < s) : Integrable (F s) := integrable_timeValue_integrand hα a s hs f x
  have hF'cont (s : ℝ) (hs : 0 < s) : Continuous (F' s) :=
    f.continuous.mul ((continuous_subtype_val.comp a.continuous).smul
      (continuous_bilapKernel_comp (fun y : V => s*(a y).val) (fun y => x-y)
        (continuous_const.mul (continuous_subtype_val.comp a.continuous))
        (continuous_const.sub continuous_id) (fun y => mul_pos hs (hay y))).neg)
  obtain ⟨B,hB,hbound⟩ := bilapKernel_shifted_majorant (V := V)
    ((q/2)*α) ((2*q)*β) (by positivity) x
  have hspos (s : ℝ) (hs : s ∈ Ioo (q/2) (2*q)) : 0 < s := lt_trans (by positivity) hs.1
  have hsb (s : ℝ) (hs : s ∈ Ioo (q/2) (2*q)) (y : V) :
      s*(a y).val ∈ Icc ((q/2)*α) ((2*q)*β) :=
    ⟨mul_le_mul hs.1.le (a y).property.1 hα.le (hspos s hs).le,
      mul_le_mul hs.2.le (a y).property.2 (hay y).le (by positivity)⟩
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun y => (‖f‖*β)*B y)
    (s := Ioo (q/2) (2*q)) (Ioo_mem_nhds (by linarith) (by linarith))
    (by filter_upwards [Ioi_mem_nhds hq] with s hs; exact (hFi s hs).aestronglyMeasurable)
    (hFi q hq) (hF'cont q hq).aestronglyMeasurable
    (Eventually.of_forall (fun y s hs => by
      simp only [F',norm_mul,norm_smul,Real.norm_eq_abs,abs_of_pos (hay y),norm_neg]
      rw [← mul_assoc]
      exact mul_le_mul
        (mul_le_mul (f.toBCF.norm_coe_le_norm y) (a y).property.2 (hay y).le (norm_nonneg f))
        (hbound _ (hsb s hs y) x (Metric.mem_ball_self zero_lt_one) y)
        (norm_nonneg _) (by positivity)))
    (hB.const_mul (‖f‖*β))
    (Eventually.of_forall (fun y s hs => by
      simpa [F,F',Function.comp_def,Complex.real_smul,mul_assoc] using
        ((hasDerivAt_kernel_bilap (s*(a y).val) (mul_pos (hspos s hs) (hay y)) (x-y)).scomp s
        ((hasDerivAt_id s).mul_const (a y).val)).const_mul (f y)))
  have he : (∫ y, F' q y) = -(∫ y, ((a y).val : ℂ)*f y*bilapKernel (q*(a y).val) (x-y)) := by
    rw [← integral_neg]
    congr 1
    funext y
    dsimp [F']
    ring
  rw [he] at hd
  exact hd.2

lemma frozen_pde_residual (hα : 0 < α) (a₀ a₁ : C(V,Icc α β)) (b : V →ᵇ ℂ)
    (q : ℝ) (hq : 0 < q) (f : C₀(V,ℂ)) (x : V) :
    deriv (fun s => timeValue a₀ s f x) q + ((a₁ x).val : ℂ) *
      Δ (Δ (timeValue a₀ q f)) x + b x * timeValue a₀ q f x =
        fullResidualCLM hα a₀ a₁ b (ParabolicRadius.radius q) f x := by
  rw [(hasDerivAt_timeValue hα a₀ q hq f x).deriv, bilaplacian_timeValue hα a₀ q hq f x,
    fullResidualCLM_apply]
  change _ = principalResidual hα a₀ a₁ (ParabolicRadius.radius q) f x +
    b x * frozenOp hα a₀ (ParabolicRadius.radius q) f x
  rw [← timeValue_eq_frozenOp hα a₀ q hq f, principalResidual_apply_unscaled hα a₀ a₁ _
    (ParabolicRadius.pos hq), ParabolicRadius.pow_four hq.le]
  have hi₀ := integrable_bilapValue_integrand hα a₀ q hq f x
  have hi₁ := integrable_bilapValue_integrand hα a₀ q hq
    (C0Multiplier.mul (coefficient a₀) f) x
  change Integrable (fun y => (((a₀ y).val : ℂ)*f y)*bilapKernel (q*(a₀ y).val) (x-y)) at hi₁
  have he : (fun y => (((a₁ x).val-(a₀ y).val : ℝ) : ℂ) *
      bilapKernel (q*(a₀ y).val) (x-y) * f y) =
    fun y => ((a₁ x).val : ℂ)*(f y*bilapKernel (q*(a₀ y).val) (x-y)) -
      (((a₀ y).val : ℂ)*f y)*bilapKernel (q*(a₀ y).val) (x-y) := by
    funext y
    rw [Complex.ofReal_sub]
    ring
  rw [he, integral_sub (hi₀.const_mul _) hi₁, integral_const_mul]
  ring

end FrozenParametrix

open scoped Topology SchwartzMap ZeroAtInfty BoundedContinuousFunction
open Set Filter MeasureTheory
namespace KernelPairing
section IntegrableProdOfTranslationBound
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integrable_prod_of_translation_bound (F : V × V → ℂ) (hF : Continuous F)
    (φ B : V → ℝ) (hφ : Integrable φ)
    (hB : Integrable B) (C : ℝ)
    (hbound : ∀ x y, ‖F (x,y)‖ ≤ φ x * C * B (x-y)) :
    Integrable F (volume.prod volume) := by
  have hBi (x : V) : Integrable (fun y => B (x-y)) :=
    (integrable_comp_sub_left B x).mpr hB
  have hFi (x : V) : Integrable (fun y => F (x,y)) := by
    apply ((hBi x).const_mul (φ x * C)).mono'
    · exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · exact Eventually.of_forall (hbound x)
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall hFi, ?_⟩
  apply ((hφ.mul_const C).mul_const (∫ y, B y)).mono'
  · exact hF.aestronglyMeasurable.norm.integral_prod_right'
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    calc
      _ ≤ ∫ y, φ x*C*B (x-y) := integral_mono (hFi x).norm
        ((hBi x).const_mul _) (hbound x)
      _ = φ x*C*(∫ y, B y) := by rw [integral_const_mul, integral_sub_left_eq_self]

lemma integrable_pair (φ : V → ℂ) (hφ : Integrable φ) (f : V →ᵇ ℂ) :
    Integrable (fun x => φ x * f x) := by
  apply (hφ.norm.mul_const ‖f‖).mono'
  · exact hφ.aestronglyMeasurable.mul f.continuous.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)

lemma norm_pair_le (φ : V → ℂ) (hφ : Integrable φ) (f : V →ᵇ ℂ) :
    ‖∫ x, φ x*f x‖ ≤ (∫ x, ‖φ x‖)*‖f‖ := by
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_mul_const]
  apply integral_mono (integrable_pair φ hφ f).norm (hφ.norm.mul_const _)
  intro x
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)

def pairCLM (φ : V → ℂ) (hφ : Integrable φ) : C₀(V,ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, φ x * f x
      map_add' := by
        intro f g
        change (∫ x, φ x*(f x+g x)) = _
        simp_rw [mul_add]
        exact integral_add (integrable_pair φ hφ f.toBCF) (integrable_pair φ hφ g.toBCF)
      map_smul' := by
        intro c f
        change (∫ x, φ x*(c*f x)) = c*(∫ x, φ x*f x)
        simp_rw [mul_left_comm (φ _) c]
        exact integral_const_mul _ _ }
    (∫ x, ‖φ x‖) (fun f => norm_pair_le φ hφ f.toBCF)

@[simp] lemma pairCLM_apply (φ : V → ℂ) (hφ : Integrable φ) (f : C₀(V,ℂ)) :
    pairCLM φ hφ f = ∫ x, φ x * f x := rfl

end IntegrableProdOfTranslationBound

open scoped Laplacian
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
lemma laplacian_translate (f : V → ℂ) (y : V) :
    Δ (fun x => f (x-y)) = fun x => Δ f (x-y) := by
  simp_rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_sub]

omit [MeasurableSpace V] [BorelSpace V] in
lemma schwartz_laplacian_translate (f : SchwartzMap V ℂ) (y : V) :
    Δ (f.compSubConstCLM ℂ y : SchwartzMap V ℂ) =
      (Δ f : SchwartzMap V ℂ).compSubConstCLM ℂ y := by
  ext x
  rw [SchwartzMap.laplacian_apply, SchwartzMap.compSubConstCLM_apply,
    SchwartzMap.laplacian_apply]
  exact congrFun (laplacian_translate (f : V → ℂ) y) x

lemma schwartz_bilaplacian_pair (φ g : SchwartzMap V ℂ) :
    (∫ x, φ x*(Δ (Δ g : SchwartzMap V ℂ) : SchwartzMap V ℂ) x) =
      ∫ x, (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x*g x := by
  rw [SchwartzMap.integral_mul_laplacian_right_eq_left,
    SchwartzMap.integral_mul_laplacian_right_eq_left]

lemma bilaplacian_pair_kernel (φ : SchwartzMap V ℂ) (f : V → ℂ)
    (K : V → SchwartzMap V ℂ)
    (h₀ : Integrable (fun p : V × V =>
      (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) p.1 * (f p.2*K p.2 (p.1-p.2)))
        (volume.prod volume))
    (h₄ : Integrable (fun p : V × V =>
      φ p.1*(f p.2*(Δ (Δ (K p.2) : SchwartzMap V ℂ) : SchwartzMap V ℂ) (p.1-p.2)))
        (volume.prod volume)) :
    (∫ x, φ x*(∫ y, f y*(Δ (Δ (K y) : SchwartzMap V ℂ) : SchwartzMap V ℂ) (x-y))) =
      ∫ x, (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x*(∫ y, f y*K y (x-y)) := by
  simp_rw [← integral_const_mul]
  conv_lhs => rw [integral_integral_swap h₄]
  conv_rhs => rw [integral_integral_swap h₀]
  apply integral_congr_ae
  filter_upwards with y
  have he := schwartz_bilaplacian_pair φ ((K y).compSubConstCLM ℂ y)
  simp only [schwartz_laplacian_translate, SchwartzMap.compSubConstCLM_apply] at he
  calc
    _ = f y*(∫ x, φ x*(Δ (Δ (K y) : SchwartzMap V ℂ) : SchwartzMap V ℂ) (x-y)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = f y*(∫ x, (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x*K y (x-y)) := by rw [he]
    _ = _ := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring

end KernelPairing

namespace FrozenParametrix
section IntegrableKernelPairProd
open scoped SchwartzMap Laplacian ZeroAtInfty BoundedContinuousFunction
open BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}

lemma integrable_kernel_pair_prod (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (φ : SchwartzMap V ℂ) :
    Integrable (fun p : V × V => φ p.1 * (f p.2*kernel (q*(a p.2).val) (p.1-p.2)))
      (volume.prod volume) := by
  obtain ⟨B,hB,hbound⟩ := kernel_majorant (V := V) (q*α) (q*β) (mul_pos hq hα)
  apply KernelPairing.integrable_prod_of_translation_bound _
    (φ.continuous.comp continuous_fst |>.mul
      ((f.continuous.comp continuous_snd).mul
        (continuous_kernel_comp (fun p : V × V => q*(a p.2).val) (fun p => p.1-p.2)
          (continuous_const.mul (continuous_subtype_val.comp (a.continuous.comp continuous_snd)))
          (continuous_fst.sub continuous_snd) (fun p => mul_pos hq (hα.trans_le (a p.2).property.1)))))
    (fun x => ‖φ x‖) B φ.integrable.norm hB ‖f‖
  intro x y
  change ‖φ x * (f y * kernel (q*(a y).val) (x-y))‖ ≤ ‖φ x‖*‖f‖*B (x-y)
  rw [norm_mul,norm_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact mul_le_mul (f.toBCF.norm_coe_le_norm y)
    (hbound _ ⟨mul_le_mul_of_nonneg_left (a y).property.1 hq.le,
      mul_le_mul_of_nonneg_left (a y).property.2 hq.le⟩ (x-y))
    (norm_nonneg _) (norm_nonneg _)

lemma integrable_bilap_pair_prod (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (φ : SchwartzMap V ℂ) :
    Integrable (fun p : V × V => φ p.1 * (f p.2*bilapKernel (q*(a p.2).val) (p.1-p.2)))
      (volume.prod volume) := by
  obtain ⟨B,hB,_,_,hbound⟩ := bilapKernel_weighted_majorant (V := V) (q*α) (q*β) (mul_pos hq hα)
  apply KernelPairing.integrable_prod_of_translation_bound _
    (φ.continuous.comp continuous_fst |>.mul
      ((f.continuous.comp continuous_snd).mul
        (continuous_bilapKernel_comp (fun p : V × V => q*(a p.2).val) (fun p => p.1-p.2)
          (continuous_const.mul (continuous_subtype_val.comp (a.continuous.comp continuous_snd)))
          (continuous_fst.sub continuous_snd) (fun p => mul_pos hq (hα.trans_le (a p.2).property.1)))))
    (fun x => ‖φ x‖) B φ.integrable.norm hB ‖f‖
  intro x y
  change ‖φ x * (f y * bilapKernel (q*(a y).val) (x-y))‖ ≤ ‖φ x‖*‖f‖*B (x-y)
  rw [norm_mul,norm_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact mul_le_mul (f.toBCF.norm_coe_le_norm y)
    (hbound _ ⟨mul_le_mul_of_nonneg_left (a y).property.1 hq.le,
      mul_le_mul_of_nonneg_left (a y).property.2 hq.le⟩ (x-y))
    (norm_nonneg _) (norm_nonneg _)

lemma pair_bilaplacian_timeValue (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (φ : SchwartzMap V ℂ) :
    (∫ x, φ x * Δ (Δ (timeValue a q f)) x) =
      ∫ x, (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x * timeValue a q f x := by
  let K : V → SchwartzMap V ℂ := fun y : V => heatKernel (q*(a y).val) (mul_pos hq (hα.trans_le (a y).property.1))
  have he₀ (y x : V) : K y x = kernel (q*(a y).val) x := by
    exact congrFun (heatKernel_eq_kernel _ _) x
  have he₄ (y x : V) : (Δ (Δ (K y) : SchwartzMap V ℂ) : SchwartzMap V ℂ) x =
      bilapKernel (q*(a y).val) x := (bilapKernel_eq_schwartz _ _ x).symm
  have h₀ := integrable_kernel_pair_prod hα a q hq f (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
  have h₄ := integrable_bilap_pair_prod hα a q hq f φ
  simp_rw [bilaplacian_timeValue hα a q hq f]
  unfold timeValue
  have hp := KernelPairing.bilaplacian_pair_kernel φ f K
    (by simpa only [he₀] using h₀) (by simpa only [he₄] using h₄)
  simpa only [he₀,he₄] using hp


lemma norm_bilap_integral_le (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (B : V → ℝ) (hB : Integrable B)
    (hbound : ∀ y z, ‖bilapKernel (q*(a y).val) z‖ ≤ B z) (x : V) :
    ‖∫ y, f y*bilapKernel (q*(a y).val) (x-y)‖ ≤ ‖f‖*(∫ y, B y) := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ y, ‖f‖*B (x-y) := by
      apply integral_mono (integrable_bilapValue_integrand hα a q hq f x).norm
        ((hB.comp_sub_left x).const_mul _)
      intro y
      dsimp only
      rw [norm_mul]
      exact mul_le_mul (f.toBCF.norm_coe_le_norm y) (hbound y (x-y))
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul, integral_sub_left_eq_self]

lemma hasDerivAt_pair_timeValue (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (φ : SchwartzMap V ℂ) :
    HasDerivAt (fun s => ∫ x, φ x*timeValue a s f x)
      (-(∫ x, (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x *
        timeValue a q (C0Multiplier.mul (coefficient a) f) x)) q := by
  let f₁ := C0Multiplier.mul (coefficient a) f
  let F := fun s : ℝ => fun x : V => φ x*timeValue a s f x
  let F' := fun s : ℝ => fun x : V =>
    -(φ x*(∫ y, f₁ y*bilapKernel (s*(a y).val) (x-y)))
  have hay (y : V) : 0 < (a y).val := hα.trans_le (a y).property.1
  have hβ : 0 < β := (hay 0).trans_le (a 0).property.2
  have hFi (s : ℝ) (hs : 0 < s) : Integrable (F s) := by
    have hh := (integrable_kernel_pair_prod hα a s hs f φ).integral_prod_left
    simpa only [F,timeValue,integral_const_mul] using hh
  have hF'i (s : ℝ) (hs : 0 < s) : Integrable (F' s) := by
    have hh := (integrable_bilap_pair_prod hα a s hs f₁ φ).integral_prod_left.neg
    change Integrable (fun x => -(∫ y, φ x * (f₁ y *
      bilapKernel (s*(a y).val) (x-y)))) at hh
    simpa only [F',integral_const_mul] using hh
  obtain ⟨B,hB,_,_,hbound⟩ := bilapKernel_weighted_majorant (V := V)
    ((q/2)*α) ((2*q)*β) (by positivity)
  have hspos (s : ℝ) (hs : s ∈ Ioo (q/2) (2*q)) : 0 < s := lt_trans (by positivity) hs.1
  have hsb (s : ℝ) (hs : s ∈ Ioo (q/2) (2*q)) (y : V) :
      s*(a y).val ∈ Icc ((q/2)*α) ((2*q)*β) :=
    ⟨mul_le_mul hs.1.le (a y).property.1 hα.le (hspos s hs).le,
      mul_le_mul hs.2.le (a y).property.2 (hay y).le (by positivity)⟩
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun x => ‖φ x‖*(‖f₁‖*(∫ y, B y)))
    (s := Ioo (q/2) (2*q)) (Ioo_mem_nhds (by linarith) (by linarith))
    (by filter_upwards [Ioi_mem_nhds hq] with s hs; exact (hFi s hs).aestronglyMeasurable)
    (hFi q hq) (hF'i q hq).aestronglyMeasurable
    (Eventually.of_forall (fun x s hs => by
      simp only [F',norm_neg,norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_bilap_integral_le hα a s (hspos s hs) f₁ B hB
          (fun y z => hbound _ (hsb s hs y) z) x) (norm_nonneg _)))
    (φ.integrable.norm.mul_const _)
    (Eventually.of_forall (fun x s hs => by
      convert (hasDerivAt_timeValue hα a s (hspos s hs) f x).const_mul (φ x) using 1
      simp only [F',f₁,C0Multiplier.mul_apply,coefficient_apply,mul_neg]))
  have he : (∫ x, F' q x) = -(∫ x, (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x *
      timeValue a q f₁ x) := by
    unfold F'
    rw [integral_neg]
    congr 1
    simpa only [bilaplacian_timeValue hα a q hq f₁] using
      pair_bilaplacian_timeValue hα a q hq f₁ φ
  rw [he] at hd
  exact hd.2


lemma integrable_pair_bilaplacian (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (φ : SchwartzMap V ℂ) :
    Integrable (fun x => φ x * Δ (Δ (timeValue a q f)) x) := by
  simp_rw [bilaplacian_timeValue hα a q hq f]
  have hh := (integrable_bilap_pair_prod hα a q hq f φ).integral_prod_left
  simpa only [integral_const_mul] using hh

lemma integrable_pair_timeValue (hα : 0 < α) (a : C(V,Icc α β)) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (φ : V → ℂ) (hφ : Integrable φ) :
    Integrable (fun x => φ x * timeValue a q f x) := by
  rw [timeValue_eq_frozenOp hα a q hq f]
  exact KernelPairing.integrable_pair φ hφ (frozenOp hα a (ParabolicRadius.radius q) f).toBCF

lemma weak_frozen_residual (hα : 0 < α) (a₀ a₁ : C(V,Icc α β)) (b : V →ᵇ ℂ)
    (q : ℝ) (hq : 0 < q) (f : C₀(V,ℂ)) (φ ψ : SchwartzMap V ℂ)
    (hψ : ∀ x, ψ x = ((a₁ x).val : ℂ)*φ x) :
    deriv (fun s => ∫ x, φ x*timeValue a₀ s f x) q +
      (∫ x, (Δ (Δ ψ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x*timeValue a₀ q f x) +
      (∫ x, φ x*b x*timeValue a₀ q f x) =
      ∫ x, φ x*fullResidualCLM hα a₀ a₁ b (ParabolicRadius.radius q) f x := by
  let f₁ := C0Multiplier.mul (coefficient a₀) f
  have hD (x : V) : deriv (fun s => timeValue a₀ s f x) q =
      -Δ (Δ (timeValue a₀ q f₁)) x := by
    rw [(hasDerivAt_timeValue hα a₀ q hq f x).deriv,
      bilaplacian_timeValue hα a₀ q hq f₁]
    rfl
  have hid : Integrable (fun x => -(φ x * Δ (Δ (timeValue a₀ q f₁)) x)) :=
    (integrable_pair_bilaplacian hα a₀ q hq f₁ φ).neg
  have his := integrable_pair_bilaplacian hα a₀ q hq f ψ
  have hiz := integrable_pair_timeValue hα a₀ q hq f (fun x => φ x*b x)
    (KernelPairing.integrable_pair φ φ.integrable b)
  have he : (∫ x, -(φ x * Δ (Δ (timeValue a₀ q f₁)) x) +
      ψ x * Δ (Δ (timeValue a₀ q f)) x + φ x*b x*timeValue a₀ q f x) =
      ∫ x, φ x*fullResidualCLM hα a₀ a₁ b (ParabolicRadius.radius q) f x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [← frozen_pde_residual hα a₀ a₁ b q hq f x, hD, hψ]
    ring
  have hids : Integrable (fun x => -(φ x * Δ (Δ (timeValue a₀ q f₁)) x) +
      ψ x * Δ (Δ (timeValue a₀ q f)) x) := hid.add his
  rw [integral_add hids hiz, integral_add hid his, integral_neg,
    pair_bilaplacian_timeValue hα a₀ q hq f₁ φ,
    pair_bilaplacian_timeValue hα a₀ q hq f ψ] at he
  rw [(hasDerivAt_pair_timeValue hα a₀ q hq f φ).deriv]
  exact he

end IntegrableKernelPairProd

open scoped SchwartzMap Laplacian ZeroAtInfty BoundedContinuousFunction
open BiharmonicKernel KernelPairing
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}

def c0Time (hα : 0 < α) (a : V →ᵇ Icc α β) (q : ℝ) (f : C₀(V,ℂ)) : C₀(V,ℂ) :=
  frozenOp hα a.toContinuousMap (ParabolicRadius.radius q) f

lemma continuous_c0Time (hα : 0 < α) (a : V →ᵇ Icc α β) (f : C₀(V,ℂ)) :
    Continuous (fun q : ℝ => c0Time hα a q f) :=
  continuous_frozenOp_comp hα (fun _ => a) ParabolicRadius.radius continuous_const
    (ParabolicRadius.continuous_comp _ continuous_id) f

lemma c0Time_zero (hα : 0 < α) (a : V →ᵇ Icc α β) (f : C₀(V,ℂ)) :
    c0Time hα a 0 f = f := by
  unfold c0Time ParabolicRadius.radius
  rw [Real.zero_rpow (by norm_num : (1/4 : ℝ) ≠ 0)]
  exact frozen_zero _ _ _ _ _ _ f

lemma c0Time_apply (hα : 0 < α) (a : V →ᵇ Icc α β) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (x : V) : c0Time hα a q f x = timeValue a.toContinuousMap q f x :=
  (congrFun (timeValue_eq_frozenOp hα a.toContinuousMap q hq f) x).symm

lemma hasDerivAt_pair_c0Time (hα : 0 < α) (a : V →ᵇ Icc α β) (q : ℝ) (hq : 0 < q)
    (f : C₀(V,ℂ)) (φ : SchwartzMap V ℂ) :
    HasDerivAt (fun s => pairCLM φ φ.integrable (c0Time hα a s f))
      (-pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
        (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
        (c0Time hα a q (C0Multiplier.mul (coefficient a.toContinuousMap) f))) q := by
  have he (s : ℝ) (hs : 0 < s) (g : C₀(V,ℂ)) (ψ : SchwartzMap V ℂ) :
      pairCLM ψ ψ.integrable (c0Time hα a s g) = ∫ x, ψ x*timeValue a.toContinuousMap s g x := by
    simp only [pairCLM_apply,c0Time_apply hα a s hs g]
  rw [he q hq]
  apply (hasDerivAt_pair_timeValue hα a.toContinuousMap q hq f φ).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with s hs
  exact he s hs f φ

lemma pair_c0Time_integral (hα : 0 < α) (a : V →ᵇ Icc α β) (q : ℝ) (hq : 0 ≤ q)
    (f : C₀(V,ℂ)) (φ : SchwartzMap V ℂ) :
    pairCLM φ φ.integrable (c0Time hα a q f) = pairCLM φ φ.integrable f -
      ∫ s in (0 : ℝ)..q,
        pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
          (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
          (c0Time hα a s (C0Multiplier.mul (coefficient a.toContinuousMap) f)) := by
  let L := pairCLM φ φ.integrable
  let M := pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
      (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
  let f₁ := C0Multiplier.mul (coefficient a.toContinuousMap) f
  have hc := L.continuous.comp (continuous_c0Time hα a f)
  have hd := (M.continuous.comp (continuous_c0Time hα a f₁)).neg
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hq hc.continuousOn
    (fun s hs => hasDerivAt_pair_c0Time hα a s hs.1 f φ) (hd.intervalIntegrable 0 q)
  change (∫ y in (0 : ℝ)..q, -M (c0Time hα a y f₁)) =
    L (c0Time hα a q f) - L (c0Time hα a 0 f) at hh
  rw [c0Time_zero, intervalIntegral.integral_neg] at hh
  change L (c0Time hα a q f) = L f - ∫ s in (0 : ℝ)..q, M (c0Time hα a s f₁)
  dsimp only [L] at hh ⊢
  linear_combination -hh

end FrozenParametrix

namespace StrongWeightedVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {T : ℝ}

lemma continuous_unweighted_on_time (j : Time T →ᵇ E) :
    Continuous (fun t : Time T => unweighted j t.val) := by
  simp_rw [unweighted_at_time]
  exact (continuous_subtype_val.rpow_const (fun t => Or.inl t.property.1.ne')).smul j.continuous

lemma stronglyMeasurable_unweighted (j : Time T →ᵇ E) : StronglyMeasurable (unweighted j) := by
  classical
  unfold unweighted
  apply StronglyMeasurable.dite (s := Time T)
    (f := fun t : Time T => t.val^(-3/4 : ℝ) • j t)
    (g := fun _ => (0 : E)) _ stronglyMeasurable_const measurableSet_Ioc
  exact ((continuous_subtype_val.rpow_const (fun t : Time T => Or.inl t.property.1.ne')).smul
    j.continuous).stronglyMeasurable

lemma norm_unweighted_le (j : Time T →ᵇ E) (r : ℝ) (hr : 0 < r) :
    ‖unweighted j r‖ ≤ r^(-3/4 : ℝ)*‖j‖ := by
  by_cases hrt : r ≤ T
  · rw [unweighted,dite_eq_left (show r ∈ Ioc 0 T from ⟨hr,hrt⟩),norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr.le _)]
    exact mul_le_mul_of_nonneg_left (j.norm_coe_le_norm _) (Real.rpow_nonneg hr.le _)
  · rw [unweighted,dite_eq_right (by simpa only [mem_Ioc,not_and,not_le] using fun _ => lt_of_not_ge hrt),norm_zero]
    positivity

lemma intervalIntegrable_unweighted (j : Time T →ᵇ E) (t : ℝ) (ht : 0 ≤ t) :
    IntervalIntegrable (unweighted j) volume 0 t := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).mpr
  have hp : IntegrableOn (fun r : ℝ => r^(-3/4 : ℝ)*‖j‖) (Ioo 0 t) := by
    rcases eq_or_lt_of_le ht with he | ht'
    · subst t; simp
    · exact ((intervalIntegral.integrableOn_Ioo_rpow_iff ht').mpr (by norm_num)).mul_const ‖j‖
  apply hp.mono' (stronglyMeasurable_unweighted j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact norm_unweighted_le j r hr.1

end StrongWeightedVolterra

namespace VolterraIntegral
section IntegralTriangleLeft
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : ℝ}

lemma integral_triangle_left (F : ℝ → ℝ → E) (hT : 0 ≤ T) (r : ℝ)
    (hr : r ∈ Icc 0 T) :
    (∫ s in (0 : ℝ)..T, if s < r then F r s else 0) = ∫ s in (0 : ℝ)..r, F r s := by
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hr.1]
  change (∫ s in Ioc (0 : ℝ) T, (Iio r).indicator (F r) s) = _
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have he : Iio r ∩ Ioc (0 : ℝ) T = Ioo 0 r := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨hxr,hx0,_⟩; exact ⟨hx0,hxr⟩
    · rintro ⟨hx0,hxr⟩; exact ⟨hxr,hx0,hxr.le.trans hr.2⟩
  rw [he, integral_Ioc_eq_integral_Ioo]

lemma integral_triangle_right (F : ℝ → ℝ → E) (hT : 0 ≤ T) (s : ℝ)
    (hs : s ∈ Icc 0 T) :
    (∫ r in (0 : ℝ)..T, if s < r then F r s else 0) = ∫ r in s..T, F r s := by
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hs.2]
  change (∫ r in Ioc (0 : ℝ) T, (Ioi s).indicator (fun r => F r s) r) = _
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi s ∩ Ioc (0 : ℝ) T = Ioc s T := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨hsx,_,hxT⟩; exact ⟨hsx,hxT⟩
    · rintro ⟨hsx,hxT⟩; exact ⟨hsx,lt_of_le_of_lt hs.1 hsx,hxT⟩
  rw [he]

lemma integral_triangle_swap (F : ℝ → ℝ → E) (hT : 0 ≤ T)
    (hF : IntegrableOn (fun p : ℝ × ℝ => if p.2 < p.1 then F p.1 p.2 else 0)
      (Ioc 0 T ×ˢ Ioc 0 T)) :
    (∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..r, F r s) =
      ∫ s in (0 : ℝ)..T, ∫ r in s..T, F r s := by
  have hh := intervalIntegral_intervalIntegral_swap
    (F := fun r s => if s < r then F r s else 0)
    (a := 0) (b := T) (c := 0) (d := T) (by simpa only [uIoc_of_le hT, Function.uncurry_def] using hF)
  calc
    _ = ∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..T, if s < r then F r s else 0 := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact (integral_triangle_left F hT r (by simpa only [uIcc_of_le hT] using hr)).symm
    _ = _ := hh
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact integral_triangle_right F hT s (by simpa only [uIcc_of_le hT] using hs)

end IntegralTriangleLeft

section IntegrableOnTriangleOfBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : ℝ}

omit [NormedSpace ℝ E] in

lemma integrableOn_triangle_of_bound (F : ℝ → ℝ → E)
    (hF : AEStronglyMeasurable
      (fun p : ℝ × ℝ => if p.2 < p.1 then F p.1 p.2 else 0)
      (volume.restrict (Ioc 0 T ×ˢ Ioc 0 T)))
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioc 0 T))
    (hB0 : ∀ s ∈ Ioc 0 T, 0 ≤ B s)
    (hbound : ∀ r ∈ Ioc 0 T, ∀ s ∈ Ioc 0 T, s < r → ‖F r s‖ ≤ B s) :
    IntegrableOn (fun p : ℝ × ℝ => if p.2 < p.1 then F p.1 p.2 else 0)
      (Ioc 0 T ×ˢ Ioc 0 T) := by
  have hb : IntegrableOn (fun p : ℝ × ℝ => B p.2) (Ioc 0 T ×ˢ Ioc 0 T) := by
    have hh := hB.comp_snd (volume.restrict (Ioc (0 : ℝ) T))
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod, IntegrableOn] using hh
  refine hb.mono' hF ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  by_cases hlt : p.2 < p.1
  · simpa only [ite_eq_left hlt] using hbound p.1 hp.1 p.2 hp.2 hlt
  · simpa only [ite_eq_right hlt, norm_zero] using hB0 p.2 hp.2

lemma duhamel_integral_identity (A F : ℝ → ℝ → E) (d : ℝ → E) (hT : 0 ≤ T)
    (hA : IntervalIntegrable (A T) volume 0 T)
    (hd : IntervalIntegrable d volume 0 T)
    (hF : IntegrableOn (fun p : ℝ × ℝ => if p.2 < p.1 then F p.1 p.2 else 0)
      (Ioc 0 T ×ˢ Ioc 0 T))
    (hFTC : ∀ s ∈ Ioo 0 T, A T s - d s = ∫ r in s..T, F r s) :
    (∫ s in (0 : ℝ)..T, A T s) = (∫ s in (0 : ℝ)..T, d s) +
      ∫ r in (0 : ℝ)..T, ∫ s in (0 : ℝ)..r, F r s := by
  rw [integral_triangle_swap F hT hF]
  have he : (∫ s in (0 : ℝ)..T, A T s - d s) =
      ∫ s in (0 : ℝ)..T, ∫ r in s..T, F r s := by
    exact intervalIntegral.integral_congr_Ioo_of_le hT hFTC
  rw [intervalIntegral.integral_sub hA hd] at he
  exact sub_eq_iff_eq_add'.mp he

end IntegrableOnTriangleOfBound

variable {E : Type*} [NormedAddCommGroup E]
variable {T : ℝ}

def sourceExtend (F : ℝ × Ioc (0 : ℝ) T → E) (r s : ℝ) : E :=
  if hs : s ∈ Ioc (0 : ℝ) T then F (r,⟨s,hs⟩) else 0

lemma sourceExtend_apply (F : ℝ × Ioc (0 : ℝ) T → E) (r s : ℝ) (hs : s ∈ Ioc (0 : ℝ) T) :
    sourceExtend F r s = F (r,⟨s,hs⟩) := by rw [sourceExtend,dite_eq_left hs]

lemma stronglyMeasurable_sourceExtend (F : ℝ × Ioc (0 : ℝ) T → E) (hF : Continuous F) :
    StronglyMeasurable (fun p : ℝ × ℝ => sourceExtend F p.1 p.2) := by
  classical
  let D : Set (ℝ × ℝ) := {p | p.2 ∈ Ioc (0 : ℝ) T}
  let G : D → ℝ × Ioc (0 : ℝ) T := fun p => (p.val.1,⟨p.val.2,p.property⟩)
  have hG : Continuous G := by
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  have hD : MeasurableSet D := measurableSet_Ioc.preimage measurable_snd
  exact StronglyMeasurable.dite (s := D) (f := F ∘ G) (g := fun _ => 0)
    (hF.comp hG).stronglyMeasurable stronglyMeasurable_const hD

lemma integrableOn_sourceExtend (F : ℝ × Ioc (0 : ℝ) T → E) (hF : Continuous F)
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioc 0 T))
    (hbound : ∀ (r : ℝ) (s : Ioc (0 : ℝ) T), ‖F (r,s)‖ ≤ B s.val) (r : ℝ) :
    IntegrableOn (sourceExtend F r) (Ioc 0 T) := by
  apply hB.mono'
  · exact ((stronglyMeasurable_sourceExtend F hF).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [sourceExtend_apply F r s hs]
    exact hbound r ⟨s,hs⟩

lemma integrableOn_sourceExtend_triangle (F : ℝ × Ioc (0 : ℝ) T → E) (hF : Continuous F)
    (B : ℝ → ℝ) (hB : IntegrableOn B (Ioc 0 T))
    (hbound : ∀ (r : ℝ) (s : Ioc (0 : ℝ) T), ‖F (r,s)‖ ≤ B s.val) :
    IntegrableOn (fun p : ℝ × ℝ => if p.2 < p.1 then sourceExtend F p.1 p.2 else 0)
      (Ioc 0 T ×ˢ Ioc 0 T) := by
  apply integrableOn_triangle_of_bound (sourceExtend F)
    (((stronglyMeasurable_sourceExtend F hF).ite
      (measurableSet_lt measurable_snd measurable_fst) stronglyMeasurable_const).aestronglyMeasurable)
    B hB
  · intro s hs
    exact (norm_nonneg _).trans (hbound 0 ⟨s,hs⟩)
  · intro r _ s hs _
    rw [sourceExtend_apply F r s hs]
    exact hbound r ⟨s,hs⟩

end VolterraIntegral

namespace FrozenParametrix
open scoped ZeroAtInfty BoundedContinuousFunction
open StrongWeightedVolterra ParametrixVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}

lemma continuous_c0Time_comp {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (hα : 0 < α) (a : X → V →ᵇ Icc α β) (q : X → ℝ) (f : X → C₀(V,ℂ))
    (ha : Continuous a) (hq : Continuous q) (hf : Continuous f) :
    Continuous (fun x => c0Time hα (a x) (q x) (f x)) := by
  have h := continuous_apply_of_strong
    (fun x => frozenCLM hα (a x).toContinuousMap (ParabolicRadius.radius (q x)))
    (fun d => continuous_frozenOp_comp hα a (fun x => ParabolicRadius.radius (q x)) ha
      (ParabolicRadius.continuous_comp q hq) d)
    (frozenBound (V := V) (β := β) hα) (frozenBound_nonneg hα)
    (fun x => norm_frozenCLM_le hα (a x).toContinuousMap (ParabolicRadius.radius (q x)))
  have hh := h.comp (continuous_id.prodMk hf)
  simpa only [Function.comp_def, id_eq, frozenCLM_apply, c0Time] using hh

lemma norm_c0Time_le (hα : 0 < α) (a : V →ᵇ Icc α β) (q : ℝ) (f : C₀(V,ℂ)) :
    ‖c0Time hα a q f‖ ≤ frozenBound (V := V) (β := β) hα * ‖f‖ := by
  exact (frozenCLM hα a.toContinuousMap (ParabolicRadius.radius q)).le_opNorm f |>.trans
    (mul_le_mul_of_nonneg_right (norm_frozenCLM_le hα a.toContinuousMap _) (norm_nonneg _))

end FrozenParametrix

namespace ParametrixVolterra
section ContinuousSourceMultiply
open scoped ZeroAtInfty BoundedContinuousFunction SchwartzMap Laplacian
open FrozenParametrix StrongWeightedVolterra KernelPairing
variable {V : Type} [NormedAddCommGroup V]
variable {T α β : ℝ}
variable (A : C(Slab T,V →ᵇ Icc α β))

lemma continuous_sourceMultiply (j : Time T →ᵇ C₀(V,ℂ)) :
    Continuous (fun t : Time T => C0Multiplier.mul (coefficient (A (now t)).toContinuousMap) (j t)) :=
  C0Multiplier.continuous_mul_joint.comp
    ((continuous_coefficient_comp (fun t => A (now t)) (A.continuous.comp continuous_now)).prodMk j.continuous)

lemma norm_sourceMultiply_le (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T) :
    ‖C0Multiplier.mul (coefficient (A (now t)).toContinuousMap) (j t)‖ ≤ max |α| |β| * ‖j‖ :=
  (C0Multiplier.norm_mul_le _ _).trans
    (mul_le_mul (norm_coefficient_le _) (j.norm_coe_le_norm t) (norm_nonneg _)
      ((abs_nonneg α).trans (le_max_left _ _)))

def sourceMultiply (j : Time T →ᵇ C₀(V,ℂ)) : Time T →ᵇ C₀(V,ℂ) :=
  .ofNormedAddCommGroup _ (continuous_sourceMultiply A j) _ (norm_sourceMultiply_le A j)

lemma sourceMultiply_apply (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T) :
    sourceMultiply A j t = C0Multiplier.mul (coefficient (A (now t)).toContinuousMap) (j t) := rfl

lemma unweighted_sourceMultiply (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T) :
    unweighted (sourceMultiply A j) t.val =
      C0Multiplier.mul (coefficient (A (now t)).toContinuousMap) (unweighted j t.val) := by
  rw [unweighted_at_time,unweighted_at_time,sourceMultiply_apply]
  ext x
  simp only [ZeroAtInftyContinuousMap.smul_apply,C0Multiplier.mul_apply]
  rw [mul_smul_comm]

end ContinuousSourceMultiply

open scoped ZeroAtInfty BoundedContinuousFunction SchwartzMap Laplacian
open FrozenParametrix StrongWeightedVolterra KernelPairing VolterraIntegral
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}
variable (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β))

def sourceFrozen (j : Time T →ᵇ C₀(V,ℂ)) (p : ℝ × Time T) : C₀(V,ℂ) :=
  c0Time hα (A (now p.2)) (p.1-p.2.val) (unweighted j p.2.val)

lemma continuous_sourceFrozen (j : Time T →ᵇ C₀(V,ℂ)) : Continuous (sourceFrozen hα A j) :=
  continuous_c0Time_comp hα _ _ _
    (A.continuous.comp (continuous_now.comp continuous_snd))
    (continuous_fst.sub (continuous_subtype_val.comp continuous_snd))
    ((continuous_unweighted_on_time j).comp continuous_snd)

lemma norm_sourceFrozen_le (j : Time T →ᵇ C₀(V,ℂ)) (p : ℝ × Time T) :
    ‖sourceFrozen hα A j p‖ ≤ frozenBound (V := V) (β := β) hα *
      (p.2.val^(-3/4 : ℝ)*‖j‖) :=
  (norm_c0Time_le hα _ _ _).trans (mul_le_mul_of_nonneg_left
    (norm_unweighted_le j p.2.val p.2.property.1) (frozenBound_nonneg hα))

lemma integrableOn_sourceFrozen_bound (j : Time T →ᵇ C₀(V,ℂ)) :
    IntegrableOn (fun s : ℝ => frozenBound (V := V) (β := β) hα*(s^(-3/4 : ℝ)*‖j‖)) (Ioc 0 T) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (by norm_num : (-1:ℝ) < -3/4)).mul_const ‖j‖ |>.const_mul (frozenBound (V := V) (β := β) hα)
  exact h.1

lemma integrableOn_sourceFrozen_triangle (j : Time T →ᵇ C₀(V,ℂ)) :
    IntegrableOn (fun p : ℝ × ℝ => if p.2 < p.1 then
      sourceExtend (sourceFrozen hα A j) p.1 p.2 else 0) (Ioc 0 T ×ˢ Ioc 0 T) :=
  integrableOn_sourceExtend_triangle _ (continuous_sourceFrozen hα A j) _
    (integrableOn_sourceFrozen_bound hα j) (fun r s => norm_sourceFrozen_le hα A j (r,s))

lemma intervalIntegrable_sourceFrozen (j : Time T →ᵇ C₀(V,ℂ)) (r t : ℝ) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (sourceExtend (sourceFrozen hα A j) r) volume 0 t := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
  exact (integrableOn_sourceExtend _ (continuous_sourceFrozen hα A j) _
    (integrableOn_sourceFrozen_bound hα j) (fun r s => norm_sourceFrozen_le hα A j (r,s)) r).mono_set
      (Ioc_subset_Ioc le_rfl ht.2)

def duhamel (j : Time T →ᵇ C₀(V,ℂ)) (t : ℝ) : C₀(V,ℂ) :=
  ∫ s in (0 : ℝ)..t, sourceExtend (sourceFrozen hα A j) t s

lemma sourceFrozen_eq_frozenRaw (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ))
    (t : Time T) (s : ℝ) (hs : s ∈ Ioo 0 t.val) :
    sourceExtend (sourceFrozen hα A j) t.val s = frozenRaw hα A hT t s (unweighted j s) := by
  have hsT : s ∈ Ioc (0 : ℝ) T := ⟨hs.1,hs.2.le.trans t.property.2⟩
  have hsT' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le,hsT.2⟩
  rw [sourceExtend_apply _ _ _ hsT,frozenRaw,ite_eq_left hs,projIcc_of_mem hT hsT']
  rfl

lemma duhamel_eq_value (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T) :
    duhamel hα A j t.val = MildVolterra.value (mildKernel hα A) j t := by
  rw [duhamel,MildVolterra.value_eq_integral]
  apply intervalIntegral.integral_congr_Ioo_of_le t.property.1.le
  intro s hs
  dsimp only
  rw [rawKernel_eq_frozenRaw hα A hT]
  exact sourceFrozen_eq_frozenRaw hα A hT j t s hs

lemma continuousOn_duhamel (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) :
    ContinuousOn (duhamel hα A j) (Ioc 0 T) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun t : Time T => duhamel hα A j t.val)
  simp_rw [duhamel_eq_value hα A hT j]
  exact MildVolterra.continuous_value (mildKernel hα A) (frozenBound (V := V) (β := β) hα)
    (frozenBound_nonneg hα) (norm_mildKernel_le hα A) j

lemma continuousAt_duhamel (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    ContinuousAt (duhamel hα A j) t :=
  (continuousOn_duhamel hα A hT j).continuousAt (Ioc_mem_nhds ht.1 ht.2)


lemma integrableOn_pair_sourceFrozen_triangle (j : Time T →ᵇ C₀(V,ℂ))
    (L : C₀(V,ℂ) →L[ℂ] ℂ) :
    IntegrableOn (fun p : ℝ × ℝ => if p.2 < p.1 then
      L (sourceExtend (sourceFrozen hα A j) p.1 p.2) else 0) (Ioc 0 T ×ˢ Ioc 0 T) := by
  have hh := L.integrable_comp (integrableOn_sourceFrozen_triangle hα A j)
  simpa only [IntegrableOn,apply_ite,map_zero] using hh

lemma sourceFrozen_weakFTC (j : Time T →ᵇ C₀(V,ℂ)) (φ : SchwartzMap V ℂ)
    (t : ℝ) (ht : t ∈ Icc 0 T) (s : ℝ) (hs : s ∈ Ioo 0 t) :
    pairCLM φ φ.integrable (sourceExtend (sourceFrozen hα A j) t s) -
      pairCLM φ φ.integrable (unweighted j s) =
      ∫ r in s..t, -pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
        (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
        (sourceExtend (sourceFrozen hα A (sourceMultiply A j)) r s) := by
  have hsT : s ∈ Ioc (0 : ℝ) T := ⟨hs.1,hs.2.le.trans ht.2⟩
  let s₁ : Time T := ⟨s,hsT⟩
  let M := pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
    (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
  let f₁ := C0Multiplier.mul (coefficient (A (now s₁)).toContinuousMap) (unweighted j s)
  have he (r : ℝ) : sourceExtend (sourceFrozen hα A (sourceMultiply A j)) r s =
      c0Time hα (A (now s₁)) (r-s) f₁ := by
    rw [sourceExtend_apply _ _ _ hsT]
    change c0Time hα (A (now s₁)) (r-s) (unweighted (sourceMultiply A j) s₁.val) = _
    rw [unweighted_sourceMultiply]
  have hh := pair_c0Time_integral hα (A (now s₁)) (t-s) (sub_nonneg.mpr hs.2.le)
    (unweighted j s) φ
  simp_rw [he]
  change pairCLM φ φ.integrable (sourceExtend (sourceFrozen hα A j) t s) -
    pairCLM φ φ.integrable (unweighted j s) = ∫ r in s..t, -M (c0Time hα (A (now s₁)) (r-s) f₁)
  rw [intervalIntegral.integral_neg,intervalIntegral.integral_comp_sub_right
    (fun q => M (c0Time hα (A (now s₁)) q f₁)) s,sub_self,
    sourceExtend_apply _ _ _ hsT]
  change pairCLM φ φ.integrable (c0Time hα (A (now s₁)) (t-s) (unweighted j s)) -
    pairCLM φ φ.integrable (unweighted j s) = -∫ q in (0 : ℝ)..t-s, M (c0Time hα (A (now s₁)) q f₁)
  exact sub_eq_iff_eq_add.mpr (by convert hh using 1; abel)

lemma pair_duhamel_integral (j : Time T →ᵇ C₀(V,ℂ)) (φ : SchwartzMap V ℂ)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    pairCLM φ φ.integrable (duhamel hα A j t) =
      (∫ s in (0 : ℝ)..t, pairCLM φ φ.integrable (unweighted j s)) -
      ∫ r in (0 : ℝ)..t, pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
        (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
        (duhamel hα A (sourceMultiply A j) r) := by
  let L := pairCLM φ φ.integrable
  let M := pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
    (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
  let K := sourceExtend (sourceFrozen hα A j)
  let Q := sourceExtend (sourceFrozen hα A (sourceMultiply A j))
  have hK := intervalIntegrable_sourceFrozen hα A j t t ht
  have hu := intervalIntegrable_unweighted j t ht.1
  have hA : IntervalIntegrable (fun s => L (K t s)) volume 0 t :=
    ⟨L.integrable_comp hK.1,L.integrable_comp hK.2⟩
  have hd : IntervalIntegrable (fun s => L (unweighted j s)) volume 0 t :=
    ⟨L.integrable_comp hu.1,L.integrable_comp hu.2⟩
  have hQ := (integrableOn_pair_sourceFrozen_triangle hα A (sourceMultiply A j) M).neg
  have hQt : IntegrableOn (fun p : ℝ × ℝ => if p.2 < p.1 then -M (Q p.1 p.2) else 0)
      (Ioc 0 t ×ˢ Ioc 0 t) := by
    have he : (fun p : ℝ × ℝ => if p.2 < p.1 then -M (Q p.1 p.2) else 0) =
        (fun p : ℝ × ℝ => -(if p.2 < p.1 then M (Q p.1 p.2) else 0)) := by
      funext p; split_ifs <;> simp
    rw [he]
    exact hQ.mono_set (Set.prod_mono (Ioc_subset_Ioc le_rfl ht.2) (Ioc_subset_Ioc le_rfl ht.2))
  have hh := duhamel_integral_identity (fun r s => L (K r s)) (fun r s => -M (Q r s))
    (fun s => L (unweighted j s)) ht.1 hA hd hQt (sourceFrozen_weakFTC hα A j φ t ht)
  have he : (∫ r in (0 : ℝ)..t, ∫ s in (0 : ℝ)..r, -M (Q r s)) =
      -(∫ r in (0 : ℝ)..t, M (duhamel hα A (sourceMultiply A j) r)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro r hr
    dsimp only
    rw [intervalIntegral.integral_neg]
    congr 1
    exact M.intervalIntegral_comp_comm (intervalIntegrable_sourceFrozen hα A (sourceMultiply A j) r r
      ⟨hr.1.le,hr.2.le.trans ht.2⟩)
  rw [he] at hh
  rw [L.intervalIntegral_comp_comm hK] at hh
  exact hh


lemma duhamel_zero (j : Time T →ᵇ C₀(V,ℂ)) : duhamel hα A j 0 = 0 := by simp [duhamel]

lemma norm_duhamel_le (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖duhamel hα A j t‖ ≤ t^(1/4 : ℝ)*
      ((∫ u : UnitTime, MildVolterra.massWeight u)*frozenBound (V := V) (β := β) hα*‖j‖) := by
  rcases eq_or_lt_of_le ht.1 with he | ht0
  · subst t; rw [duhamel_zero,norm_zero,Real.zero_rpow (by norm_num : (1/4 : ℝ) ≠ 0),zero_mul]
  · let t₁ : Time T := ⟨t,ht0,ht.2⟩
    change ‖duhamel hα A j t₁.val‖ ≤ _
    rw [duhamel_eq_value hα A hT]
    exact MildVolterra.norm_value_le (mildKernel hα A) (frozenBound (V := V) (β := β) hα)
      (frozenBound_nonneg hα) (norm_mildKernel_le hα A) j t₁

lemma continuousWithinAt_duhamel_zero (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) :
    ContinuousWithinAt (duhamel hα A j) (Icc 0 T) 0 := by
  change Tendsto (duhamel hα A j) (𝓝[Icc 0 T] 0) (𝓝 (duhamel hα A j 0))
  rw [duhamel_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _))
    (show ∀ᶠ t in 𝓝[Icc 0 T] 0, ‖duhamel hα A j t‖ ≤ t^(1/4 : ℝ)*
      ((∫ u : UnitTime, MildVolterra.massWeight u)*frozenBound (V := V) (β := β) hα*‖j‖) from
      by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact norm_duhamel_le hα A hT j t ht)
  have hc : Continuous (fun t : ℝ => t^(1/4 : ℝ)*
      ((∫ u : UnitTime, MildVolterra.massWeight u)*frozenBound (V := V) (β := β) hα*‖j‖)) :=
    (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 1/4)).mul_const _
  simpa only [Real.zero_rpow (by norm_num : (1/4 : ℝ) ≠ 0),zero_mul] using
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds

lemma continuousOn_duhamel_Icc (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) :
    ContinuousOn (duhamel hα A j) (Icc 0 T) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with he | ht0
  · subst t; exact continuousWithinAt_duhamel_zero hα A hT j
  · apply ((continuousOn_duhamel hα A hT j) t ⟨ht0,ht.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht0)] with r hr hr0
    exact ⟨hr0,hr.2⟩

lemma intervalIntegrable_duhamel (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (duhamel hα A j) volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht.1]
  exact (continuousOn_duhamel_Icc hα A hT j).mono (Icc_subset_Icc le_rfl ht.2)

lemma hasDerivAt_pair_duhamel (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) (φ : SchwartzMap V ℂ)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => pairCLM φ φ.integrable (duhamel hα A j r))
      (pairCLM φ φ.integrable (unweighted j t) -
        pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
          (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
          (duhamel hα A (sourceMultiply A j) t)) t := by
  let L := pairCLM φ φ.integrable
  let M := pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
    (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
  have hu := intervalIntegrable_unweighted j t ht.1.le
  have hD := intervalIntegrable_duhamel hα A hT (sourceMultiply A j) t ⟨ht.1.le,ht.2.le⟩
  have huc : ContinuousOn (unweighted j) (Ioc 0 T) :=
    continuousOn_iff_continuous_domRestrict.mpr (continuous_unweighted_on_time j)
  have hc₁ : ContinuousOn (fun r => L (unweighted j r)) (Ioo 0 T) :=
    L.continuous.comp_continuousOn (huc.mono Ioo_subset_Ioc_self)
  have hc₂ : ContinuousOn (fun r => M (duhamel hα A (sourceMultiply A j) r)) (Ioo 0 T) :=
    M.continuous.comp_continuousOn ((continuousOn_duhamel hα A hT _).mono Ioo_subset_Ioc_self)
  have hd₁ := intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable (fun r => L (unweighted j r)) volume 0 t from
      ⟨L.integrable_comp hu.1,L.integrable_comp hu.2⟩)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hc₁ t ht)
    (hc₁.continuousAt (Ioo_mem_nhds ht.1 ht.2))
  have hd₂ := intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable (fun r => M (duhamel hα A (sourceMultiply A j) r)) volume 0 t from
      ⟨M.integrable_comp hD.1,M.integrable_comp hD.2⟩)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hc₂ t ht)
    (hc₂.continuousAt (Ioo_mem_nhds ht.1 ht.2))
  apply (hd₁.sub hd₂).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact pair_duhamel_integral hα A j φ r ⟨hr.1.le,hr.2.le⟩

end ParametrixVolterra

namespace FrozenParametrix
open scoped SchwartzMap Laplacian ZeroAtInfty BoundedContinuousFunction
open BiharmonicKernel KernelPairing
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}

lemma pair_fullResidual (hα : 0 < α) (a₀ a₁ : V →ᵇ Icc α β) (b : V →ᵇ ℂ)
    (q : ℝ) (hq : 0 < q) (f : C₀(V,ℂ)) (φ ψ : SchwartzMap V ℂ)
    (hψ : ∀ x, ψ x = ((a₁ x).val : ℂ)*φ x) :
    pairCLM φ φ.integrable (fullResidualCLM hα a₀.toContinuousMap a₁.toContinuousMap b
      (ParabolicRadius.radius q) f) =
      -pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
        (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
        (c0Time hα a₀ q (C0Multiplier.mul (coefficient a₀.toContinuousMap) f)) +
      pairCLM (Δ (Δ ψ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
        (Δ (Δ ψ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable (c0Time hα a₀ q f) +
      pairCLM (fun x => φ x*b x) (integrable_pair φ φ.integrable b) (c0Time hα a₀ q f) := by
  have h := weak_frozen_residual hα a₀.toContinuousMap a₁.toContinuousMap b q hq f φ ψ hψ
  rw [(hasDerivAt_pair_timeValue hα a₀.toContinuousMap q hq f φ).deriv] at h
  simpa only [pairCLM_apply,c0Time_apply hα a₀ q hq] using h.symm

end FrozenParametrix

namespace ParametrixVolterra
open scoped ZeroAtInfty BoundedContinuousFunction SchwartzMap Laplacian
open FrozenParametrix StrongWeightedVolterra KernelPairing VolterraIntegral
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}
variable (hα : 0 < α) (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))

def adjointPair (t : Time T) (φ ψ : SchwartzMap V ℂ) : C₀(V,ℂ) →L[ℂ] ℂ :=
  pairCLM (Δ (Δ ψ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
    (Δ (Δ ψ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable +
  pairCLM (fun x => φ x*b (now t) x) (integrable_pair φ φ.integrable (b (now t)))

lemma pair_residualKernel (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T)
    (φ ψ : SchwartzMap V ℂ) (hψ : ∀ x, ψ x = ((A (now t) x).val : ℂ)*φ x)
    (s : ℝ) (hs : s ∈ Ioo 0 t.val) :
    pairCLM φ φ.integrable (residualKernel hα A b hT t s (unweighted j s)) =
      -pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
        (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
        (sourceExtend (sourceFrozen hα A (sourceMultiply A j)) t.val s) +
      adjointPair b t φ ψ (sourceExtend (sourceFrozen hα A j) t.val s) := by
  have hsT : s ∈ Ioc (0:ℝ) T := ⟨hs.1,hs.2.le.trans t.property.2⟩
  have hsT' : s ∈ Icc (0:ℝ) T := ⟨hs.1.le,hsT.2⟩
  let s₁ : Time T := ⟨s,hsT⟩
  rw [residualKernel,ite_eq_left hs,projIcc_of_mem hT hsT']
  rw [sourceExtend_apply _ _ _ hsT,sourceExtend_apply _ _ _ hsT]
  change pairCLM φ φ.integrable (actualResidual hα A b t (now s₁) (unweighted j s)) = _
  dsimp only [sourceFrozen]
  rw [show unweighted (sourceMultiply A j) s =
    C0Multiplier.mul (coefficient (A (now s₁)).toContinuousMap) (unweighted j s) from
      unweighted_sourceMultiply A j s₁]
  simpa only [actualResidual,adjointPair,add_apply,now,s₁,add_assoc] using
    pair_fullResidual hα (A (now s₁)) (A (now t)) (b (now t)) (t.val-s)
      (sub_pos.mpr hs.2) (unweighted j s) φ ψ hψ

lemma pair_integral_residualKernel (hT : 0 ≤ T) (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T)
    (hi : IntervalIntegrable (fun s => residualKernel hα A b hT t s (unweighted j s)) volume 0 t.val)
    (φ ψ : SchwartzMap V ℂ) (hψ : ∀ x, ψ x = ((A (now t) x).val : ℂ)*φ x) :
    pairCLM φ φ.integrable (∫ s in (0:ℝ)..t.val, residualKernel hα A b hT t s (unweighted j s)) =
      -pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
        (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
        (duhamel hα A (sourceMultiply A j) t.val) +
      adjointPair b t φ ψ (duhamel hα A j t.val) := by
  let L := pairCLM φ φ.integrable
  let M := pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
    (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
  let N := adjointPair b t φ ψ
  have hi₁ := intervalIntegrable_sourceFrozen hα A (sourceMultiply A j) t.val t.val
    ⟨t.property.1.le,t.property.2⟩
  have hi₂ := intervalIntegrable_sourceFrozen hα A j t.val t.val ⟨t.property.1.le,t.property.2⟩
  have hm : IntervalIntegrable (fun s => M (sourceExtend (sourceFrozen hα A (sourceMultiply A j)) t.val s)) volume 0 t.val :=
    ⟨M.integrable_comp hi₁.1,M.integrable_comp hi₁.2⟩
  have hn : IntervalIntegrable (fun s => N (sourceExtend (sourceFrozen hα A j) t.val s)) volume 0 t.val :=
    ⟨N.integrable_comp hi₂.1,N.integrable_comp hi₂.2⟩
  rw [← L.intervalIntegral_comp_comm hi]
  calc
    _ = ∫ s in (0:ℝ)..t.val,
        -M (sourceExtend (sourceFrozen hα A (sourceMultiply A j)) t.val s) +
        N (sourceExtend (sourceFrozen hα A j) t.val s) := by
      apply intervalIntegral.integral_congr_Ioo_of_le t.property.1.le
      intro s hs
      exact pair_residualKernel hα A b hT j t φ ψ hψ s hs
    _ = _ := by
      rw [intervalIntegral.integral_add (f := fun s => -M (sourceExtend (sourceFrozen hα A (sourceMultiply A j)) t.val s))
        (g := fun s => N (sourceExtend (sourceFrozen hα A j) t.val s)) hm.neg hn,intervalIntegral.integral_neg,
        M.intervalIntegral_comp_comm hi₁,N.intervalIntegral_comp_comm hi₂]
      rfl

def mildTime (hT : 0 ≤ T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ)) (t : ℝ) : C₀(V,ℂ) :=
  c0Time hα (A (initial hT)) t d + duhamel hα A j t

lemma mildTime_zero (hT : 0 ≤ T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ)) :
    mildTime hα A hT d j 0 = d := by rw [mildTime,c0Time_zero,duhamel_zero,add_zero]

lemma continuousOn_mildTime (hT : 0 ≤ T) (d : C₀(V,ℂ)) (j : Time T →ᵇ C₀(V,ℂ)) :
    ContinuousOn (mildTime hα A hT d j) (Icc 0 T) :=
  (continuous_c0Time hα (A (initial hT)) d).continuousOn.add (continuousOn_duhamel_Icc hα A hT j)

lemma hasDerivAt_pair_mildTime (hT : 0 ≤ T) (d : C₀(V,ℂ)) (j l : Time T →ᵇ C₀(V,ℂ))
    (hi : ∀ t : Time T, IntervalIntegrable
      (fun s => residualKernel hα A b hT t s (unweighted j s)) volume 0 t.val)
    (hj : ∀ t : Time T, unweighted j t.val + ∫ s in 0..t.val,
      residualKernel hα A b hT t s (unweighted j s) = l t-actualResidual hα A b t (initial hT) d)
    (t : Time T) (ht : t.val < T) (φ ψ : SchwartzMap V ℂ)
    (hψ : ∀ x, ψ x = ((A (now t) x).val : ℂ)*φ x) :
    HasDerivAt (fun r => pairCLM φ φ.integrable (mildTime hα A hT d j r))
      (pairCLM φ φ.integrable (l t)-adjointPair b t φ ψ (mildTime hα A hT d j t.val)) t.val := by
  let L := pairCLM φ φ.integrable
  let M := pairCLM (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ)
    (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ).integrable
  let N := adjointPair b t φ ψ
  have h₁ := hasDerivAt_pair_c0Time hα (A (initial hT)) t.val t.property.1 d φ
  have h₂ := hasDerivAt_pair_duhamel hα A hT j φ t.val ⟨t.property.1,ht⟩
  have he₁ := pair_fullResidual hα (A (initial hT)) (A (now t)) (b (now t)) t.val t.property.1 d φ ψ hψ
  have he₂ := pair_integral_residualKernel hα A b hT j t (hi t) φ ψ hψ
  have he := congrArg L (hj t)
  simp only [map_add,map_sub] at he
  change L (unweighted j t.val) + L (∫ s in 0..t.val,
    residualKernel hα A b hT t s (unweighted j s)) = L (l t)-L (actualResidual hα A b t (initial hT) d) at he
  rw [he₂] at he
  have he₁' : L (actualResidual hα A b t (initial hT) d) =
      -M (c0Time hα (A (initial hT)) t.val
        (C0Multiplier.mul (coefficient (A (initial hT)).toContinuousMap) d)) +
      N (c0Time hα (A (initial hT)) t.val d) := by
    simpa only [L,M,N,actualResidual,initial,sub_zero,adjointPair,add_apply,add_assoc] using he₁
  rw [he₁'] at he
  have hd := h₁.add h₂
  have heq : (-M (c0Time hα (A (initial hT)) t.val
      (C0Multiplier.mul (coefficient (A (initial hT)).toContinuousMap) d))) +
      (L (unweighted j t.val)-M (duhamel hα A (sourceMultiply A j) t.val)) =
      L (l t)-N (mildTime hα A hT d j t.val) := by
    rw [mildTime,map_add]
    linear_combination he
  rw [heq] at hd
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall (fun r => L.map_add _ _)

end ParametrixVolterra

namespace StrongWeightedVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {T : ℝ}

def dampWeight (u : UnitTime) : ℝ := u.val^(-3/4 : ℝ)*(1-u.val)^(-7/8 : ℝ)

lemma dampWeight_nonneg (u : UnitTime) : 0 ≤ dampWeight u :=
  mul_nonneg (Real.rpow_nonneg u.property.1.le _)
    (Real.rpow_nonneg (sub_pos.mpr u.property.2).le _)

lemma integrable_dampWeight : Integrable dampWeight := by
  have hb := (Complex.betaIntegral_convergent
    (u := (1/4 : ℂ)) (v := (1/8 : ℂ)) (by norm_num) (by norm_num)).norm.1
  have hi := hb.mono_set Ioo_subset_Ioc_self
  have he : EqOn (fun x : ℝ => ‖(x : ℂ)^((1/4 : ℂ)-1) *
      (1-(x : ℂ))^((1/8 : ℂ)-1)‖)
      (fun x : ℝ => x^(-3/4 : ℝ)*(1-x)^(-7/8 : ℝ)) (Ioo 0 1) := by
    intro x hx
    dsimp only
    rw [norm_mul]
    have hq : (1/4 : ℂ)-1 = ((-3/4 : ℝ) : ℂ) := by norm_num
    have hr : (1/8 : ℂ)-1 = ((-7/8 : ℝ) : ℂ) := by norm_num
    rw [hq,hr, show (1 : ℂ)-(x : ℂ) = ((1-x : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_real, Complex.norm_cpow_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hx.1, abs_of_pos (sub_pos.mpr hx.2)]
  have hw := hi.congr_fun he measurableSet_Ioo
  exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp hw

lemma eighth_exp_neg_le_one (x : ℝ) (hx : 0 ≤ x) :
    x^(1/8 : ℝ)*Real.exp (-x) ≤ 1 := by
  by_cases h : x ≤ 1
  · calc
      _ ≤ 1*1 := mul_le_mul (Real.rpow_le_one hx h (by norm_num))
        (Real.exp_le_one_iff.mpr (by linarith)) (Real.exp_pos _).le (by norm_num)
      _ = _ := one_mul _
  · calc
      _ ≤ x*Real.exp (-x) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (le_of_not_ge h) (by norm_num)) (Real.exp_pos _).le
      _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one x
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)

lemma eighth_exp_scale_le (κ t v : ℝ) (hκ : 0 < κ) (ht : 0 < t) (hv : 0 < v) :
    t^(1/8 : ℝ)*Real.exp (-κ*t*v) ≤ κ^(-1/8 : ℝ)*v^(-1/8 : ℝ) := by
  have hb := eighth_exp_neg_le_one (κ*t*v) (by positivity)
  have hcκ : κ^(-1/8 : ℝ)*κ^(1/8 : ℝ)=1 := by rw [← Real.rpow_add hκ]; norm_num
  have hcv : v^(-1/8 : ℝ)*v^(1/8 : ℝ)=1 := by rw [← Real.rpow_add hv]; norm_num
  calc
    _ = (κ^(-1/8 : ℝ)*v^(-1/8 : ℝ))*((κ*t*v)^(1/8 : ℝ)*Real.exp (-(κ*t*v))) := by
      rw [Real.mul_rpow (mul_pos hκ ht).le hv.le,Real.mul_rpow hκ.le ht.le]
      calc
        _ = (κ^(-1/8 : ℝ)*κ^(1/8 : ℝ))*(v^(-1/8 : ℝ)*v^(1/8 : ℝ))*
            (t^(1/8 : ℝ)*Real.exp (-κ*t*v)) := by rw [hcκ,hcv]; ring
        _ = _ := by
          rw [show -(κ*t*v) = -κ*t*v by ring]
          ring
    _ ≤ (κ^(-1/8 : ℝ)*v^(-1/8 : ℝ))*1 :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := mul_one _

lemma damp_scalar_bound (κ : ℝ) (hκ : 0 < κ) (t : Time T) (ht : t.val ≤ 1) (u : UnitTime) :
    t.val^(1/4 : ℝ)*weight u*Real.exp (-κ*(t.val*(1-u.val))) ≤
      κ^(-1/8 : ℝ)*dampWeight u := by
  have hu : 0 < 1-u.val := sub_pos.mpr u.property.2
  have ht8 : t.val^(1/8 : ℝ) ≤ 1 := Real.rpow_le_one t.property.1.le ht (by norm_num)
  have he := eighth_exp_scale_le κ t.val (1-u.val) hκ t.property.1 hu
  have hpow : t.val^(1/4 : ℝ) = t.val^(1/8 : ℝ)*t.val^(1/8 : ℝ) := by
    rw [← Real.rpow_add t.property.1]; norm_num
  have hmul : weight u*(1-u.val)^(-1/8 : ℝ)=dampWeight u := by
    rw [weight,dampWeight,mul_assoc,← Real.rpow_add hu]; norm_num
  calc
    _ = (t.val^(1/8 : ℝ)*weight u)*(t.val^(1/8 : ℝ)*Real.exp (-κ*t.val*(1-u.val))) := by
      rw [hpow,show -κ*(t.val*(1-u.val)) = -κ*t.val*(1-u.val) by ring]
      ring
    _ ≤ (1*weight u)*(κ^(-1/8 : ℝ)*(1-u.val)^(-1/8 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right ht8 (weight_nonneg u)) he (mul_nonneg (Real.rpow_nonneg t.property.1.le _) (Real.exp_pos _).le)
        (mul_nonneg (by norm_num) (weight_nonneg u))
    _ = _ := by rw [one_mul,← hmul]; ring

def dampKernel (N : Kernel T E) (κ : ℝ) : Kernel T E where
  toFun p := Real.exp (-κ*(p.1.val*(1-p.2.val))) • N p
  continuous_apply := by
    change Continuous (fun p : (Time T × UnitTime) × E =>
      Real.exp (-κ*(p.1.1.val*(1-p.1.2.val))) • N p.1 p.2)
    exact (by fun_prop : Continuous (fun p : (Time T × UnitTime) × E =>
      Real.exp (-κ*(p.1.1.val*(1-p.1.2.val))))).smul N.continuous_apply

lemma norm_dampKernel_le (N : Kernel T E) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p, ‖N p‖ ≤ C) (κ : ℝ) (hκ : 0 ≤ κ) (p : Time T × UnitTime) :
    ‖dampKernel N κ p‖ ≤ C := by
  change ‖Real.exp (-κ*(p.1.val*(1-p.2.val))) • N p‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-κ*(p.1.val*(1-p.2.val))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      rw [neg_mul]
      exact neg_nonpos.mpr (mul_nonneg hκ (mul_nonneg p.1.property.1.le (sub_pos.mpr p.2.property.2).le)))
  exact (mul_le_mul_of_nonneg_left (hN p) (Real.exp_pos _).le).trans
    (mul_le_of_le_one_left hC he)

lemma norm_damp_data_le (N : Kernel T E) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p, ‖N p‖ ≤ C) (κ : ℝ) (hκ : 0 < κ) (ht : T ≤ 1)
    (j : Time T →ᵇ E) (t : Time T) (u : UnitTime) :
    ‖t.val^(1/4 : ℝ) • data (dampKernel N κ) j t u‖ ≤
      κ^(-1/8 : ℝ)*dampWeight u*(C*‖j‖) := by
  change ‖t.val^(1/4 : ℝ) • (weight u •
    ((Real.exp (-κ*(t.val*(1-u.val))) • N (t,u)) (j (lag t u))))‖ ≤ _
  rw [smul_apply,smul_smul,smul_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg t.property.1.le _)
    (weight_nonneg u)) (Real.exp_pos _).le)]
  calc
    _ ≤ (t.val^(1/4 : ℝ)*weight u*Real.exp (-κ*(t.val*(1-u.val))))*(C*‖j‖) :=
      mul_le_mul_of_nonneg_left ((N (t,u)).le_opNorm _ |>.trans
        (mul_le_mul (hN _) (j.norm_coe_le_norm _) (norm_nonneg _) hC))
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg t.property.1.le _) (weight_nonneg u)) (Real.exp_pos _).le)
    _ ≤ _ := mul_le_mul_of_nonneg_right (damp_scalar_bound κ hκ t (t.property.2.trans ht) u)
      (mul_nonneg hC (norm_nonneg _))

lemma norm_damp_value_le (N : Kernel T E) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p, ‖N p‖ ≤ C) (κ : ℝ) (hκ : 0 < κ) (ht : T ≤ 1)
    (j : Time T →ᵇ E) (t : Time T) :
    ‖value (dampKernel N κ) j t‖ ≤ (κ^(-1/8 : ℝ)*(∫ u : UnitTime, dampWeight u)*C)*‖j‖ := by
  rw [value,← integral_smul]
  calc
    _ ≤ ∫ u : UnitTime, κ^(-1/8 : ℝ)*dampWeight u*(C*‖j‖) :=
      norm_integral_le_of_norm_le ((integrable_dampWeight.const_mul _).mul_const _)
        (Eventually.of_forall (norm_damp_data_le N C hC hN κ hκ ht j t))
    _ = _ := by rw [integral_mul_const,integral_const_mul]; ring


lemma norm_timeExp_le (c : ℝ) (j : Time T →ᵇ E) (t : Time T) :
    ‖Real.exp (c*t.val) • j t‖ ≤ Real.exp (|c| * T)*‖j‖ := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right (le_abs_self c) t.property.1.le).trans
    (mul_le_mul_of_nonneg_left t.property.2 (abs_nonneg c)))) (j.norm_coe_le_norm t)
    (norm_nonneg _) (Real.exp_pos _).le

def timeExp (c : ℝ) (j : Time T →ᵇ E) : Time T →ᵇ E :=
  .ofNormedAddCommGroup (fun t => Real.exp (c*t.val) • j t)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul j.continuous)
    _ (norm_timeExp_le c j)

lemma timeExp_apply (c : ℝ) (j : Time T →ᵇ E) (t : Time T) :
    timeExp c j t = Real.exp (c*t.val) • j t := rfl

lemma timeExp_norm_le (c : ℝ) (j : Time T →ᵇ E) :
    ‖timeExp c j‖ ≤ Real.exp (|c| * T)*‖j‖ :=
  (BoundedContinuousFunction.norm_le (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
    (norm_timeExp_le c j)

lemma timeExp_add (c : ℝ) (j k : Time T →ᵇ E) :
    timeExp c (j+k) = timeExp c j+timeExp c k := by
  ext t
  simp only [timeExp_apply,BoundedContinuousFunction.add_apply,smul_add]

lemma timeExp_comp (c d : ℝ) (j : Time T →ᵇ E) :
    timeExp c (timeExp d j) = timeExp (c+d) j := by
  ext t
  simp only [timeExp_apply,smul_smul,← Real.exp_add,add_mul]

lemma timeExp_zero (j : Time T →ᵇ E) : timeExp 0 j = j := by
  ext t
  simp only [timeExp_apply,zero_mul,Real.exp_zero,one_smul]

lemma damp_data_conjugation (N : Kernel T E) (κ : ℝ) (j : Time T →ᵇ E) (t : Time T) (u : UnitTime) :
    data (dampKernel N κ) j t u = Real.exp (-κ*t.val) • data N (timeExp κ j) t u := by
  change weight u • ((Real.exp (-κ*(t.val*(1-u.val))) • N (t,u)) (j (lag t u))) = _
  rw [smul_apply,data,timeExp_apply,ContinuousLinearMap.map_smul_of_tower,smul_smul,smul_smul,smul_smul]
  congr 1
  change weight u*Real.exp (-κ*(t.val*(1-u.val))) =
    Real.exp (-κ*t.val)*weight u*Real.exp (κ*(t.val*u.val))
  calc
    _ = weight u*Real.exp (-κ*t.val+κ*(t.val*u.val)) := by congr 2; ring
    _ = _ := by rw [Real.exp_add]; ring

lemma damp_value_conjugation (N : Kernel T E) (κ : ℝ) (j : Time T →ᵇ E) (t : Time T) :
    value (dampKernel N κ) j t = Real.exp (-κ*t.val) • value N (timeExp κ j) t := by
  unfold value
  simp_rw [damp_data_conjugation]
  rw [integral_smul,smul_comm]

lemma damp_operator_conjugation (N : Kernel T E) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p, ‖N p‖ ≤ C) (κ : ℝ) (hκ : 0 ≤ κ) (hT : 0 ≤ T) (j : Time T →ᵇ E) :
    operator (dampKernel N κ) C hC (norm_dampKernel_le N C hC hN κ hκ) hT j =
      timeExp (-κ) (operator N C hC hN hT (timeExp κ j)) := by
  ext t
  exact damp_value_conjugation N κ j t

lemma norm_damp_operator_le (N : Kernel T E) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p, ‖N p‖ ≤ C) (κ : ℝ) (hκ : 0 < κ) (hT : 0 ≤ T) (ht : T ≤ 1)
    (j : Time T →ᵇ E) :
    ‖operator (dampKernel N κ) C hC (norm_dampKernel_le N C hC hN κ hκ.le) hT j‖ ≤
      (κ^(-1/8 : ℝ)*(∫ u : UnitTime, dampWeight u)*C)*‖j‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hκ.le _) (integral_nonneg dampWeight_nonneg)) hC)
    (norm_nonneg _))).mpr
  exact norm_damp_value_le N C hC hN κ hκ ht j

lemma norm_damp_operatorCLM_le (N : Kernel T E) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p, ‖N p‖ ≤ C) (κ : ℝ) (hκ : 0 < κ) (hT : 0 ≤ T) (ht : T ≤ 1) :
    ‖operatorCLM (dampKernel N κ) C hC (norm_dampKernel_le N C hC hN κ hκ.le) hT‖ ≤
      κ^(-1/8 : ℝ)*(∫ u : UnitTime, dampWeight u)*C := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hκ.le _) (integral_nonneg dampWeight_nonneg)) hC)
  exact norm_damp_operator_le N C hC hN κ hκ hT ht

lemma exists_damping_small (C : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ κ^(-1/8 : ℝ)*(∫ u : UnitTime, dampWeight u)*C < 1 := by
  have ht : Tendsto (fun κ : ℝ => κ^(-1/8 : ℝ)*(∫ u : UnitTime, dampWeight u)*C) atTop (𝓝 0) := by
    simpa only [zero_mul,neg_div] using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/8)).mul_const
      (∫ u : UnitTime, dampWeight u)).mul_const C
  exact ((eventually_gt_atTop (0:ℝ)).and (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)))).exists

theorem exists_unique_solution_full [CompleteSpace E] (N : Kernel T E) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p, ‖N p‖ ≤ C) (hT : 0 ≤ T) (ht : T ≤ 1) (g : Time T →ᵇ E) :
    ∃! j : Time T →ᵇ E, j+operator N C hC hN hT j=g := by
  obtain ⟨κ,hκ,hsmall⟩ := exists_damping_small C
  let M := dampKernel N κ
  have hM := norm_dampKernel_le N C hC hN κ hκ.le
  let A := operatorCLM M C hC hM hT
  have hA : ‖A‖ < 1 := (norm_damp_operatorCLM_le N C hC hN κ hκ hT ht).trans_lt hsmall
  let g₀ := timeExp (-κ) g
  let f : (Time T →ᵇ E) → (Time T →ᵇ E) := fun j => g₀-A j
  have hf : ContractingWith ‖A‖₊ f := by
    refine ⟨hA,LipschitzWith.of_dist_le_mul (fun j k => ?_)⟩
    rw [dist_eq_norm,dist_eq_norm]
    change ‖(g₀-A j)-(g₀-A k)‖ ≤ ‖A‖*‖j-k‖
    rw [sub_sub_sub_cancel_left,← A.map_sub,norm_sub_rev j k]
    exact A.le_opNorm (k-j)
  have hsolve : hf.fixedPoint+operator M C hC hM hT hf.fixedPoint = g₀ :=
    eq_sub_iff_add_eq.mp hf.fixedPoint_isFixedPt.symm
  let j := timeExp κ hf.fixedPoint
  have hj : j+operator N C hC hN hT j=g := by
    have he := congrArg (timeExp κ) hsolve
    rw [damp_operator_conjugation N C hC hN κ hκ.le hT,timeExp_add,timeExp_comp,
      add_neg_cancel,timeExp_zero] at he
    simpa only [g₀,timeExp_comp,add_neg_cancel,timeExp_zero] using he
  refine ⟨j,hj,fun k hk => ?_⟩
  have hk₀ : timeExp (-κ) k+operator M C hC hM hT (timeExp (-κ) k)=g₀ := by
    rw [damp_operator_conjugation N C hC hN κ hκ.le hT,timeExp_comp,add_neg_cancel,timeExp_zero]
    rw [← timeExp_add,hk]
  have hfix : f (timeExp (-κ) k)=timeExp (-κ) k := (eq_sub_iff_add_eq.mpr hk₀).symm
  have he := congrArg (timeExp κ) (hf.fixedPoint_unique hfix)
  simpa only [timeExp_comp,add_neg_cancel,timeExp_zero] using he


lemma norm_solution_full_le (N : Kernel T E) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p, ‖N p‖ ≤ C) (κ : ℝ) (hκ : 0 < κ) (hT : 0 ≤ T) (ht : T ≤ 1)
    (hsmall : κ^(-1/8 : ℝ)*(∫ u : UnitTime, dampWeight u)*C < 1)
    (g j : Time T →ᵇ E) (hj : j+operator N C hC hN hT j=g) :
    ‖j‖ ≤ (Real.exp (κ*T))^2/(1-κ^(-1/8 : ℝ)*(∫ u : UnitTime, dampWeight u)*C)*‖g‖ := by
  let Q := κ^(-1/8 : ℝ)*(∫ u : UnitTime, dampWeight u)*C
  let M := dampKernel N κ
  have hM := norm_dampKernel_le N C hC hN κ hκ.le
  let j₀ := timeExp (-κ) j
  let g₀ := timeExp (-κ) g
  have he : j₀+operator M C hC hM hT j₀=g₀ := by
    rw [damp_operator_conjugation N C hC hN κ hκ.le hT]
    dsimp only [j₀,g₀]
    rw [timeExp_comp,add_neg_cancel,timeExp_zero,← timeExp_add,hj]
  have hb : ‖operator M C hC hM hT j₀‖ ≤ Q*‖j₀‖ :=
    norm_damp_operator_le N C hC hN κ hκ hT ht j₀
  have hn := norm_sub_le g₀ (operator M C hC hM hT j₀)
  rw [← eq_sub_iff_add_eq.mpr he] at hn
  have hpos : 0 < 1-Q := sub_pos.mpr hsmall
  have hj₀ : ‖j₀‖ ≤ ‖g₀‖/(1-Q) := (le_div_iff₀ hpos).mpr (by nlinarith)
  have hj' : timeExp κ j₀=j := by
    change timeExp κ (timeExp (-κ) j)=j
    rw [timeExp_comp,add_neg_cancel,timeExp_zero]
  have hjb := timeExp_norm_le κ j₀
  rw [hj',abs_of_pos hκ] at hjb
  have hgb : ‖g₀‖ ≤ Real.exp (κ*T)*‖g‖ := by
    simpa only [g₀,abs_neg,abs_of_pos hκ] using timeExp_norm_le (-κ) g
  calc
    ‖j‖ ≤ Real.exp (κ*T)*(‖g₀‖/(1-Q)) := hjb.trans
      (mul_le_mul_of_nonneg_left hj₀ (Real.exp_pos _).le)
    _ ≤ Real.exp (κ*T)*((Real.exp (κ*T)*‖g‖)/(1-Q)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hgb hpos.le) (Real.exp_pos _).le
    _ = _ := by dsimp only [Q]; ring

theorem exists_full_inverse_bound [CompleteSpace E] (N : Kernel T E) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p, ‖N p‖ ≤ C) (hT : 0 ≤ T) (ht : T ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ g : Time T →ᵇ E,
      ∃ j : Time T →ᵇ E, j+operator N C hC hN hT j=g ∧ ‖j‖ ≤ D*‖g‖ := by
  obtain ⟨κ,hκ,hsmall⟩ := exists_damping_small C
  refine ⟨(Real.exp (κ*T))^2/(1-κ^(-1/8 : ℝ)*(∫ u : UnitTime, dampWeight u)*C),
    div_pos (sq_pos_of_pos (Real.exp_pos _)) (sub_pos.mpr hsmall),fun g => ?_⟩
  obtain ⟨j,hj,_⟩ := exists_unique_solution_full N C hC hN hT ht g
  exact ⟨j,hj,norm_solution_full_le N C hC hN κ hκ hT ht hsmall g j hj⟩

theorem exists_unweighted_solution_full [CompleteSpace E] (N : Kernel T E) (C : ℝ) (hC : 0 ≤ C)
    (hN : ∀ p, ‖N p‖ ≤ C) (hT : 0 ≤ T) (ht : T ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ g : Time T →ᵇ E,
      ∃ j : Time T →ᵇ E,
        (∀ t : Time T, IntervalIntegrable (fun r => kernel N t r (unweighted j r)) volume 0 t.val) ∧
        (∀ t : Time T, unweighted j t.val + ∫ r in 0..t.val, kernel N t r (unweighted j r) = unweighted g t.val) ∧
        ‖j‖ ≤ D*‖g‖ ∧
        (∀ t : Time T, ‖unweighted j t.val‖ ≤ t.val^(-3/4 : ℝ)*(D*‖g‖)) := by
  obtain ⟨D,hD,hd⟩ := exists_full_inverse_bound N C hC hN hT ht
  refine ⟨D,hD,fun g => ?_⟩
  obtain ⟨j,hj,hjb⟩ := hd g
  refine ⟨j,intervalIntegrable_kernel_unweighted N C hC hN j,
    unweighted_solves N C hC hN hT g j hj,hjb,fun t => ?_⟩
  rw [unweighted_at_time,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg t.property.1.le _)]
  exact mul_le_mul_of_nonneg_left ((j.norm_coe_le_norm t).trans hjb)
    (Real.rpow_nonneg t.property.1.le _)

end StrongWeightedVolterra

namespace ParametrixVolterra
open scoped ZeroAtInfty BoundedContinuousFunction SchwartzMap Laplacian
open FrozenParametrix C0Convolution StrongWeightedVolterra KernelPairing
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ}

theorem exists_parametrix_correction_full (hα : 0 < α)
    (A : C(Slab T, V →ᵇ Icc α β)) (b : C(Slab T, V →ᵇ ℂ))
    (hT₀ : 0 ≤ T) (hT : T ≤ 1) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|)) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 < D ∧
      ∀ (d : C₀(V,ℂ)) (l : Time T →ᵇ C₀(V,ℂ)), ∃ j : Time T →ᵇ C₀(V,ℂ),
        (∀ t : Time T, IntervalIntegrable
          (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val) ∧
        (∀ t : Time T, unweighted j t.val + ∫ r in 0..t.val,
          residualKernel hα A b hT₀ t r (unweighted j r) =
            l t-actualResidual hα A b t (initial hT₀) d) ∧
        ‖j‖ ≤ D*(‖l‖+C*‖d‖) := by
  obtain ⟨C,hC,hR⟩ := exists_actualResidual_bound hα A b hT L B hL hB hb hLip
  obtain ⟨D,hD,hN⟩ := exists_normalized_bound hα A b hT L B hL hB hb hLip
  have hR₀ : ∀ t : Time T, ‖actualResidual hα A b t (initial hT₀)‖ ≤ C*t.val^(-3/4 : ℝ) := by
    intro t
    simpa only [initial,sub_zero] using hR t (initial hT₀) t.property.1
  let N : Kernel T C₀(V,ℂ) := Kernel.ofStrong (normalized hα A b)
    (continuous_normalized_apply hα A b) D hD hN
  obtain ⟨E,hE,he⟩ := exists_unweighted_solution_full N D hD hN hT₀ hT
  refine ⟨C,E,hC,hE,fun d l => ?_⟩
  let g := weightedSource hα A b hT₀ hT C hC hR₀ d l
  obtain ⟨j,hi,hj,hbound,_⟩ := he g
  have hk : ∀ t r, kernel N t r = residualKernel hα A b hT₀ t r :=
    kernel_eq_residualKernel hα A b hT₀ D hD hN
  simp_rw [hk] at hi hj
  have hg : ∀ t : Time T, unweighted g t.val = l t-actualResidual hα A b t (initial hT₀) d :=
    unweighted_weightedSource hα A b hT₀ hT C hC hR₀ d l
  simp_rw [hg] at hj
  refine ⟨j,hi,hj,hbound.trans ?_⟩
  have hgnorm : ‖g‖ ≤ ‖l‖+C*‖d‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    exact norm_sourceRHS_le hα A b hT₀ hT C hC hR₀ d l
  exact mul_le_mul_of_nonneg_left hgnorm hE.le

def coefficientTest (a : V →ᵇ Icc α β) (ha : ContDiff ℝ ∞ (fun x => (a x).val))
    (φ : SchwartzMap V ℂ) (hφ : HasCompactSupport (φ : V → ℂ)) : SchwartzMap V ℂ :=
  HasCompactSupport.toSchwartzMap (f := fun x => ((a x).val : ℂ)*φ x) hφ.mul_left
    ((Complex.ofRealCLM.contDiff.comp ha).mul (φ.smooth ⊤))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma coefficientTest_apply (a : V →ᵇ Icc α β) (ha : ContDiff ℝ ∞ (fun x => (a x).val))
    (φ : SchwartzMap V ℂ) (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    coefficientTest a ha φ hφ x = ((a x).val : ℂ)*φ x := rfl

theorem exists_weak_evolution (hα : 0 < α)
    (A : C(Slab T,V →ᵇ Icc α β)) (b : C(Slab T,V →ᵇ ℂ))
    (hT₀ : 0 ≤ T) (hT : T ≤ 1) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hA : ∀ s, ContDiff ℝ ∞ (fun x => (A s x).val)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d : C₀(V,ℂ)) (l : Time T →ᵇ C₀(V,ℂ)),
      ∃ u : ℝ → C₀(V,ℂ), u 0=d ∧ ContinuousOn u (Icc 0 T) ∧
        (∀ t ∈ Icc 0 T, ‖u t‖ ≤ K*(‖l‖+‖d‖)) ∧
        (∀ (t : Time T), t.val < T → ∀ (φ : SchwartzMap V ℂ)
          (hφ : HasCompactSupport (φ : V → ℂ)),
          HasDerivAt (fun r => pairCLM φ φ.integrable (u r))
            (pairCLM φ φ.integrable (l t)-
              adjointPair b t φ (coefficientTest (A (now t)) (hA (now t)) φ hφ) (u t.val)) t.val) := by
  obtain ⟨C,D,hC,hD,hs⟩ := exists_parametrix_correction_full hα A b hT₀ hT L B hL hB hb hLip
  let M := frozenBound (V := V) (β := β) hα
  let Q := ∫ v : UnitTime, MildVolterra.massWeight v
  have hM : 0 ≤ M := frozenBound_nonneg hα
  have hQ : 0 ≤ Q := integral_nonneg MildVolterra.massWeight_nonneg
  refine ⟨M+Q*M*D*(1+C),by positivity,fun d l => ?_⟩
  obtain ⟨j,hi,hj,hjb⟩ := hs d l
  refine ⟨mildTime hα A hT₀ d j,mildTime_zero hα A hT₀ d j,
    continuousOn_mildTime hα A hT₀ d j,fun t ht => ?_,fun t ht φ hφ => ?_⟩
  · have ht1 : t^(1/4 : ℝ) ≤ 1 := Real.rpow_le_one ht.1 (ht.2.trans hT) (by positivity)
    have h0 := norm_c0Time_le hα (A (initial hT₀)) t d
    have h1 := norm_duhamel_le hα A hT₀ j t ht
    have hjb' : ‖j‖ ≤ D*((1+C)*(‖l‖+‖d‖)) := hjb.trans
      (mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg l,norm_nonneg d]) hD.le)
    calc
      ‖mildTime hα A hT₀ d j t‖ ≤ M*‖d‖+t^(1/4 : ℝ)*(Q*M*‖j‖) :=
        (norm_add_le _ _).trans (add_le_add h0 h1)
      _ ≤ M*‖d‖+Q*M*‖j‖ := add_le_add le_rfl
        (mul_le_of_le_one_left (mul_nonneg (mul_nonneg hQ hM) (norm_nonneg j)) ht1)
      _ ≤ M*(‖l‖+‖d‖)+Q*M*(D*((1+C)*(‖l‖+‖d‖))) := add_le_add
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg l)) hM)
        (mul_le_mul_of_nonneg_left hjb' (mul_nonneg hQ hM))
      _ = _ := by ring
  · exact hasDerivAt_pair_mildTime hα A b hT₀ d j l hi hj t ht φ
      (coefficientTest (A (now t)) (hA (now t)) φ hφ) (coefficientTest_apply _ _ _ _)

end ParametrixVolterra

open Set Filter MeasureTheory
open scoped SchwartzMap Topology
namespace SchwartzTimeScale
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def euler (K : SchwartzMap V E) (N : ℕ) : SchwartzMap V E :=
  (-(N : ℝ)/4) • K - (1/4 : ℝ) •
    (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ E).flip
      (by fun_prop : Function.HasTemperateGrowth (fun y : V => y))
      (SchwartzMap.fderivCLM ℝ V E K))

lemma euler_apply (K : SchwartzMap V E) (N : ℕ) (y : V) :
    euler K N y = (-(N : ℝ)/4) • K y-(1/4 : ℝ) • (fderiv ℝ K y y) := rfl

def atTime (K : SchwartzMap V E) (N : ℕ) (q : ℝ) (y : V) : E :=
  q^(-(N : ℝ)/4) • K (q^(-(1 : ℝ)/4) • y)

lemma hasDerivAt_atTime (K : SchwartzMap V E) (N : ℕ) (q : ℝ) (hq : 0 < q) (y : V) :
    HasDerivAt (fun s => atTime K N s y)
      (atTime (euler K N) (N+4) q y) q := by
  have h1 := Real.hasDerivAt_rpow_const (p := -(N : ℝ)/4) (Or.inl hq.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := -(1 : ℝ)/4) (Or.inl hq.ne')
  have hK := (K.hasFDerivAt (q^(-(1 : ℝ)/4) • y)).comp_hasDerivAt q (h2.smul_const y)
  have hd := h1.smul hK
  convert hd using 1
  · rfl
  · dsimp only [atTime,Function.comp_apply,Pi.smul_apply]
    rw [euler_apply,smul_sub]
    simp only [ContinuousLinearMap.map_smul,smul_smul]
    have he1 : q^(-((N+4 : ℕ) : ℝ)/4) = q^(-(N : ℝ)/4-1) := by
      congr 1
      push_cast
      ring
    have he2 : q^(-(N : ℝ)/4) * (-(1 : ℝ)/4*q^(-(1 : ℝ)/4-1)) =
        -(q^(-(N : ℝ)/4-1)*(1/4))*q^(-(1 : ℝ)/4) := by
      calc
        _ = (-(1 : ℝ)/4)*q^(-(N : ℝ)/4+(-(1 : ℝ)/4-1)) := by rw [Real.rpow_add hq]; ring
        _ = (-(1 : ℝ)/4)*q^((-(N : ℝ)/4-1)+(-(1 : ℝ)/4)) := by congr 2; ring
        _ = _ := by rw [Real.rpow_add hq]; ring
    rw [he1,he2]
    module

lemma atTime_eq_scaled (K : SchwartzMap V E) (N : ℕ) (q : ℝ) (hq : 0 < q) (y : V) :
    atTime K N q y = ((q^(1/4 : ℝ))⁻¹)^N • K ((q^(1/4 : ℝ))⁻¹ • y) := by
  unfold atTime
  rw [show -(1 : ℝ)/4 = -(1/4 : ℝ) by ring,Real.rpow_neg hq.le]
  congr 1
  rw [← Real.rpow_natCast,← Real.rpow_neg hq.le,← Real.rpow_mul hq.le]
  congr 1
  ring
end SchwartzTimeScale

namespace SourceFrozenCancellation
open SchwartzTimeScale
open scoped BoundedContinuousFunction
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma parameter_envelope (K : SchwartzMap V E) (N : ℕ) (α β : ℝ) (hα : 0 < α) :
    ∃ B : V → ℝ, Integrable B ∧ Integrable (fun z => (1+‖z‖)*B z) ∧
      (∀ z, 0 ≤ B z) ∧ ∀ a ∈ Icc α β, ∀ z, ‖atTime K N a z‖ ≤ B z := by
  obtain ⟨B,hB,hw,hp,hb⟩ := SchwartzConvolution.scaled_weighted_majorant K
    (α^(1/4 : ℝ)) (β^(1/4 : ℝ)) (by positivity) N 1
  refine ⟨B,hB,by simpa only [pow_one] using hw,hp,?_⟩
  intro a ha z
  rw [atTime_eq_scaled K N a (hα.trans_le ha.1)]
  exact hb _ ⟨Real.rpow_le_rpow hα.le ha.1 (by norm_num),
    Real.rpow_le_rpow (hα.trans_le ha.1).le ha.2 (by norm_num)⟩ z

omit [CompleteSpace E] in
lemma parameter_lipschitz_envelope (K : SchwartzMap V E) (N : ℕ) (α β : ℝ) (hα : 0 < α) :
    ∃ C : V → ℝ, Integrable C ∧ Integrable (fun z => (1+‖z‖)*C z) ∧
      (∀ z, 0 ≤ C z) ∧ ∀ a ∈ Icc α β, ∀ b ∈ Icc α β, ∀ z,
        ‖atTime K N a z-atTime K N b z‖ ≤ C z*‖a-b‖ := by
  obtain ⟨C,hC,hw,hp,hb⟩ := parameter_envelope (euler K N) (N+4) α β hα
  refine ⟨C,hC,hw,hp,fun a ha b hb' z => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q hq => (hasDerivAt_atTime K N q (hα.trans_le hq.1) z).hasDerivWithinAt)
    (fun q hq => hb q hq z) (convex_Icc α β) hb' ha

omit [CompleteSpace E] in
lemma integral_atTime_zero (K : SchwartzMap V E) (N : ℕ) (a : ℝ) (ha : 0 < a)
    (hK : ∫ z, K z = 0) : ∫ z, atTime K N a z = 0 := by
  simp_rw [atTime_eq_scaled K N a ha]
  rw [integral_smul,Measure.integral_comp_inv_smul_of_nonneg volume _ (by positivity)]
  simp only [hK,smul_zero]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace E] in
lemma continuous_variable (K : SchwartzMap V E) (N : ℕ) (a : V → ℝ) (ha : Continuous a)
    (hp : ∀ z, 0 < a z) : Continuous (fun z => atTime K N (a z) z) := by
  unfold atTime
  exact (ha.rpow_const (fun z => Or.inl (hp z).ne')).smul
    (K.continuous.comp ((ha.rpow_const (fun z => Or.inl (hp z).ne')).smul continuous_id))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] in
lemma integrable_envelope_power (B : V → ℝ) (hB : Integrable B)
    (hW : Integrable (fun z => (1+‖z‖)*B z)) (hp : ∀ z, 0 ≤ B z)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) : Integrable (fun z => ‖z‖^γ*B z) := by
  apply hW.mono'
  · exact (continuous_norm.rpow_const (fun _ => Or.inr hγ)).aestronglyMeasurable.mul
      hB.aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hp z))]
    apply mul_le_mul_of_nonneg_right _ (hp z)
    by_cases hz : ‖z‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg _) hz hγ).trans (by linarith [norm_nonneg z])
    · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hz) hγ1
      rw [Real.rpow_one] at hh
      exact hh.trans (by linarith)

omit [CompleteSpace E] in

lemma norm_normalized_source_integral (K : SchwartzMap V E) (N : ℕ)
    (α β : ℝ) (hα : 0 < α) (hK : ∫ z, K z = 0)
    (B C : V → ℝ) (hB : Integrable B) (hBw : Integrable (fun z => (1+‖z‖)*B z))
    (hBp : ∀ z, 0 ≤ B z) (hC : Integrable C) (hCw : Integrable (fun z => (1+‖z‖)*C z))
    (hCp : ∀ z, 0 ≤ C z)
    (hb : ∀ a ∈ Icc α β, ∀ z, ‖atTime K N a z‖ ≤ B z)
    (hc : ∀ a ∈ Icc α β, ∀ b ∈ Icc α β, ∀ z,
      ‖atTime K N a z-atTime K N b z‖ ≤ C z*‖a-b‖)
    (A : V → ℝ) (hA : Continuous A) (hAr : ∀ y, A y ∈ Icc α β)
    (L : ℝ) (_hL : 0 ≤ L) (hAL : ∀ x y, ‖A x-A y‖ ≤ L*‖x-y‖)
    (f : V →ᵇ ℂ) (γ H : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H)
    (hhold : ∀ x y, ‖f x-f y‖ ≤ H*‖x-y‖^γ) (r : ℝ) (hr : 0 < r) (x : V) :
    ‖∫ z, f (x-r • z) • atTime K N (A (x-r • z)) z‖ ≤
      H*r^γ*(∫ z, ‖z‖^γ*B z)+‖f‖*L*r*(∫ z, ‖z‖*C z) := by
  let a : V → ℝ := fun z => A (x-r • z)
  have ha : Continuous a := hA.comp (continuous_const.sub (continuous_const.smul continuous_id))
  have hp (z : V) : 0 < a z := hα.trans_le (hAr _).1
  have hi : Integrable (fun z => f (x-r • z) • atTime K N (a z) z) := by
    apply (hB.const_mul ‖f‖).mono'
    · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul
        (continuous_variable K N a ha hp)).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)
  have hi₀ : Integrable (fun z => f x • atTime K N (A x) z) := by
    apply (hB.const_mul ‖f x‖).mono'
    · exact ((continuous_variable K N (fun _ => A x) continuous_const
        (fun _ => hα.trans_le (hAr x).1)).const_smul (f x)).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hb _ (hAr x) z) (norm_nonneg _)
  have hzero : ∫ z, f x • atTime K N (A x) z = 0 := by
    rw [integral_smul,integral_atTime_zero K N (A x) (hα.trans_le (hAr x).1) hK,smul_zero]
  have hiB := integrable_envelope_power B hB hBw hBp γ hγ hγ1
  have hiC : Integrable (fun z => ‖z‖*C z) := by
    simpa using integrable_envelope_power C hC hCw hCp 1 (by norm_num) le_rfl
  have hd (z : V) : ‖(x-r • z)-x‖ = r*‖z‖ := by
    rw [sub_sub_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  calc
    _ = ‖∫ z, (f (x-r • z) • atTime K N (a z) z-f x • atTime K N (A x) z)‖ := by
      rw [integral_sub hi hi₀,hzero,sub_zero]
    _ ≤ ∫ z, ‖f (x-r • z) • atTime K N (a z) z-f x • atTime K N (A x) z‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, (H*r^γ)*(‖z‖^γ*B z)+(‖f‖*L*r)*(‖z‖*C z) := by
      apply integral_mono (hi.sub hi₀).norm ((hiB.const_mul _).add (hiC.const_mul _))
      intro z
      have hdec : f (x-r • z) • atTime K N (a z) z-f x • atTime K N (A x) z =
          (f (x-r • z)-f x) • atTime K N (a z) z+
          f x • (atTime K N (a z) z-atTime K N (A x) z) := by module
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [hdec]
      apply (norm_add_le _ _).trans
      rw [norm_smul,norm_smul]
      have hF : ‖f (x-r • z)-f x‖ ≤ H*r^γ*‖z‖^γ := by
        simpa only [hd,Real.mul_rpow hr.le (norm_nonneg _),mul_assoc] using hhold (x-r • z) x
      have hcoef : ‖atTime K N (a z) z-atTime K N (A x) z‖ ≤ C z*(L*r*‖z‖) := by
        exact (hc _ (hAr _) _ (hAr x) z).trans
          (mul_le_mul_of_nonneg_left (by simpa only [hd,mul_assoc] using hAL (x-r • z) x) (hCp z))
      calc
        _ ≤ (H*r^γ*‖z‖^γ)*B z+‖f‖*(C z*(L*r*‖z‖)) :=
          add_le_add (mul_le_mul hF (hb _ (hAr _) z) (norm_nonneg _) (by positivity))
            (mul_le_mul (f.norm_coe_le_norm x) hcoef (norm_nonneg _) (norm_nonneg _))
        _ = _ := by ring
    _ = _ := by rw [integral_add (hiB.const_mul _) (hiC.const_mul _),integral_const_mul,integral_const_mul]
end SourceFrozenCancellation
open Set Filter MeasureTheory
open scoped SchwartzMap ContDiff FourierTransform BoundedContinuousFunction Convolution Topology

namespace SchwartzDerivatives
section Iterated
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def iterated (g : SchwartzMap V E) : (n : ℕ) →
    SchwartzMap V (ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E)
  | 0 => g.postcompCLM (continuousMultilinearCurryFin0 ℝ V E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  | n+1 => (SchwartzMap.fderivCLM ℝ V _ (iterated g n)).postcompCLM
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => V) E).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma iterated_coe (g : SchwartzMap V E) (n : ℕ) :
    (iterated g n : V → ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E) =
      iteratedFDeriv ℝ n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    change ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => V) E).symm ∘
      fderiv ℝ (iterated g n)) = _
    rw [ih]

lemma iterated_apply (g : SchwartzMap V E) (n : ℕ) (x : V) :
    iterated g n x = iteratedFDeriv ℝ n g x := congrFun (iterated_coe g n) x

end Iterated

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma integral_fderiv (g : SchwartzMap V E) :
    ∫ x : V, fderiv ℝ g x = 0 := by
  have h := congrArg (fun f : SchwartzMap V (V →L[ℝ] E) => f 0)
    (SchwartzMap.fourier_fderivCLM_eq (𝕜 := ℝ) g)
  simpa [SchwartzMap.fourier_coe, Real.fourier_eq,
    SchwartzMap.smulRightCLM_apply_apply, SchwartzMap.fderivCLM_apply] using h

lemma integral_iterated (g : SchwartzMap V E) (n : ℕ) :
    ∫ x : V, iteratedFDeriv ℝ (n+1) g x = 0 := by
  let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => V) E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let : ContinuousENorm (V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E) :=
    @SeminormedAddGroup.toContinuousENorm (V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E) inferInstance
  have hi : Integrable (fun x : V => fderiv ℝ (iterated g n) x) :=
    (SchwartzMap.fderivCLM ℝ V _ (iterated g n)).integrable
  rw [iteratedFDeriv_succ_eq_comp_left, ← iterated_coe g n]
  change (∫ x, L (fderiv ℝ (iterated g n) x)) = 0
  have hh := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
    (E := V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E)
    (Fₗ := ContinuousMultilinearMap ℝ (fun _ : Fin (n+1) => V) E) L hi
  exact hh.trans (by rw [integral_fderiv, map_zero])

end SchwartzDerivatives

namespace ScaledSchwartzConvolution
variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {a b : ℝ} (ha : 0 < a) (c : V → ℝ) (hc : Continuous c) (hcb : ∀ y, c y ∈ Icc a b)

include ha hc hcb
lemma iteratedFDeriv_value_smul (f : V →ᵇ ℂ) (g : SchwartzMap V E) (K n : ℕ) :
    iteratedFDeriv ℝ n (value c (ContinuousLinearMap.lsmul ℝ ℂ) f g K) =
      value c (ContinuousLinearMap.lsmul ℝ ℂ) f (SchwartzDerivatives.iterated g n) (K+n) := by
  induction n with
  | zero =>
    funext x
    let L := (continuousMultilinearCurryFin0 ℝ V E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hi : Integrable (fun y => f y • ((c y)⁻¹^K • g ((c y)⁻¹ • (x-y)))) :=
      integrable_integrand ha c hc hcb (ContinuousLinearMap.lsmul ℝ ℂ) f g K x
    change L (∫ y, f y • (c y)⁻¹^K • g ((c y)⁻¹ • (x-y))) =
      ∫ y, f y • ((c y)⁻¹^K • L (g ((c y)⁻¹ • (x-y))))
    rw [← ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) L hi]
    apply integral_congr_ae
    filter_upwards with y
    ext m
    rfl
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, ih, fderiv_value ha c hc hcb]
    funext x
    let g' := SchwartzMap.fderivCLM ℝ V _ (SchwartzDerivatives.iterated g n)
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => V) E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hi := integrable_integrand ha c hc hcb
      (E := V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E)
      (F := V →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => V) E)
      ((ContinuousLinearMap.lsmul ℝ ℂ).precompR V) f g' (K+n+1) x
    change L (∫ y, ((ContinuousLinearMap.lsmul ℝ ℂ).precompR V) (f y)
        ((c y)⁻¹^(K+n+1) • g' ((c y)⁻¹ • (x-y)))) =
      ∫ y, f y • ((c y)⁻¹^(K+(n+1)) • L (g' ((c y)⁻¹ • (x-y))))
    simp only [← Nat.add_assoc]
    rw [← ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) L hi]
    apply integral_congr_ae
    filter_upwards with y
    ext m
    rfl

lemma iteratedFDeriv_value_smul_apply (f : V →ᵇ ℂ) (g : SchwartzMap V E) (K n : ℕ) (x : V) :
    iteratedFDeriv ℝ n (value c (ContinuousLinearMap.lsmul ℝ ℂ) f g K) x =
      ∫ y, f y • ((c y)⁻¹^(K+n) • iteratedFDeriv ℝ n g ((c y)⁻¹ • (x-y))) := by
  rw [iteratedFDeriv_value_smul ha c hc hcb]
  simp only [value,ContinuousLinearMap.lsmul_apply,SchwartzDerivatives.iterated_apply]
end ScaledSchwartzConvolution
open Set Filter MeasureTheory
open scoped Topology SchwartzMap
namespace SourceFrozenScaling
variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [Measure.IsAddHaarMeasure (volume : Measure V)]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma normalized_integral (f : V → ℂ) (g : V → E) (c : V → ℝ) (r : ℝ) (hr : 0 < r)
    (K : ℕ) (x : V) :
    (∫ y, f y • ((r*c y)⁻¹^K • g ((r*c y)⁻¹ • (x-y)))) =
      (r^Module.finrank ℝ V*(r⁻¹)^K) • ∫ z, f (x-r • z) •
        ((c (x-r • z))⁻¹^K • g ((c (x-r • z))⁻¹ • z)) := by
  rw [← integral_sub_left_eq_self (fun y : V =>
    f y • ((r*c y)⁻¹^K • g ((r*c y)⁻¹ • (x-y)))) volume x]
  simp only [sub_sub_self]
  let F : V → E := fun z => f (x-r • z) •
    ((c (x-r • z))⁻¹^K • g ((c (x-r • z))⁻¹ • z))
  have he (y : V) : f (x-y) • ((r*c (x-y))⁻¹^K • g ((r*c (x-y))⁻¹ • y)) =
      (r⁻¹)^K • F (r⁻¹ • y) := by
    dsimp [F]
    rw [smul_inv_smul₀ hr.ne',mul_inv,mul_pow]
    rw [mul_comm r⁻¹ ((c (x-y))⁻¹),mul_smul]
    rw [mul_smul,smul_comm (f (x-y)) ((r⁻¹)^K)]
  simp_rw [he]
  rw [integral_smul,Measure.integral_comp_inv_smul_of_nonneg volume F hr.le,smul_smul]
  congr 1
  ring

lemma dimension_cancel (r : ℝ) (hr : r ≠ 0) (d n : ℕ) :
    r^d*(r⁻¹)^(d+n) = (r⁻¹)^n := by
  rw [pow_add,← mul_assoc,← mul_pow,mul_inv_cancel₀ hr,one_pow,one_mul]

lemma normalized_integral_order (f : V → ℂ) (g : V → E) (c : V → ℝ)
    (r : ℝ) (hr : 0 < r) (n : ℕ) (x : V) :
    (∫ y, f y • ((r*c y)⁻¹^(Module.finrank ℝ V+n) • g ((r*c y)⁻¹ • (x-y)))) =
      (r⁻¹)^n • ∫ z, f (x-r • z) •
        ((c (x-r • z))⁻¹^(Module.finrank ℝ V+n) • g ((c (x-r • z))⁻¹ • z)) := by
  rw [normalized_integral f g c r hr,dimension_cancel r hr.ne']
end SourceFrozenScaling

namespace SourceFrozenRows
open ScaledSchwartzConvolution SchwartzTimeScale
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def value (K : SchwartzMap V ℂ) (A : V → ℝ) (r : ℝ) (f : V →ᵇ ℂ) : V → ℂ :=
  ScaledSchwartzConvolution.value (fun y => r*(A y)^(1/4 : ℝ))
    (ContinuousLinearMap.lsmul ℝ ℂ) f K (Module.finrank ℝ V)

def row (K : SchwartzMap V ℂ) (A : V → ℝ) (r : ℝ) (f : V →ᵇ ℂ)
    (j : ℕ) : V → V [×j]→L[ℝ] ℂ :=
  ScaledSchwartzConvolution.value (fun y => r*(A y)^(1/4 : ℝ))
    (ContinuousLinearMap.lsmul ℝ ℂ) f (SchwartzDerivatives.iterated K j) (Module.finrank ℝ V+j)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
lemma radius_bounds (A : V → ℝ) (α β : ℝ) (hα : 0 < α)
    (hA : ∀ y, A y ∈ Icc α β) (r : ℝ) (hr : 0 < r) (y : V) :
    r*(A y)^(1/4 : ℝ) ∈ Icc (r*α^(1/4 : ℝ)) (r*β^(1/4 : ℝ)) := by
  constructor
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hα.le (hA y).1 (by norm_num)) hr.le
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (hα.trans_le (hA y).1).le (hA y).2 (by norm_num)) hr.le

lemma contDiff_value (K : SchwartzMap V ℂ) (A : V → ℝ) (hA : Continuous A)
    (α β : ℝ) (hα : 0 < α) (hAr : ∀ y, A y ∈ Icc α β)
    (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) : ContDiff ℝ ∞ (value K A r f) := by
  apply ScaledSchwartzConvolution.contDiff_value (a := r*α^(1/4 : ℝ))
    (b := r*β^(1/4 : ℝ)) (by positivity) _
    (continuous_const.mul (hA.rpow_const (fun _ => Or.inr (by norm_num))))
    (radius_bounds A α β hα hAr r hr)

lemma row_eq (K : SchwartzMap V ℂ) (A : V → ℝ) (hA : Continuous A)
    (α β : ℝ) (hα : 0 < α) (hAr : ∀ y, A y ∈ Icc α β)
    (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (j : ℕ) :
    row K A r f j = iteratedFDeriv ℝ j (value K A r f) := by
  symm
  apply ScaledSchwartzConvolution.iteratedFDeriv_value_smul (a := r*α^(1/4 : ℝ))
    (b := r*β^(1/4 : ℝ)) (by positivity) _
    (continuous_const.mul (hA.rpow_const (fun _ => Or.inr (by norm_num))))
    (radius_bounds A α β hα hAr r hr)

lemma row_normalized (K : SchwartzMap V ℂ) (A : V → ℝ)
    (hAp : ∀ y, 0 < A y) (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (j : ℕ) (x : V) :
    row K A r f j x = (r⁻¹)^j • ∫ z, f (x-r • z) •
      atTime (SchwartzDerivatives.iterated K j) (Module.finrank ℝ V+j) (A (x-r • z)) z := by
  unfold row ScaledSchwartzConvolution.value
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [SourceFrozenScaling.normalized_integral_order _ _ _ r hr]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [atTime_eq_scaled _ _ _ (hAp _)]

lemma exists_row_holder_bound (K : SchwartzMap V ℂ) (j : ℕ) (hj : 0 < j)
    (α β : ℝ) (hα : 0 < α) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (A : V → ℝ) (_hA : Continuous A) (_hAr : ∀ y, A y ∈ Icc α β)
        (L : ℝ) (_hL : 0 ≤ L) (_hAL : ∀ x y, ‖A x-A y‖ ≤ L*‖x-y‖)
        (f : V →ᵇ ℂ) (H : ℝ) (_hH : 0 ≤ H)
        (_hhold : ∀ x y, ‖f x-f y‖ ≤ H*‖x-y‖^γ)
        (r : ℝ) (_hr : 0 < r) (x : V),
      ‖row K A r f j x‖ ≤ (r⁻¹)^j*(H*r^γ*C+‖f‖*L*r*D) := by
  let K' := SchwartzDerivatives.iterated K j
  obtain ⟨B,hB,hBw,hBp,hb⟩ := SourceFrozenCancellation.parameter_envelope K' (Module.finrank ℝ V+j) α β hα
  obtain ⟨D,hD,hDw,hDp,hd⟩ := SourceFrozenCancellation.parameter_lipschitz_envelope K' (Module.finrank ℝ V+j) α β hα
  refine ⟨∫ z, ‖z‖^γ*B z, ∫ z, ‖z‖*D z,
    integral_nonneg (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hBp z)),
    integral_nonneg (fun z => mul_nonneg (norm_nonneg _) (hDp z)), ?_⟩
  intro A hA hAr L hL hAL f H hH hhold r hr x
  rw [row_normalized K A (fun y => hα.trans_le (hAr y).1) r hr,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hz : ∫ z, K' z = 0 := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    simp only [K',SchwartzDerivatives.iterated_apply]
    exact SchwartzDerivatives.integral_iterated K n
  exact SourceFrozenCancellation.norm_normalized_source_integral K' _ α β hα hz
    B D hB hBw hBp hD hDw hDp hb hd A hA hAr L hL hAL f γ H hγ hγ1 hH hhold r hr x
end SourceFrozenRows

namespace SourceFrozenOrder
open ScaledSchwartzConvolution SchwartzTimeScale
open scoped BoundedContinuousFunction ContDiff
variable {V E : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

def value (K : SchwartzMap V E) (A : V → ℝ) (r : ℝ) (f : V →ᵇ ℂ) (j : ℕ) : V → E :=
  ScaledSchwartzConvolution.value (fun y => r*(A y)^(1/4 : ℝ))
    (ContinuousLinearMap.lsmul ℝ ℂ) f K (Module.finrank ℝ V+j)

lemma normalized (K : SchwartzMap V E) (A : V → ℝ)
    (hAp : ∀ y, 0 < A y) (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (j : ℕ) (x : V) :
    value K A r f j x = (r⁻¹)^j • ∫ z, f (x-r • z) •
      atTime K (Module.finrank ℝ V+j) (A (x-r • z)) z := by
  unfold value ScaledSchwartzConvolution.value
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [SourceFrozenScaling.normalized_integral_order _ _ _ r hr]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [atTime_eq_scaled _ _ _ (hAp _)]

lemma exists_norm_bound (K : SchwartzMap V E) (j : ℕ) (α β : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : V → ℝ) (_hA : Continuous A)
      (_hAr : ∀ y, A y ∈ Icc α β) (r : ℝ) (_hr : 0 < r) (f : V →ᵇ ℂ) (x : V),
      ‖value K A r f j x‖ ≤ (r⁻¹)^j * (‖f‖*C) := by
  obtain ⟨B,hB,_hw,hBp,hb⟩ := SourceFrozenCancellation.parameter_envelope K (Module.finrank ℝ V+j) α β hα
  refine ⟨∫ z, B z,integral_nonneg hBp,?_⟩
  intro A hA hAr r hr f x
  rw [normalized K A (fun y => hα.trans_le (hAr y).1) r hr,norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ (r⁻¹)^j)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hi : Integrable (fun z => f (x-r • z) •
      atTime K (Module.finrank ℝ V+j) (A (x-r • z)) z) := by
    apply (hB.const_mul ‖f‖).mono'
    · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul
        (SourceFrozenCancellation.continuous_variable K _ (fun z => A (x-r • z))
          (hA.comp (continuous_const.sub (continuous_const.smul continuous_id)))
          (fun z => hα.trans_le (hAr _).1))).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)
  change ‖∫ z, f (x-r • z) • atTime K _ (A (x-r • z)) z‖ ≤ _
  calc
    _ ≤ ∫ z, ‖f (x-r • z) • atTime K _ (A (x-r • z)) z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖f‖*B z := by
      apply integral_mono hi.norm (hB.const_mul ‖f‖)
      intro z
      dsimp only
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)
    _ = _ := integral_const_mul ..

lemma hasFDerivAt_value (K : SchwartzMap V E) (A : V → ℝ) (hA : Continuous A)
    (α β : ℝ) (hα : 0 < α) (hAr : ∀ y, A y ∈ Icc α β)
    (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (j : ℕ) (x : V) :
    HasFDerivAt (value K A r f j)
      (value (SchwartzMap.fderivCLM ℝ V E K) A r f (j+1) x) x := by
  have h := ScaledSchwartzConvolution.hasFDerivAt_value
    (a := r*α^(1/4 : ℝ)) (b := r*β^(1/4 : ℝ)) (by positivity)
    (fun y => r*(A y)^(1/4 : ℝ))
    (continuous_const.mul (hA.rpow_const (fun _ => Or.inr (by norm_num))))
    (SourceFrozenRows.radius_bounds A α β hα hAr r hr)
    (ContinuousLinearMap.lsmul ℝ ℂ) f K (Module.finrank ℝ V+j) x
  have he : (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E).precompR V =
      (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] (V →L[ℝ] E) →L[ℝ] (V →L[ℝ] E)) := by
    ext c g v
    rfl
  simpa only [value, Nat.add_assoc, he] using h

lemma exists_bounds (K : SchwartzMap V E) (j : ℕ) (α β : ℝ) (hα : 0 < α) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (A : V → ℝ) (_hA : Continuous A) (_hAr : ∀ z, A z ∈ Icc α β)
        (r : ℝ) (_hr : 0 < r) (f : V →ᵇ ℂ),
        (∀ x, ‖value K A r f j x‖ ≤ (r⁻¹)^j*(‖f‖*C)) ∧
        (∀ x y, ‖value K A r f j x-value K A r f j y‖ ≤ ((r⁻¹)^(j+1)*(‖f‖*D))*‖x-y‖) := by
  obtain ⟨C,hC,hb⟩ := exists_norm_bound K j α β hα
  obtain ⟨D,hD,hd⟩ := exists_norm_bound (SchwartzMap.fderivCLM ℝ V E K) (j+1) α β hα
  refine ⟨C,D,hC,hD,?_⟩
  intro A hA hAr r hr f
  refine ⟨hb A hA hAr r hr f,fun x y => ?_⟩
  exact (convex_univ : Convex ℝ (univ : Set V)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hasFDerivAt_value K A hA α β hα hAr r hr f j z).hasFDerivWithinAt)
    (fun z _ => hd A hA hAr r hr f z) (mem_univ y) (mem_univ x)
end SourceFrozenOrder

namespace FrozenParametrix
open scoped SchwartzMap Laplacian ZeroAtInfty BoundedContinuousFunction
open BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def bilapOne : SchwartzMap V ℂ := Δ (Δ (heatKernel (V := V) 1 zero_lt_one) : SchwartzMap V ℂ)

def heatOne : SchwartzMap V ℂ := heatKernel 1 zero_lt_one

lemma quarter_root (t : ℝ) (ht : 0 < t) : Real.sqrt (Real.sqrt t) = t^(1/4 : ℝ) := by
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul ht.le]
  norm_num

lemma bilapKernel_ordered (t : ℝ) (ht : 0 < t) (r : ℝ) (hr : 0 < r) (z : V) :
    bilapKernel (r^4*t) z = ((r*t^(1/4 : ℝ))⁻¹)^(Module.finrank ℝ V+4) •
      bilapOne ((r*t^(1/4 : ℝ))⁻¹ • z) := by
  rw [bilapKernel_scaling t ht r hr,bilapKernel_eq_scaled t ht,quarter_root t ht]
  dsimp only [bilapOne]
  rw [mul_inv,mul_pow,smul_smul,smul_smul]
  congr 2
  rw [mul_comm]

lemma kernel_ordered (t : ℝ) (ht : 0 < t) (r : ℝ) (hr : 0 < r) (z : V) :
    kernel (r^4*t) z = ((r*t^(1/4 : ℝ))⁻¹)^(Module.finrank ℝ V) •
      heatOne ((r*t^(1/4 : ℝ))⁻¹ • z) := by
  have hs := heatKernel_scaling t ht r hr z
  rw [heatKernel_eq_kernel,heatKernel_eq_kernel] at hs
  rw [hs,kernel_eq_scaled t ht,quarter_root t ht]
  dsimp only [heatOne]
  rw [mul_inv,mul_pow,smul_smul,smul_smul]
  simp only [inv_pow]
  congr 2
  rw [mul_comm]

lemma integrable_ordered (K : SchwartzMap V ℂ) (j : ℕ) {α β : ℝ} (hα : 0 < α)
    (a : C(V,Icc α β)) (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (x : V) :
    Integrable (fun y => f y • (((r*(a y).val^(1/4 : ℝ))⁻¹)^(Module.finrank ℝ V+j) •
      K ((r*(a y).val^(1/4 : ℝ))⁻¹ • (x-y)))) := by
  exact ScaledSchwartzConvolution.integrable_integrand
    (a := r*α^(1/4 : ℝ)) (b := r*β^(1/4 : ℝ)) (by positivity)
    (fun y => r*(a y).val^(1/4 : ℝ))
    (continuous_const.mul ((continuous_subtype_val.comp a.continuous).rpow_const
      (fun _ => Or.inr (by norm_num))))
    (SourceFrozenRows.radius_bounds (fun y => (a y).val) α β hα (fun y => (a y).property) r hr)
    (ContinuousLinearMap.lsmul ℝ ℂ) f K (Module.finrank ℝ V+j) x

lemma principal_eq_ordered {α β : ℝ} (hα : 0 < α) (a₀ a₁ : C(V,Icc α β))
    (r : ℝ) (hr : 0 < r) (f : C₀(V,ℂ)) (x : V) :
    principalResidual hα a₀ a₁ r f x = coefficient a₁ x *
      SourceFrozenOrder.value bilapOne (fun y => (a₀ y).val) r f.toBCF 4 x -
      SourceFrozenOrder.value bilapOne (fun y => (a₀ y).val) r (coefficient a₀*f.toBCF) 4 x := by
  rw [principalResidual_apply_unscaled hα a₀ a₁ r hr]
  simp_rw [bilapKernel_ordered _ (hα.trans_le (a₀ _).property.1) r hr]
  have hi := integrable_ordered bilapOne 4 hα a₀ r hr f.toBCF x
  have hi' := integrable_ordered bilapOne 4 hα a₀ r hr (coefficient a₀*f.toBCF) x
  unfold SourceFrozenOrder.value ScaledSchwartzConvolution.value
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul] at hi hi' ⊢
  rw [← integral_const_mul,← integral_sub (hi.const_mul (coefficient a₁ x)) hi']
  apply integral_congr_ae
  filter_upwards with y
  simp only [coefficient_apply,BoundedContinuousFunction.coe_mul,Pi.mul_apply,
    Complex.ofReal_sub]
  change (_-_)*_*f y = _*(f y*_)-(_*f y)*_
  ring

lemma frozen_eq_ordered {α β : ℝ} (hα : 0 < α) (a₀ : C(V,Icc α β))
    (r : ℝ) (hr : 0 < r) (f : C₀(V,ℂ)) (x : V) :
    frozenOp hα a₀ r f x = SourceFrozenOrder.value heatOne (fun y => (a₀ y).val) r f.toBCF 0 x := by
  rw [frozenOp,frozen_apply_unscaled _ _ _ _ _ _ _ hr]
  unfold SourceFrozenOrder.value ScaledSchwartzConvolution.value
  simp only [Nat.add_zero,ContinuousLinearMap.lsmul_apply,smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [kernel_ordered _ (hα.trans_le (a₀ _).property.1) r hr]
  exact mul_comm _ _
end FrozenParametrix

open Set MeasureTheory
namespace ProductLipschitz
lemma bound {X : Type*} [NormedAddCommGroup X] (a u : X → ℂ)
    (B L M N : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (ha : ∀ x, ‖a x‖ ≤ B) (hu : ∀ x, ‖u x‖ ≤ M)
    (hal : ∀ x y, ‖a x-a y‖ ≤ L*‖x-y‖)
    (hul : ∀ x y, ‖u x-u y‖ ≤ N*‖x-y‖) (x y : X) :
    ‖a x*u x-a y*u y‖ ≤ (B*N+L*M)*‖x-y‖ := by
  have he : a x*u x-a y*u y = a x*(u x-u y)+(a x-a y)*u y := by ring
  rw [he]
  calc
    _ ≤ ‖a x*(u x-u y)‖+‖(a x-a y)*u y‖ := norm_add_le ..
    _ = ‖a x‖*‖u x-u y‖+‖a x-a y‖*‖u y‖ := by rw [norm_mul,norm_mul]
    _ ≤ B*(N*‖x-y‖)+(L*‖x-y‖)*M := add_le_add
      (mul_le_mul (ha x) (hul x y) (norm_nonneg _) hB)
      (mul_le_mul (hal x y) (hu y) (norm_nonneg _) (mul_nonneg hL (norm_nonneg _)))
    _ = _ := by ring

lemma inv_pow_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {j k : ℕ} (hjk : j ≤ k) :
    (r⁻¹)^j ≤ (r⁻¹)^k := by
  have hh : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
  exact pow_le_pow_right₀ hh hjk
end ProductLipschitz

namespace FrozenParametrix
open scoped SchwartzMap Laplacian ZeroAtInfty BoundedContinuousFunction
open BiharmonicKernel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma norm_coefficient_le_pos {α β : ℝ} (hα : 0 < α) (a : C(V,Icc α β)) :
    ‖coefficient a‖ ≤ max β 0 := by
  apply (BoundedContinuousFunction.norm_le (le_max_right _ _)).mpr
  intro x
  rw [coefficient_apply,Complex.norm_real,Real.norm_of_nonneg (hα.le.trans (a x).property.1)]
  exact (a x).property.2.trans (le_max_left _ _)

lemma exists_principal_lipschitz_bound (α β : ℝ) (hα : 0 < α) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a₀ a₁ : C(V,Icc α β))
      (_hLip : ∀ x y, |(a₁ x).val-(a₁ y).val| ≤ L*‖x-y‖)
      (r : ℝ) (_hr : 0 < r) (_hr1 : r ≤ 1) (f : C₀(V,ℂ)) (x y : V),
      ‖principalResidual hα a₀ a₁ r f x-principalResidual hα a₀ a₁ r f y‖ ≤
        ((r⁻¹)^5*‖f‖*C)*‖x-y‖ := by
  obtain ⟨C,D,hC,hD,hb⟩ := SourceFrozenOrder.exists_bounds (bilapOne : SchwartzMap V ℂ) 4 α β hα
  let B := max β 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨L*C+2*B*D,by positivity,?_⟩
  intro a₀ a₁ hLip r hr hr1 f x y
  let A := fun z => (a₀ z).val
  have hA : Continuous A := continuous_subtype_val.comp a₀.continuous
  have hAr : ∀ z, A z ∈ Icc α β := fun z => (a₀ z).property
  obtain ⟨hu,hul⟩ := hb A hA hAr r hr f.toBCF
  obtain ⟨_hv,hvl⟩ := hb A hA hAr r hr (coefficient a₀*f.toBCF)
  have ha : ∀ z, ‖coefficient a₁ z‖ ≤ B := fun z =>
    ((coefficient a₁).norm_coe_le_norm z).trans (norm_coefficient_le_pos hα a₁)
  have hal : ∀ z w, ‖coefficient a₁ z-coefficient a₁ w‖ ≤ L*‖z-w‖ := by
    intro z w
    simpa only [coefficient_apply,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hLip z w
  have hmul : ‖coefficient a₀*f.toBCF‖ ≤ B*‖f‖ := by
    simpa only [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using
      (norm_mul_le (coefficient a₀) f.toBCF).trans
        (mul_le_mul_of_nonneg_right (norm_coefficient_le_pos hα a₀) (norm_nonneg f.toBCF))
  have hp := ProductLipschitz.bound (coefficient a₁)
    (SourceFrozenOrder.value bilapOne A r f.toBCF 4)
    B L ((r⁻¹)^4*(‖f.toBCF‖*C)) ((r⁻¹)^5*(‖f.toBCF‖*D)) hB hL ha hu hal hul x y
  simp_rw [principal_eq_ordered hα a₀ a₁ r hr]
  calc
    _ = ‖(coefficient a₁ x*SourceFrozenOrder.value bilapOne A r f.toBCF 4 x-
          coefficient a₁ y*SourceFrozenOrder.value bilapOne A r f.toBCF 4 y)-
          (SourceFrozenOrder.value bilapOne A r (coefficient a₀*f.toBCF) 4 x-
          SourceFrozenOrder.value bilapOne A r (coefficient a₀*f.toBCF) 4 y)‖ := by congr 1; ring
    _ ≤ ‖coefficient a₁ x*SourceFrozenOrder.value bilapOne A r f.toBCF 4 x-
          coefficient a₁ y*SourceFrozenOrder.value bilapOne A r f.toBCF 4 y‖+
          ‖SourceFrozenOrder.value bilapOne A r (coefficient a₀*f.toBCF) 4 x-
          SourceFrozenOrder.value bilapOne A r (coefficient a₀*f.toBCF) 4 y‖ := norm_sub_le ..
    _ ≤ (B*((r⁻¹)^5*(‖f.toBCF‖*D))+L*((r⁻¹)^4*(‖f.toBCF‖*C)))*‖x-y‖+
          ((r⁻¹)^5*(‖coefficient a₀*f.toBCF‖*D))*‖x-y‖ := add_le_add hp (hvl x y)
    _ ≤ (B*((r⁻¹)^5*(‖f‖*D))+L*((r⁻¹)^5*(‖f‖*C)))*‖x-y‖+
          ((r⁻¹)^5*((B*‖f‖)*D))*‖x-y‖ := by
      simp only [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      gcongr <;> first | exact hmul | exact (one_le_inv₀ hr).mpr hr1 | norm_num
    _ = _ := by ring

lemma exists_frozen_lipschitz_bound (α β : ℝ) (hα : 0 < α) (B L : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : C(V,Icc α β)) (b : V →ᵇ ℂ)
      (_hb : ‖b‖ ≤ B) (_hLip : ∀ x y, ‖b x-b y‖ ≤ L*‖x-y‖)
      (r : ℝ) (_hr : 0 < r) (_hr1 : r ≤ 1) (f : C₀(V,ℂ)) (x y : V),
      ‖b x*frozenOp hα a r f x-b y*frozenOp hα a r f y‖ ≤
        ((r⁻¹)^5*‖f‖*C)*‖x-y‖ := by
  obtain ⟨C,D,hC,hD,hbound⟩ := SourceFrozenOrder.exists_bounds (heatOne : SchwartzMap V ℂ) 0 α β hα
  refine ⟨B*D+L*C,by positivity,?_⟩
  intro a b hb hLip r hr hr1 f x y
  obtain ⟨hu,hul⟩ := hbound (fun z => (a z).val) (continuous_subtype_val.comp a.continuous)
    (fun z => (a z).property) r hr f.toBCF
  have hh := ProductLipschitz.bound b
    (SourceFrozenOrder.value heatOne (fun z => (a z).val) r f.toBCF 0)
    B L ((r⁻¹)^0*(‖f.toBCF‖*C)) ((r⁻¹)^1*(‖f.toBCF‖*D)) hB hL
    (fun z => (b.norm_coe_le_norm z).trans hb) hu hLip hul x y
  simp_rw [frozen_eq_ordered hα a r hr]
  apply hh.trans
  calc
    _ ≤ (B*((r⁻¹)^5*(‖f‖*D))+L*((r⁻¹)^5*(‖f‖*C)))*‖x-y‖ := by
      simp only [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      gcongr <;> first | exact (one_le_inv₀ hr).mpr hr1 | norm_num
    _ = _ := by ring

lemma exists_fullResidual_lipschitz_bound (α β : ℝ) (hα : 0 < α) (B L : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a₀ a₁ : C(V,Icc α β)) (b : V →ᵇ ℂ)
      (_hb : ‖b‖ ≤ B) (_hLipa : ∀ x y, |(a₁ x).val-(a₁ y).val| ≤ L*‖x-y‖)
      (_hLipb : ∀ x y, ‖b x-b y‖ ≤ L*‖x-y‖)
      (r : ℝ) (_hr : 0 < r) (_hr1 : r ≤ 1) (f : C₀(V,ℂ)) (x y : V),
      ‖fullResidualCLM hα a₀ a₁ b r f x-fullResidualCLM hα a₀ a₁ b r f y‖ ≤
        ((r⁻¹)^5*‖f‖*C)*‖x-y‖ := by
  obtain ⟨C,hC,hp⟩ := exists_principal_lipschitz_bound (V := V) α β hα L hL
  obtain ⟨D,hD,hf⟩ := exists_frozen_lipschitz_bound (V := V) α β hα B L hB hL
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro a₀ a₁ b hb ha hl r hr hr1 f x y
  have he : fullResidualCLM hα a₀ a₁ b r f x-fullResidualCLM hα a₀ a₁ b r f y =
      (principalResidual hα a₀ a₁ r f x-principalResidual hα a₀ a₁ r f y)+
      (b x*frozenOp hα a₀ r f x-b y*frozenOp hα a₀ r f y) := by
    simp only [fullResidualCLM_apply, ZeroAtInftyContinuousMap.add_apply, C0Multiplier.mul_apply]
    ring
  rw [he]
  calc
    _ ≤ ‖principalResidual hα a₀ a₁ r f x-principalResidual hα a₀ a₁ r f y‖+
      ‖b x*frozenOp hα a₀ r f x-b y*frozenOp hα a₀ r f y‖ := norm_add_le ..
    _ ≤ ((r⁻¹)^5*‖f‖*C)*‖x-y‖+((r⁻¹)^5*‖f‖*D)*‖x-y‖ :=
      add_le_add (hp a₀ a₁ ha r hr hr1 f x y) (hf a₀ b hb hl r hr hr1 f x y)
    _ = _ := by ring
end FrozenParametrix

open scoped Topology
namespace HolderInterpolation
lemma scalar {z A B δ γ : ℝ} (hz : 0 ≤ z) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hγ : 0 < γ) (hγ1 : γ < 1) (ha : z ≤ A) (hb : z ≤ B*δ) :
    z ≤ A^(1-γ)*B^γ*δ^γ := by
  by_cases hz0 : z = 0
  · rw [hz0]; positivity
  have hz' : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  calc
    _ = z^(1-γ)*z^γ := by rw [← Real.rpow_add hz']; simp
    _ ≤ A^(1-γ)*(B*δ)^γ := mul_le_mul
      (Real.rpow_le_rpow hz ha (by linarith)) (Real.rpow_le_rpow hz hb hγ.le)
      (Real.rpow_nonneg hz _) (Real.rpow_nonneg hA _)
    _ = _ := by rw [Real.mul_rpow hB hδ]; ring

lemma scaled {z C δ q γ p₀ p₁ : ℝ} (hz : 0 ≤ z) (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hq : 0 < q) (hγ : 0 < γ) (hγ1 : γ < 1)
    (ha : z ≤ C*q^p₀) (hb : z ≤ (C*q^p₁)*δ) :
    z ≤ C*q^(p₀*(1-γ)+p₁*γ)*δ^γ := by
  by_cases hC0 : C = 0
  · simpa only [hC0,zero_mul] using ha
  have hC' : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  have he := scalar hz (mul_nonneg hC (Real.rpow_nonneg hq.le _))
    (mul_nonneg hC (Real.rpow_nonneg hq.le _)) hδ hγ hγ1 ha hb
  rw [Real.mul_rpow hC (Real.rpow_nonneg hq.le _),
    Real.mul_rpow hC (Real.rpow_nonneg hq.le _),
    ← Real.rpow_mul hq.le,← Real.rpow_mul hq.le] at he
  have heq : C^(1-γ)*q^(p₀*(1-γ))*(C^γ*q^(p₁*γ))*δ^γ =
      C*q^(p₀*(1-γ)+p₁*γ)*δ^γ := by
    calc
      _ = (C^(1-γ)*C^γ)*(q^(p₀*(1-γ))*q^(p₁*γ))*δ^γ := by ring
      _ = _ := by rw [← Real.rpow_add hC',← Real.rpow_add hq]; simp
  exact heq ▸ he

lemma residual {z C δ q γ : ℝ} (hz : 0 ≤ z) (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hq : 0 < q) (hγ : 0 < γ) (hγ1 : γ < 1)
    (ha : z ≤ C*q^(-(3/4 : ℝ))) (hb : z ≤ (C*q^(-(5/4 : ℝ)))*δ) :
    z ≤ C*q^(-(3+2*γ)/4)*δ^γ := by
  simpa only [show (-(3/4 : ℝ))*(1-γ)+ (-(5/4 : ℝ))*γ = -(3+2*γ)/4 by ring] using
    (scaled hz hC hδ hq hγ hγ1 ha hb)
end HolderInterpolation

namespace ParabolicRadius
lemma inv_pow_five {q : ℝ} (hq : 0 ≤ q) : (radius q)⁻¹^5 = q^(-5/4 : ℝ) := by
  unfold radius
  rw [← Real.rpow_natCast,← Real.rpow_neg hq,← Real.rpow_mul hq]
  congr 1
  norm_num
end ParabolicRadius

namespace ParametrixVolterra
open scoped ZeroAtInfty BoundedContinuousFunction
open FrozenParametrix C0Convolution StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T, V →ᵇ Icc α β)) (b : C(Slab T, V →ᵇ ℂ))

lemma exists_actualResidual_holder_bound (hT : T ≤ 1) (L B : ℝ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hb : ∀ s, ‖b s‖ ≤ B)
    (hLip : ∀ s r : Slab T, ∀ x z : V,
      |(A s x).val-(A r z).val| ≤ L*(‖x-z‖+|s.val-r.val|))
    (hLipb : ∀ s : Slab T, ∀ x z : V, ‖b s x-b s z‖ ≤ L*‖x-z‖)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : Time T) (s : Slab T) (_hst : s.val<t.val)
      (f : C₀(V,ℂ)) (x y : V),
      ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
        C*‖f‖*(t.val-s.val)^(-(3+2*γ)/4)*‖x-y‖^γ := by
  obtain ⟨C,hC,hb₀⟩ := exists_actualResidual_bound hα A b hT L B hL hB hb hLip
  obtain ⟨D,hD,hb₁⟩ := exists_fullResidual_lipschitz_bound (V := V) α β hα B L hB hL
  refine ⟨2*C+D,by positivity,?_⟩
  intro t s hst f x y
  let q := t.val-s.val
  have hq : 0 < q := sub_pos.mpr hst
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [t.property.2,s.property.1]
  have hnorm (z : V) : ‖actualResidual hα A b t s f z‖ ≤ C*q^(-3/4 : ℝ)*‖f‖ :=
    ((actualResidual hα A b t s f).toBCF.norm_coe_le_norm z).trans
      (((actualResidual hα A b t s).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (hb₀ t s hst) (norm_nonneg f)))
  have hs : ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
      ((2*C+D)*‖f‖)*q^(-3/4 : ℝ) := by
    calc
      _ ≤ ‖actualResidual hα A b t s f x‖+‖actualResidual hα A b t s f y‖ := norm_sub_le ..
      _ ≤ C*q^(-3/4 : ℝ)*‖f‖+C*q^(-3/4 : ℝ)*‖f‖ := add_le_add (hnorm x) (hnorm y)
      _ ≤ _ := by nlinarith [mul_nonneg hD (mul_nonneg (norm_nonneg f) (Real.rpow_nonneg hq.le (-3/4 : ℝ)))]
  have hl : ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
      (((2*C+D)*‖f‖)*q^(-5/4 : ℝ))*‖x-y‖ := by
    have h := hb₁ (A s).toContinuousMap (A (now t)).toContinuousMap (b (now t)) (hb _)
      (fun z w => by
        change |(A (now t) z).val-(A (now t) w).val| ≤ L*‖z-w‖
        simpa only [sub_self,abs_zero,add_zero] using hLip (now t) (now t) z w)
      (hLipb _) (ParabolicRadius.radius q) (ParabolicRadius.pos hq)
      (ParabolicRadius.le_one hq.le hq1) f x y
    rw [ParabolicRadius.inv_pow_five hq.le] at h
    apply h.trans
    calc
      _ = D*‖f‖*q^(-5/4 : ℝ)*‖x-y‖ := by ring
      _ ≤ _ := by gcongr; nlinarith
  simpa only [neg_div] using HolderInterpolation.residual (norm_nonneg _)
    (show 0 ≤ (2*C+D)*‖f‖ by positivity) (norm_nonneg (x-y)) hq hγ hγ1
    (by simpa only [neg_div] using hs) (by simpa only [neg_div] using hl)
end ParametrixVolterra

open Set MeasureTheory
namespace BetaWeights

def density (σ ρ t s : ℝ) : ℝ := s^(-σ)*(t-s)^(-ρ)

lemma density_nonneg (σ ρ t s : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) : 0 ≤ density σ ρ t s := by
  exact mul_nonneg (Real.rpow_nonneg hs _) (Real.rpow_nonneg (sub_nonneg.mpr hst) _)

lemma intervalIntegrable_one (σ ρ : ℝ) (hσ : σ < 1) (hρ : ρ < 1) :
    IntervalIntegrable (density σ ρ 1) volume 0 1 := by
  have hb := (Complex.betaIntegral_convergent
    (u := ((1-σ : ℝ) : ℂ)) (v := ((1-ρ : ℝ) : ℂ)) (by simpa using sub_pos.mpr hσ)
      (by simpa using sub_pos.mpr hρ)).norm
  apply hb.congr_ae
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  dsimp only [density]
  rw [norm_mul]
  have hq : ((1-σ : ℝ) : ℂ)-1 = ((-σ : ℝ) : ℂ) := by push_cast; ring
  have hr : ((1-ρ : ℝ) : ℂ)-1 = ((-ρ : ℝ) : ℂ) := by push_cast; ring
  rw [hq,hr,show (1 : ℂ)-(x : ℂ) = ((1-x : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_real,Complex.norm_cpow_real,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hx.1,abs_of_pos (sub_pos.mpr hx.2)]

lemma density_scaled (σ ρ t s : ℝ) (ht : 0 < t) (hs : s ∈ Ioo 0 1) :
    density σ ρ t (t*s) = (t^(-σ)*t^(-ρ))*density σ ρ 1 s := by
  unfold density
  rw [show t-t*s = t*(1-s) by ring,Real.mul_rpow ht.le hs.1.le,
    Real.mul_rpow ht.le (sub_nonneg.mpr hs.2.le)]
  ring

lemma intervalIntegrable (σ ρ : ℝ) (hσ : σ < 1) (hρ : ρ < 1) (t : ℝ) (ht : 0 < t) :
    IntervalIntegrable (density σ ρ t) volume 0 t := by
  rw [← IntervalIntegrable.comp_mul_left_iff ht.ne']
  simp only [zero_div,div_self ht.ne']
  apply ((intervalIntegrable_one σ ρ hσ hρ).const_mul (t^(-σ)*t^(-ρ))).congr_ae
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hmem : ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) 1), s ∈ Ioo 0 1 := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem] with s hs
  exact (density_scaled σ ρ t s ht hs).symm

lemma integral_scale (σ ρ t : ℝ) (ht : 0 < t) :
    (∫ s in 0..t, density σ ρ t s) = t^(1-σ-ρ)*(∫ s in 0..1, density σ ρ 1 s) := by
  have hc := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (density σ ρ t) t
  simp only [mul_zero,mul_one,smul_eq_mul] at hc
  rw [← hc]
  have he : (∫ s in 0..1, density σ ρ t (t*s)) =
      (t^(-σ)*t^(-ρ))*(∫ s in 0..1, density σ ρ 1 s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),← ae_restrict_iff' measurableSet_Ioc,← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact density_scaled σ ρ t s ht hs
  rw [he,← mul_assoc]
  congr 1
  calc
    _ = t^(1 : ℝ)*(t^(-σ)*t^(-ρ)) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add ht,← Real.rpow_add ht]; congr 1; ring
end BetaWeights

namespace HolderIntegral
open scoped ZeroAtInfty BoundedContinuousFunction
variable {V : Type*} [TopologicalSpace V]

def eval (x : V) : C₀(V,ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun f => by
        change ‖f.toBCF x‖ ≤ 1*‖f‖
        simpa only [one_mul,ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using f.toBCF.norm_coe_le_norm x)

lemma intervalIntegral_apply (f : ℝ → C₀(V,ℂ)) {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (x : V) :
    (∫ s in a..b, f s) x = ∫ s in a..b, f s x :=
  ((eval x).intervalIntegral_comp_comm hf).symm

lemma beta_holder {x y : V} (f : ℝ → C₀(V,ℂ)) (t : ℝ) (ht : 0 < t)
    (hf : IntervalIntegrable f volume 0 t) (σ ρ : ℝ) (hσ : σ < 1) (hρ : ρ < 1)
    (C δ : ℝ) (h : ∀ s ∈ Ioo 0 t,
      ‖f s x-f s y‖ ≤ C*BetaWeights.density σ ρ t s*δ) :
    ‖(∫ s in 0..t, f s) x-(∫ s in 0..t, f s) y‖ ≤
      C*t^(1-σ-ρ)*(∫ s in 0..1, BetaWeights.density σ ρ 1 s)*δ := by
  rw [intervalIntegral_apply f hf x,intervalIntegral_apply f hf y,
    ← intervalIntegral.integral_sub (show IntervalIntegrable (fun s => f s x) volume 0 t from ⟨(eval x).integrable_comp hf.1,(eval x).integrable_comp hf.2⟩)
      (show IntervalIntegrable (fun s => f s y) volume 0 t from ⟨(eval y).integrable_comp hf.1,(eval y).integrable_comp hf.2⟩)]
  calc
    _ ≤ ∫ s in 0..t, C*BetaWeights.density σ ρ t s*δ := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht.le
      · rw [← ae_restrict_iff' measurableSet_Ioc,← restrict_Ioo_eq_restrict_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact h s hs
      · exact ((BetaWeights.intervalIntegrable σ ρ hσ hρ t ht).const_mul C).mul_const δ
    _ = _ := by
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,
        BetaWeights.integral_scale σ ρ t ht]
      ring
end HolderIntegral
namespace ParametrixVolterra
open scoped ZeroAtInfty BoundedContinuousFunction
open FrozenParametrix C0Convolution StrongWeightedVolterra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {T α β : ℝ} (hα : 0 < α) (A : C(Slab T, V →ᵇ Icc α β)) (b : C(Slab T, V →ᵇ ℂ))

lemma holder_residual_integral (hT₀ : 0 ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ (t : Time T) (s : Slab T), s.val<t.val → ∀ (f : C₀(V,ℂ)) (x y : V),
      ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
        C*‖f‖*(t.val-s.val)^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ))
    (j : Time T →ᵇ C₀(V,ℂ)) (t : Time T)
    (hi : IntervalIntegrable (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val)
    (x y : V) :
    ‖(∫ r in 0..t.val, residualKernel hα A b hT₀ t r (unweighted j r)) x-
      (∫ r in 0..t.val, residualKernel hα A b hT₀ t r (unweighted j r)) y‖ ≤
      (C*‖j‖)*t.val^(-5/8 : ℝ)*(∫ s in 0..1, BetaWeights.density (3/4) (7/8) 1 s)*‖x-y‖^(1/4 : ℝ) := by
  have hh := HolderIntegral.beta_holder (x := x) (y := y)
    (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) t.val t.property.1 hi
    (3/4) (7/8) (by norm_num) (by norm_num) (C*‖j‖) (‖x-y‖^(1/4 : ℝ))
  apply (show 1-(3/4 : ℝ)-7/8 = -5/8 by norm_num) ▸ hh
  intro r hr
  let s : Slab T := ⟨r,hr.1.le,hr.2.le.trans t.property.2⟩
  have he : projIcc 0 T hT₀ r = s := projIcc_of_mem hT₀ s.property
  have hu : ‖unweighted j r‖ ≤ r^(-3/4 : ℝ)*‖j‖ := by
    let u : Time T := ⟨r,hr.1,hr.2.le.trans t.property.2⟩
    change ‖unweighted j u.val‖ ≤ _
    rw [unweighted_at_time,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr.1.le _)]
    exact mul_le_mul_of_nonneg_left (j.norm_coe_le_norm u) (Real.rpow_nonneg hr.1.le _)
  simp only [residualKernel,ite_eq_left hr,he]
  calc
    _ ≤ C*‖unweighted j r‖*(t.val-r)^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ) := hR t s hr.2 _ x y
    _ ≤ C*(r^(-3/4 : ℝ)*‖j‖)*(t.val-r)^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ) := by
      gcongr
      exact Real.rpow_nonneg (sub_nonneg.mpr hr.2.le) _
    _ = _ := by unfold BetaWeights.density; ring_nf

lemma correction_holder (hT₀ : 0 ≤ T) (hT : T ≤ 1) (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ (t : Time T) (s : Slab T), s.val<t.val → ∀ (f : C₀(V,ℂ)) (x y : V),
      ‖actualResidual hα A b t s f x-actualResidual hα A b t s f y‖ ≤
        C*‖f‖*(t.val-s.val)^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ))
    (d : C₀(V,ℂ)) (l j : Time T →ᵇ C₀(V,ℂ)) (H : ℝ) (hH : 0 ≤ H)
    (hl : ∀ t x y, ‖l t x-l t y‖ ≤ H*‖x-y‖^(1/4 : ℝ))
    (hi : ∀ t : Time T, IntervalIntegrable
      (fun r => residualKernel hα A b hT₀ t r (unweighted j r)) volume 0 t.val)
    (hj : ∀ t : Time T, unweighted j t.val + ∫ r in 0..t.val,
      residualKernel hα A b hT₀ t r (unweighted j r) = l t-actualResidual hα A b t (initial hT₀) d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : Time T, ∀ x y,
      ‖unweighted j t.val x-unweighted j t.val y‖ ≤ D*t.val^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ) := by
  let Q := ∫ s in 0..1, BetaWeights.density (3/4) (7/8) 1 s
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
    (fun s hs => BetaWeights.density_nonneg _ _ _ _ hs.1 hs.2)
  refine ⟨H+C*‖d‖+C*‖j‖*Q,by positivity,fun t x y => ?_⟩
  let v := ∫ r in 0..t.val, residualKernel hα A b hT₀ t r (unweighted j r)
  have he : unweighted j t.val = l t-actualResidual hα A b t (initial hT₀) d-v :=
    eq_sub_of_add_eq (hj t)
  have hd := hR t (initial hT₀) t.property.1 d x y
  simp only [initial,sub_zero] at hd
  have hv := holder_residual_integral hα A b hT₀ C hC hR j t (hi t) x y
  have ht1 : t.val ≤ 1 := t.property.2.trans hT
  have hp : 1 ≤ t.val^(-7/8 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos t.property.1 ht1 (by norm_num)
  have hq : t.val^(-5/8 : ℝ) ≤ t.val^(-7/8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge t.property.1 ht1 (by norm_num)
  rw [he]
  change ‖(l t x-actualResidual hα A b t (initial hT₀) d x-v x)-
    (l t y-actualResidual hα A b t (initial hT₀) d y-v y)‖ ≤ _
  calc
    _ = ‖(l t x-l t y)-(actualResidual hα A b t (initial hT₀) d x-
      actualResidual hα A b t (initial hT₀) d y)-(v x-v y)‖ := by congr 1; ring
    _ ≤ ‖l t x-l t y‖+‖actualResidual hα A b t (initial hT₀) d x-
      actualResidual hα A b t (initial hT₀) d y‖+‖v x-v y‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ H*‖x-y‖^(1/4 : ℝ)+C*‖d‖*t.val^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ)+
      (C*‖j‖)*t.val^(-5/8 : ℝ)*Q*‖x-y‖^(1/4 : ℝ) := add_le_add (add_le_add (hl t x y) hd) hv
    _ ≤ H*t.val^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ)+C*‖d‖*t.val^(-7/8 : ℝ)*‖x-y‖^(1/4 : ℝ)+
      (C*‖j‖)*t.val^(-7/8 : ℝ)*Q*‖x-y‖^(1/4 : ℝ) := by gcongr; exact le_mul_of_one_le_right hH hp
    _ = _ := by ring
end ParametrixVolterra

namespace SourceFrozenRows
section ExistsRowZeroBound
open ScaledSchwartzConvolution SchwartzTimeScale
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma exists_row_zero_bound (K : SchwartzMap V ℂ) (α β : ℝ) (hα : 0 < α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : V → ℝ) (_hA : Continuous A)
      (_hAr : ∀ y, A y ∈ Icc α β) (r : ℝ) (_hr : 0 < r) (f : V →ᵇ ℂ) (x : V),
      ‖row K A r f 0 x‖ ≤ ‖f‖*C := by
  let K' := SchwartzDerivatives.iterated K 0
  obtain ⟨B,hB,_hw,hBp,hb⟩ := SourceFrozenCancellation.parameter_envelope K' (Module.finrank ℝ V+0) α β hα
  refine ⟨∫ z, B z,integral_nonneg hBp,?_⟩
  intro A hA hAr r hr f x
  rw [row_normalized K A (fun y => hα.trans_le (hAr y).1) r hr,pow_zero,one_smul]
  have hi : Integrable (fun z => f (x-r • z) •
      atTime K' (Module.finrank ℝ V+0) (A (x-r • z)) z) := by
    apply (hB.const_mul ‖f‖).mono'
    · exact ((f.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))).smul
        (SourceFrozenCancellation.continuous_variable K' _ (fun z => A (x-r • z))
          (hA.comp (continuous_const.sub (continuous_const.smul continuous_id)))
          (fun z => hα.trans_le (hAr _).1))).aestronglyMeasurable
    · filter_upwards with z
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)
  change ‖∫ z, f (x-r • z) • atTime K' _ (A (x-r • z)) z‖ ≤ _
  calc
    _ ≤ ∫ z, ‖f (x-r • z) • atTime K' _ (A (x-r • z)) z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖f‖*B z := by
      apply integral_mono hi.norm (hB.const_mul ‖f‖)
      intro z
      dsimp only
      rw [norm_smul]
      exact mul_le_mul (f.norm_coe_le_norm _) (hb _ (hAr _) z) (norm_nonneg _) (norm_nonneg _)
    _ = _ := integral_const_mul ..

lemma continuous_row (K : SchwartzMap V ℂ) (A : V → ℝ) (hA : Continuous A)
    (α β : ℝ) (hα : 0 < α) (hAr : ∀ y, A y ∈ Icc α β)
    (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (j : ℕ) : Continuous (row K A r f j) := by
  rw [row_eq K A hA α β hα hAr r hr]
  have hd : ContDiff ℝ (j+1) (value K A r f) :=
    by simpa only [Nat.cast_add,Nat.cast_one] using
      (contDiff_infty.mp (contDiff_value K A hA α β hα hAr r hr f) (j+1))
  exact hd.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_succ j)

lemma hasFDerivAt_row (K : SchwartzMap V ℂ) (A : V → ℝ) (hA : Continuous A)
    (α β : ℝ) (hα : 0 < α) (hAr : ∀ y, A y ∈ Icc α β)
    (r : ℝ) (hr : 0 < r) (f : V →ᵇ ℂ) (j : ℕ) (x : V) :
    HasFDerivAt (row K A r f j)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ)
        (row K A r f (j+1) x)) x := by
  rw [row_eq K A hA α β hα hAr r hr f j,
    row_eq K A hA α β hα hAr r hr f (j+1)]
  have hd : ContDiff ℝ (j+1) (value K A r f) :=
    by simpa only [Nat.cast_add,Nat.cast_one] using
      (contDiff_infty.mp (contDiff_value K A hA α β hα hAr r hr f) (j+1))
  have hd' := (hd.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast Nat.lt_succ_self j) x).hasFDerivAt
  simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using hd'

lemma stronglyMeasurable_time_row (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (j : ℕ) (t : ℝ) (x : V) :
    StronglyMeasurable (fun s : ℝ => row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x) := by
  let c : ℝ × V → ℝ := fun p => (((t-p.1)^(1/4 : ℝ))*(A p.1 p.2)^(1/4 : ℝ))⁻¹
  have hc : Measurable c := by
    dsimp [c]
    exact (((measurable_const.sub measurable_fst).pow_const _).mul
      (hA.measurable.pow_const _)).inv
  have he : Continuous (fun p : ℝ × V => f p.1 p.2) := by fun_prop
  have hg := (SchwartzDerivatives.iterated K j).continuous
  have hm : StronglyMeasurable (fun p : ℝ × V => f p.1 p.2 •
      (c p ^ (Module.finrank ℝ V+j) • SchwartzDerivatives.iterated K j (c p • (x-p.2)))) :=
    he.stronglyMeasurable.smul ((hc.pow_const _).stronglyMeasurable.smul
      (hg.comp_stronglyMeasurable (hc.stronglyMeasurable.smul
        (continuous_const.sub continuous_snd).stronglyMeasurable)))
  exact hm.integral_prod_right'

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
lemma radius_weight (q : ℝ) (hq : 0 < q) (j : ℕ) (p : ℝ) :
    ((q^(1/4 : ℝ))⁻¹)^j*(q^(1/4 : ℝ))^p = q^((p-j)/4) := by
  rw [inv_pow,← Real.rpow_natCast,← Real.rpow_mul hq.le,← Real.rpow_neg hq.le,
    ← Real.rpow_mul hq.le,← Real.rpow_add hq]
  congr 1
  ring
end ExistsRowZeroBound

section IntegrableOnLagRpow
open SchwartzTimeScale
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integrableOn_lag_rpow (t p : ℝ) (ht : 0 ≤ t) (hp : -1 < p) :
    IntegrableOn (fun s : ℝ => (t-s)^p) (Ioo 0 t) := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) hp).comp_sub_left t
  simp only [sub_zero,sub_self] at hi
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).mp hi.symm

lemma exists_integrable_row_bound (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (α β : ℝ) (hα : 0 < α)
    (hAr : ∀ s y, A s y ∈ Icc α β) (L : ℝ) (hL : 0 ≤ L)
    (hAL : ∀ s x y, ‖A s x-A s y‖ ≤ L*‖x-y‖)
    (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (γ H t : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H)
    (hhold : ∀ s ∈ Ioo 0 t, ∀ x y : V, ‖f s x-f s y‖ ≤ H*‖x-y‖^γ)
    (j : ℕ) (hj4 : j ≤ 4) :
    ∃ b : ℝ → ℝ, IntegrableOn b (Ioo 0 t) ∧
      ∀ s ∈ Ioo 0 t, ∀ x : V,
        ‖row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x‖ ≤ b s := by
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hf.continuousOn
  have hAs (s : ℝ) : Continuous (A s) := hA.comp (continuous_const.prodMk continuous_id)
  by_cases hj : j = 0
  · subst j
    obtain ⟨C,hC,hb⟩ := exists_row_zero_bound K α β hα
    refine ⟨fun _ => M*C,integrableOn_const (hs := measure_Ioo_lt_top.ne),?_⟩
    intro s hs x
    exact (hb (A s) (hAs s) (hAr s) _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) x).trans
      (mul_le_mul_of_nonneg_right (hM s ⟨hs.1.le,hs.2.le⟩) hC)
  · obtain ⟨C,D,hC,hD,hb⟩ := exists_row_holder_bound K j (Nat.pos_of_ne_zero hj) α β hα γ hγ.le hγ1
    have hp : -1 < (γ-j)/4 := by
      have : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
      linarith
    have hp' : -1 < ((1 : ℝ)-j)/4 := by
      have : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
      linarith
    refine ⟨fun s => H*C*(t-s)^((γ-j)/4)+M*L*D*(t-s)^(((1 : ℝ)-j)/4),
      ((integrableOn_lag_rpow t _ ht hp).const_mul _).add
        ((integrableOn_lag_rpow t _ ht hp').const_mul _),?_⟩
    intro s hs x
    have hq : 0 < t-s := sub_pos.mpr hs.2
    have hr : 0 < (t-s)^(1/4 : ℝ) := Real.rpow_pos_of_pos hq _
    have he := hb (A s) (hAs s) (hAr s) L hL (hAL s) (f s) H hH
      (hhold s hs) _ hr x
    have heq : (((t-s)^(1/4 : ℝ))⁻¹)^j *
        (H*((t-s)^(1/4 : ℝ))^γ*C+‖f s‖*L*((t-s)^(1/4 : ℝ))*D) =
        H*C*(t-s)^((γ-j)/4)+‖f s‖*L*D*(t-s)^(((1 : ℝ)-j)/4) := by
      rw [mul_add]
      have h1 := radius_weight (t-s) hq j γ
      have h2 := radius_weight (t-s) hq j 1
      rw [Real.rpow_one] at h2
      calc
        _ = H*C*((((t-s)^(1/4 : ℝ))⁻¹)^j*((t-s)^(1/4 : ℝ))^γ) +
            ‖f s‖*L*D*((((t-s)^(1/4 : ℝ))⁻¹)^j*(t-s)^(1/4 : ℝ)) := by ring
        _ = _ := by rw [h1,h2]
    rw [heq] at he
    apply he.trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (hM s ⟨hs.1.le,hs.2.le⟩) hL) hD) (Real.rpow_nonneg hq.le _))

def integralRow (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (f : ℝ → (V →ᵇ ℂ)) (t : ℝ) (j : ℕ) (x : V) : V [×j]→L[ℝ] ℂ :=
  ∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x

variable (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (α β : ℝ) (hα : 0 < α)
    (hAr : ∀ s y, A s y ∈ Icc α β) (L : ℝ) (hL : 0 ≤ L)
    (hAL : ∀ s x y, ‖A s x-A s y‖ ≤ L*‖x-y‖)
    (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (γ H t : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H)
    (hhold : ∀ s ∈ Ioo 0 t, ∀ x y : V, ‖f s x-f s y‖ ≤ H*‖x-y‖^γ)
include hA hα hAr hf hAL hL hH ht hγ hγ1 hhold

lemma integrableOn_row (j : ℕ) (hj4 : j ≤ 4) (x : V) :
    IntegrableOn (fun s => row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x) (Ioo 0 t) := by
  obtain ⟨b,hi,hb⟩ := exists_integrable_row_bound K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j hj4
  exact hi.mono' (stronglyMeasurable_time_row K A hA f hf j t x).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs; exact hb s hs x)

lemma continuous_integralRow (j : ℕ) (hj4 : j ≤ 4) :
    Continuous (integralRow K A f t j) := by
  obtain ⟨b,hbi,hb⟩ := exists_integrable_row_bound K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j hj4
  apply continuous_of_dominated (bound := b)
  · intro x
    exact (stronglyMeasurable_time_row K A hA f hf j t x).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hb s hs x
  · exact hbi
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact continuous_row K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
      _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) j

lemma hasFDerivAt_integralRow (j : ℕ) (hj4 : j+1 ≤ 4) (x : V) :
    HasFDerivAt (integralRow K A f t j)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ)
        (integralRow K A f t (j+1) x)) x := by
  let C := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  let : ContinuousENorm (V →L[ℝ] V [×j]→L[ℝ] ℂ) :=
    @SeminormedAddGroup.toContinuousENorm (V →L[ℝ] V [×j]→L[ℝ] ℂ) inferInstance
  have hi := integrableOn_row K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold (j+1) hj4 x
  have hcomm := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
    (E := V [×(j+1)]→L[ℝ] ℂ) (Fₗ := V →L[ℝ] V [×j]→L[ℝ] ℂ) C hi
  change HasFDerivAt (fun x => ∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x)
    (C (∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) x)) x
  rw [← hcomm]
  obtain ⟨b,hbi,hb⟩ := exists_integrable_row_bound K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold (j+1) hj4
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun x s => C (row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) x)) (bound := b) (univ_mem : univ ∈ 𝓝 x)
  · exact Eventually.of_forall fun z => (stronglyMeasurable_time_row K A hA f hf j t z).aestronglyMeasurable
  · exact integrableOn_row K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j (by omega) x
  · exact (C.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_time_row K A hA f hf (j+1) t x)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    change ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ)
      (row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) z)‖ ≤ b s
    rw [LinearIsometryEquiv.norm_map]
    exact hb s hs z
  · exact hbi
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    exact hasFDerivAt_row K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
      _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) j z

lemma contDiff_integralRow (j n : ℕ) (hjn : j+n ≤ 4) :
    ContDiff ℝ n (integralRow K A f t j) := by
  induction n generalizing j with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_integralRow K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j (by omega)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
    let C : (V [×(j+1)]→L[ℝ] ℂ) →L[ℝ] (V →L[ℝ] V [×j]→L[ℝ] ℂ) := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    refine ⟨fun x => C (integralRow K A f t (j+1) x), ?_, ?_⟩
    · exact contDiff_const.clm_apply (ih (j+1) (by omega))
    · intro x
      exact hasFDerivAt_integralRow K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j (by omega) x

end IntegrableOnLagRpow
section Duhamel
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def duhamel (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (f : ℝ → (V →ᵇ ℂ)) (t : ℝ) (x : V) : ℂ :=
  ∫ s in Ioo 0 t, value K (A s) ((t-s)^(1/4 : ℝ)) (f s) x

variable (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (α β : ℝ) (hα : 0 < α)
    (hAr : ∀ s y, A s y ∈ Icc α β) (L : ℝ) (hL : 0 ≤ L)
    (hAL : ∀ s x y, ‖A s x-A s y‖ ≤ L*‖x-y‖)
    (f : ℝ → (V →ᵇ ℂ)) (hf : Continuous f)
    (γ H t : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hH : 0 ≤ H)
    (hhold : ∀ s ∈ Ioo 0 t, ∀ x y : V, ‖f s x-f s y‖ ≤ H*‖x-y‖^γ)
include hA hα hAr hf hAL hL hH ht hγ hγ1 hhold

lemma duhamel_eq_integralRow_zero (x : V) : duhamel K A f t x =
    (continuousMultilinearCurryFin0 ℝ V ℂ) (integralRow K A f t 0 x) := by
  let C := (continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have hc := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
    (E := V [×0]→L[ℝ] ℂ) (Fₗ := ℂ) C
    (integrableOn_row K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold 0 (by omega) x)
  change (∫ s in Ioo 0 t, value K (A s) ((t-s)^(1/4 : ℝ)) (f s) x) =
    C (∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) 0 x)
  rw [← hc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [row_eq K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
    _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _),iteratedFDeriv_zero_eq_comp]
  exact (LinearIsometryEquiv.apply_symm_apply _ _).symm

lemma contDiff_duhamel : ContDiff ℝ 4 (duhamel K A f t) := by
  have he : duhamel K A f t = fun x => (continuousMultilinearCurryFin0 ℝ V ℂ)
      (integralRow K A f t 0 x) :=
    funext (duhamel_eq_integralRow_zero K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold)
  rw [he]
  let C : (V [×0]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    (continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  change ContDiff ℝ 4 (fun x => C (integralRow K A f t 0 x))
  exact contDiff_const.clm_apply
    (contDiff_integralRow K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold 0 4 (by omega))

lemma iteratedFDeriv_duhamel (j : ℕ) (hj : j ≤ 4) :
    iteratedFDeriv ℝ j (duhamel K A f t) = integralRow K A f t j := by
  induction j with
  | zero =>
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    change (continuousMultilinearCurryFin0 ℝ V ℂ).symm (duhamel K A f t x) = _
    rw [duhamel_eq_integralRow_zero K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold,
      LinearIsometryEquiv.symm_apply_apply]
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left,ih (by omega)]
    funext x
    dsimp only [Function.comp_apply]
    rw [(hasFDerivAt_integralRow K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j hj x).fderiv]
    exact LinearIsometryEquiv.symm_apply_apply _ _

lemma exists_norm_iteratedFDeriv_duhamel_bound (j : ℕ) (hj : j ≤ 4) :
    ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j (duhamel K A f t) x‖ ≤ C := by
  obtain ⟨b,hi,hb⟩ := exists_integrable_row_bound K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j hj
  refine ⟨∫ s in Ioo 0 t, b s,fun x => ?_⟩
  rw [iteratedFDeriv_duhamel K A hA α β hα hAr L hL hAL f hf γ H t ht hγ hγ1 hH hhold j hj]
  apply norm_integral_le_of_norm_le hi
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact hb s hs x
end Duhamel

open ScaledSchwartzConvolution SchwartzTimeScale
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma stronglyMeasurable_time_row_of_stronglyMeasurable
    (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (f : ℝ → (V →ᵇ ℂ))
    (hf : StronglyMeasurable f) (j : ℕ) (t : ℝ) (x : V) :
    StronglyMeasurable (fun s : ℝ => row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x) := by
  let c : ℝ × V → ℝ := fun p => (((t-p.1)^(1/4 : ℝ))*(A p.1 p.2)^(1/4 : ℝ))⁻¹
  have hc : Measurable c := by
    dsimp [c]
    exact (((measurable_const.sub measurable_fst).pow_const _).mul
      (hA.measurable.pow_const _)).inv
  have he' : Continuous (fun p : (V →ᵇ ℂ) × V => p.1 p.2) := by fun_prop
  have he : StronglyMeasurable (fun p : ℝ × V => f p.1 p.2) :=
    he'.comp_stronglyMeasurable
      ((hf.comp_measurable measurable_fst).prodMk continuous_snd.stronglyMeasurable)
  have hg := (SchwartzDerivatives.iterated K j).continuous
  have hm : StronglyMeasurable (fun p : ℝ × V => f p.1 p.2 •
      (c p ^ (Module.finrank ℝ V+j) • SchwartzDerivatives.iterated K j (c p • (x-p.2)))) :=
    he.smul ((hc.pow_const _).stronglyMeasurable.smul
      (hg.comp_stronglyMeasurable (hc.stronglyMeasurable.smul
        (continuous_const.sub continuous_snd).stronglyMeasurable)))
  exact hm.integral_prod_right'

lemma exists_integrable_row_bound_weighted (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (α β : ℝ) (hα : 0 < α)
    (hAr : ∀ s y, A s y ∈ Icc α β) (L : ℝ) (hL : 0 ≤ L)
    (hAL : ∀ s x y, ‖A s x-A s y‖ ≤ L*‖x-y‖)
    (f : ℝ → (V →ᵇ ℂ)) (σ τ M H γ t : ℝ)
    (hσ : σ < 1) (hτ : τ < 1) (_hM : 0 ≤ M) (hH : 0 ≤ H)
    (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hfn : ∀ s ∈ Ioo 0 t, ‖f s‖ ≤ M*s^(-σ))
    (hhold : ∀ s ∈ Ioo 0 t, ∀ x y : V, ‖f s x-f s y‖ ≤ (H*s^(-τ))*‖x-y‖^γ)
    (j : ℕ) (hj4 : j ≤ 4) :
    ∃ b : ℝ → ℝ, IntegrableOn b (Ioo 0 t) ∧
      ∀ s ∈ Ioo 0 t, ∀ x : V,
        ‖row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x‖ ≤ b s := by
  have hAs (s : ℝ) : Continuous (A s) := hA.comp (continuous_const.prodMk continuous_id)
  by_cases hj : j = 0
  · subst j
    obtain ⟨C,hC,hb⟩ := exists_row_zero_bound K α β hα
    have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (BetaWeights.intervalIntegrable σ 0 hσ (by norm_num) t ht)
    refine ⟨fun s => (M*C)*BetaWeights.density σ 0 t s,hi.const_mul _,?_⟩
    intro s hs x
    have hh := (hb (A s) (hAs s) (hAr s) ((t-s)^(1/4 : ℝ)) (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) x).trans
      (mul_le_mul_of_nonneg_right (hfn s hs) hC)
    simpa only [BetaWeights.density,neg_zero,Real.rpow_zero,mul_one,mul_assoc,mul_comm,mul_left_comm] using hh
  · obtain ⟨C,D,hC,hD,hb⟩ := exists_row_holder_bound K j (Nat.pos_of_ne_zero hj) α β hα γ hγ.le hγ1
    have hp : ((j : ℝ)-γ)/4 < 1 := by
      have : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
      linarith
    have hp' : ((j : ℝ)-1)/4 < 1 := by
      have : (j : ℝ) ≤ 4 := by exact_mod_cast hj4
      linarith
    have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (BetaWeights.intervalIntegrable τ ((j-γ)/4) hτ hp t ht)
    have hi' := (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
      (BetaWeights.intervalIntegrable σ ((j-1)/4) hσ hp' t ht)
    refine ⟨fun s => (H*C)*BetaWeights.density τ ((j-γ)/4) t s+
        (M*L*D)*BetaWeights.density σ ((j-1)/4) t s,
      (hi.const_mul _).add (hi'.const_mul _),?_⟩
    intro s hs x
    have hq : 0 < t-s := sub_pos.mpr hs.2
    have hr : 0 < (t-s)^(1/4 : ℝ) := Real.rpow_pos_of_pos hq _
    have hsτ : 0 ≤ H*s^(-τ) := mul_nonneg hH (Real.rpow_nonneg hs.1.le _)
    have he := hb (A s) (hAs s) (hAr s) L hL (hAL s) (f s) (H*s^(-τ)) hsτ
      (hhold s hs) _ hr x
    have heq : (((t-s)^(1/4 : ℝ))⁻¹)^j *
        ((H*s^(-τ))*((t-s)^(1/4 : ℝ))^γ*C+‖f s‖*L*((t-s)^(1/4 : ℝ))*D) =
        (H*s^(-τ))*C*(t-s)^((γ-j)/4)+‖f s‖*L*D*(t-s)^(((1 : ℝ)-j)/4) := by
      rw [mul_add]
      have h1 := radius_weight (t-s) hq j γ
      have h2 := radius_weight (t-s) hq j 1
      rw [Real.rpow_one] at h2
      calc
        _ = (H*s^(-τ))*C*((((t-s)^(1/4 : ℝ))⁻¹)^j*((t-s)^(1/4 : ℝ))^γ) +
            ‖f s‖*L*D*((((t-s)^(1/4 : ℝ))⁻¹)^j*(t-s)^(1/4 : ℝ)) := by ring
        _ = _ := by rw [h1,h2]
    rw [heq] at he
    apply he.trans
    have hn := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hfn s hs) hL) hD)
      (Real.rpow_nonneg hq.le (((1 : ℝ)-j)/4))
    calc
      _ ≤ (H*s^(-τ))*C*(t-s)^((γ-j)/4)+(M*s^(-σ))*L*D*(t-s)^(((1 : ℝ)-j)/4) :=
        add_le_add le_rfl hn
      _ = _ := by
        unfold BetaWeights.density
        rw [show -((↑j-γ)/4) = (γ-j)/4 by ring,show -(((j:ℝ)-1)/4) = ((1:ℝ)-j)/4 by ring]
        ring
end SourceFrozenRows

namespace WeightedSourceFrozenRows
open SourceFrozenRows
open scoped BoundedContinuousFunction ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (K : SchwartzMap V ℂ) (A : ℝ → V → ℝ)
    (hA : Continuous (Function.uncurry A)) (α β : ℝ) (hα : 0 < α)
    (hAr : ∀ s y, A s y ∈ Icc α β) (L : ℝ) (hL : 0 ≤ L)
    (hAL : ∀ s x y, ‖A s x-A s y‖ ≤ L*‖x-y‖)
    (f : ℝ → (V →ᵇ ℂ)) (hf : StronglyMeasurable f) (σ τ M H γ t : ℝ)
    (hσ : σ < 1) (hτ : τ < 1) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (ht : 0 < t) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hfn : ∀ s ∈ Ioo 0 t, ‖f s‖ ≤ M*s^(-σ))
    (hhold : ∀ s ∈ Ioo 0 t, ∀ x y : V, ‖f s x-f s y‖ ≤ (H*s^(-τ))*‖x-y‖^γ)
include hA hα hAr hf hAL hL hH ht hγ hγ1 hhold hσ hτ hM hfn

lemma integrableOn_row (j : ℕ) (hj4 : j ≤ 4) (x : V) :
    IntegrableOn (fun s => row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x) (Ioo 0 t) := by
  obtain ⟨b,hi,hb⟩ := SourceFrozenRows.exists_integrable_row_bound_weighted K A hA α β hα hAr L hL hAL f σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j hj4
  exact hi.mono' (stronglyMeasurable_time_row_of_stronglyMeasurable K A hA f hf j t x).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs; exact hb s hs x)

lemma continuous_integralRow (j : ℕ) (hj4 : j ≤ 4) :
    Continuous (integralRow K A f t j) := by
  obtain ⟨b,hbi,hb⟩ := SourceFrozenRows.exists_integrable_row_bound_weighted K A hA α β hα hAr L hL hAL f σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j hj4
  apply continuous_of_dominated (bound := b)
  · intro x
    exact (stronglyMeasurable_time_row_of_stronglyMeasurable K A hA f hf j t x).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hb s hs x
  · exact hbi
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact continuous_row K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
      _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) j

lemma hasFDerivAt_integralRow (j : ℕ) (hj4 : j+1 ≤ 4) (x : V) :
    HasFDerivAt (integralRow K A f t j)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ)
        (integralRow K A f t (j+1) x)) x := by
  let C := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  let : ContinuousENorm (V →L[ℝ] V [×j]→L[ℝ] ℂ) :=
    @SeminormedAddGroup.toContinuousENorm (V →L[ℝ] V [×j]→L[ℝ] ℂ) inferInstance
  have hi := integrableOn_row K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold (j+1) hj4 x
  have hcomm := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
    (E := V [×(j+1)]→L[ℝ] ℂ) (Fₗ := V →L[ℝ] V [×j]→L[ℝ] ℂ) C hi
  change HasFDerivAt (fun x => ∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) j x)
    (C (∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) x)) x
  rw [← hcomm]
  obtain ⟨b,hbi,hb⟩ := SourceFrozenRows.exists_integrable_row_bound_weighted K A hA α β hα hAr L hL hAL f σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold (j+1) hj4
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun x s => C (row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) x)) (bound := b) (univ_mem : univ ∈ 𝓝 x)
  · exact Eventually.of_forall fun z => (stronglyMeasurable_time_row_of_stronglyMeasurable K A hA f hf j t z).aestronglyMeasurable
  · exact integrableOn_row K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j (by omega) x
  · exact (C.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_time_row_of_stronglyMeasurable K A hA f hf (j+1) t x)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    change ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ)
      (row K (A s) ((t-s)^(1/4 : ℝ)) (f s) (j+1) z)‖ ≤ b s
    rw [LinearIsometryEquiv.norm_map]
    exact hb s hs z
  · exact hbi
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs z _
    exact hasFDerivAt_row K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
      _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _) (f s) j z

lemma contDiff_integralRow (j n : ℕ) (hjn : j+n ≤ 4) :
    ContDiff ℝ n (integralRow K A f t j) := by
  induction n generalizing j with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_integralRow K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j (by omega)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
    let C : (V [×(j+1)]→L[ℝ] ℂ) →L[ℝ] (V →L[ℝ] V [×j]→L[ℝ] ℂ) := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => V) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
    refine ⟨fun x => C (integralRow K A f t (j+1) x), ?_, ?_⟩
    · exact contDiff_const.clm_apply (ih (j+1) (by omega))
    · intro x
      exact hasFDerivAt_integralRow K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j (by omega) x

lemma duhamel_eq_integralRow_zero (x : V) : duhamel K A f t x =
    (continuousMultilinearCurryFin0 ℝ V ℂ) (integralRow K A f t 0 x) := by
  let C := (continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have hc := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
    (E := V [×0]→L[ℝ] ℂ) (Fₗ := ℂ) C
    (integrableOn_row K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold 0 (by omega) x)
  change (∫ s in Ioo 0 t, value K (A s) ((t-s)^(1/4 : ℝ)) (f s) x) =
    C (∫ s in Ioo 0 t, row K (A s) ((t-s)^(1/4 : ℝ)) (f s) 0 x)
  rw [← hc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [row_eq K (A s) (hA.comp (continuous_const.prodMk continuous_id)) α β hα (hAr s)
    _ (Real.rpow_pos_of_pos (sub_pos.mpr hs.2) _),iteratedFDeriv_zero_eq_comp]
  exact (LinearIsometryEquiv.apply_symm_apply _ _).symm

lemma contDiff_duhamel : ContDiff ℝ 4 (duhamel K A f t) := by
  have he : duhamel K A f t = fun x => (continuousMultilinearCurryFin0 ℝ V ℂ)
      (integralRow K A f t 0 x) :=
    funext (duhamel_eq_integralRow_zero K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold)
  rw [he]
  let C : (V [×0]→L[ℝ] ℂ) →L[ℝ] ℂ :=
    (continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  change ContDiff ℝ 4 (fun x => C (integralRow K A f t 0 x))
  exact contDiff_const.clm_apply
    (contDiff_integralRow K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold 0 4 (by omega))

lemma iteratedFDeriv_duhamel (j : ℕ) (hj : j ≤ 4) :
    iteratedFDeriv ℝ j (duhamel K A f t) = integralRow K A f t j := by
  induction j with
  | zero =>
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    change (continuousMultilinearCurryFin0 ℝ V ℂ).symm (duhamel K A f t x) = _
    rw [duhamel_eq_integralRow_zero K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold,
      LinearIsometryEquiv.symm_apply_apply]
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left,ih (by omega)]
    funext x
    dsimp only [Function.comp_apply]
    rw [(hasFDerivAt_integralRow K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j hj x).fderiv]
    exact LinearIsometryEquiv.symm_apply_apply _ _

lemma exists_norm_iteratedFDeriv_duhamel_bound (j : ℕ) (hj : j ≤ 4) :
    ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j (duhamel K A f t) x‖ ≤ C := by
  obtain ⟨b,hi,hb⟩ := SourceFrozenRows.exists_integrable_row_bound_weighted K A hA α β hα hAr L hL hAL f σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j hj
  refine ⟨∫ s in Ioo 0 t, b s,fun x => ?_⟩
  rw [iteratedFDeriv_duhamel K A hA α β hα hAr L hL hAL f hf σ τ M H γ t hσ hτ hM hH ht hγ hγ1 hfn hhold j hj]
  apply norm_integral_le_of_norm_le hi
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact hb s hs x
end WeightedSourceFrozenRows

end

end OAI
