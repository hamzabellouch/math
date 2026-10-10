import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma differentiable_of_exp_eq {g f : ℂ → ℂ} (hg : Continuous g)
    (hf : Differentiable ℂ f) (he : ∀ z, Complex.exp (g z) = f z) :
    Differentiable ℂ g := by
  intro z
  have hn : f z ≠ 0 := by rw [← he]; exact Complex.exp_ne_zero _
  have hd : DifferentiableAt ℂ (fun w => Complex.log (f w/f z)+g z) z := by
    apply DifferentiableAt.add_const
    apply DifferentiableAt.clog ((hf z).div_const _)
    simp only [div_self hn]
    exact Complex.one_mem_slitPlane
  apply hd.congr_of_eventuallyEq
  have hc : ContinuousAt (fun w => (g w-g z).im) z := by fun_prop
  have hsmall : ∀ᶠ w in 𝓝 z, (g w-g z).im ∈ Set.Ioo (-Real.pi) Real.pi :=
    hc (IsOpen.mem_nhds isOpen_Ioo (by simp [Real.pi_pos]))
  filter_upwards [hsmall] with w hw
  rw [← he w,← he z,← Complex.exp_sub,Complex.log_exp hw.1 hw.2.le]
  exact (sub_add_cancel _ _).symm

lemma exists_entire_log {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hn : ∀ z, f z ≠ 0) (h0 : f 0 = 1) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 = 0 ∧ ∀ z, Complex.exp (g z) = f z := by
  have : ContractibleSpace (Set.univ : Set ℂ) := convex_univ.contractibleSpace Set.univ_nonempty
  obtain ⟨g,hgc,hge⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (U := Set.univ) (show SimplyConnectedSpace (Set.univ : Set ℂ) from inferInstance) isOpen_univ hf.continuous.continuousOn
    (by simpa only [Set.mem_image,Set.mem_univ,true_and,not_exists] using hn)
  have hg : Continuous g := continuousOn_univ.mp hgc
  have he : ∀ z, Complex.exp (g z) = f z := fun z => hge (Set.mem_univ z)
  refine ⟨fun z => g z-g 0,(differentiable_of_exp_eq hg hf he).sub_const _,by simp,?_⟩
  intro z
  rw [Complex.exp_sub,he,he,h0,div_one]

lemma entire_norm_quadratic_bound {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h0 : g 0 = 0) {C : ℝ} (hC : 0 < C)
    (hb : ∀ z, (g z).re ≤ C*(1+‖z‖^2)) (z : ℂ) :
    ‖g z‖ ≤ 12*C*(1+‖z‖^2) := by
  let R := 2*‖z‖+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : z ∈ Metric.ball 0 R := by
    rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg z]
  have hM : 0 < C*(1+R^2) := mul_pos hC (by positivity)
  have hm : Set.MapsTo g (Metric.ball 0 R) {w | w.re ≤ C*(1+R^2)} := by
    intro w hw
    exact (hb w).trans (mul_le_mul_of_nonneg_left
      (by nlinarith [mem_ball_zero_iff.mp hw,norm_nonneg w]) hC.le)
  have h := Complex.borelCaratheodory_zero hM hg.differentiableOn hm hR hz h0
  have hden : 0 < R-‖z‖ := by dsimp [R]; linarith [norm_nonneg z]
  calc ‖g z‖ ≤ 2*(C*(1+R^2))*‖z‖/(R-‖z‖) := h
    _ ≤ 2*(C*(1+R^2)) := by
      apply (div_le_iff₀ hden).2
      exact mul_le_mul_of_nonneg_left (by dsimp [R]; linarith) (by positivity)
    _ ≤ 12*C*(1+‖z‖^2) := by
      dsimp [R]
      nlinarith [mul_nonneg hC.le (sq_nonneg (‖z‖-1))]

lemma entire_third_deriv_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ z, ‖g z‖ ≤ K*(1+‖z‖^2)) (c : ℂ) :
    iteratedDeriv 3 g c = 0 := by
  have hh : ∀ᶠ R : ℝ in atTop, ‖iteratedDeriv 3 g c‖ ≤ 30*K/R := by
    filter_upwards [eventually_ge_atTop (max 1 ‖c‖)] with R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    have hRc : ‖c‖ ≤ R := (le_max_right _ _).trans hR
    have hRp : 0 < R := by linarith
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      3 hRp hg.diffContOnCl (C := 5*K*R^2) (c := c) (fun z hz => by
        have hnorm : ‖z‖ ≤ 2*R := by
          calc ‖z‖ ≤ ‖z-c‖+‖c‖ := norm_le_norm_sub_add _ _
            _ ≤ 2*R := by rw [mem_sphere_iff_norm.mp hz]; linarith
        have hs : 1+‖z‖^2 ≤ 5*R^2 := by nlinarith [norm_nonneg z]
        calc ‖g z‖ ≤ K*(1+‖z‖^2) := hb z
          _ ≤ K*(5*R^2) := mul_le_mul_of_nonneg_left hs hK
          _ = 5*K*R^2 := by ring)
    calc ‖iteratedDeriv 3 g c‖ ≤ ((3:ℕ).factorial:ℝ)*(5*K*R^2)/R^3 := hc
      _ = 30*K/R := by norm_num; field_simp; ring
  have ht : Tendsto (fun R : ℝ => 30*K/R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using (tendsto_const_nhds (x := (30*K:ℝ))).mul (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht hh) (norm_nonneg _))

theorem entire_log_quadratic {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h0 : g 0 = 0) {C : ℝ} (hC : 0 < C)
    (hb : ∀ z, (g z).re ≤ C*(1+‖z‖^2)) :
    ∀ z, g z = deriv g 0*z + deriv (deriv g) 0*z^2/2 := by
  have h3 : ∀ z, deriv (deriv (deriv g)) z = 0 := by
    intro z
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      entire_third_deriv_zero hg (by positivity : 0 ≤ 12*C)
        (entire_norm_quadratic_bound hg h0 hC hb) z
  have h2 : ∀ z, deriv (deriv g) z = deriv (deriv g) 0 :=
    fun z => is_const_of_deriv_eq_zero hg.deriv.deriv h3 z 0
  have hlin (z : ℂ) : HasDerivAt
      (fun w => deriv g w-(deriv g 0+deriv (deriv g) 0*w)) 0 z := by
    have h := (hg.deriv z).hasDerivAt.sub ((hasDerivAt_const z (deriv g 0)).add
      ((hasDerivAt_id z).const_mul (deriv (deriv g) 0)))
    convert! h using 1
    simp only [h2,zero_add,mul_one,sub_self]
  have h1 (z : ℂ) : deriv g z = deriv g 0+deriv (deriv g) 0*z := by
    have h := is_const_of_deriv_eq_zero (fun z => (hlin z).differentiableAt)
      (fun z => (hlin z).deriv) z 0
    simpa only [mul_zero,add_zero,sub_self,sub_eq_zero] using h
  have hpoly (z : ℂ) : HasDerivAt
      (fun w => g w-(deriv g 0*w+deriv (deriv g) 0*w^2/2)) 0 z := by
    have h := (hg z).hasDerivAt.sub (((hasDerivAt_id z).const_mul (deriv g 0)).add
      ((((hasDerivAt_id z).pow 2).const_mul (deriv (deriv g) 0)).div_const 2))
    convert! h using 1
    simp only [id_eq]
    rw [h1]; ring
  intro z
  have h := is_const_of_deriv_eq_zero (fun z => (hpoly z).differentiableAt)
    (fun z => (hpoly z).deriv) z 0
  simpa only [h0,zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_div,add_zero,sub_zero,sub_eq_zero]
    using h

theorem entire_gaussian_factor {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : f 0 = 1) (A : ℂ)
    (hp : ∀ z, f z*f (-z) = Complex.exp (A*z^2)) {C : ℝ} (hC : 0 < C)
    (hb : ∀ z, ‖f z‖ ≤ Real.exp (C*(1+‖z‖^2))) :
    ∀ z, f z = Complex.exp (deriv f 0*z+A*z^2/2) := by
  have hn (z) : f z ≠ 0 := by
    intro hz
    have h := hp z
    rw [hz,zero_mul] at h
    exact Complex.exp_ne_zero _ h.symm
  obtain ⟨g,hg,hg0,he⟩ := exists_entire_log hf hn h0
  have hgb (z) : (g z).re ≤ C*(1+‖z‖^2) := by
    have h := hb z
    rw [← he z,Complex.norm_exp] at h
    exact Real.exp_le_exp.mp h
  have hpoly := entire_log_quadratic hg hg0 hC hgb
  let b := deriv (deriv g) 0
  have hprod (z : ℂ) : Complex.exp (b*z^2) = Complex.exp (A*z^2) := by
    have h := hp z
    rw [← he z,← he (-z),← Complex.exp_add,hpoly z,hpoly (-z)] at h
    convert h using 1
    congr 1
    dsimp [b]
    ring
  have h1 : Complex.exp b = Complex.exp A := by simpa using hprod 1
  have hd := congrArg (fun F : ℂ → ℂ => deriv F 1) (funext hprod)
  have hdb : deriv (fun z : ℂ => Complex.exp (b*z^2)) 1 = Complex.exp b*(b*2) := by
    simpa using ((((hasDerivAt_id (1:ℂ)).pow 2).const_mul b).cexp).deriv
  have hdA : deriv (fun z : ℂ => Complex.exp (A*z^2)) 1 = Complex.exp A*(A*2) := by
    simpa using ((((hasDerivAt_id (1:ℂ)).pow 2).const_mul A).cexp).deriv
  rw [hdb,hdA,h1] at hd
  have hbA : b = A := mul_right_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    (mul_left_cancel₀ (Complex.exp_ne_zero A) hd)
  have hdf : deriv f 0 = deriv g 0 := by
    have h := ((hg 0).hasDerivAt.cexp).deriv
    have hef : (fun z => Complex.exp (g z)) = f := funext he
    rw [hef,hg0,Complex.exp_zero,one_mul] at h
    exact h
  intro z
  rw [← he z,hpoly z,← hdf]
  change Complex.exp (deriv f 0*z+b*z^2/2) = _
  rw [hbA]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
