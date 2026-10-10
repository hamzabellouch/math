import Mathlib
import OAI.Probability.SKValue.Control.ControlPayoffConvex

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma gradient_bound (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) : |gradient W γ t x|≤1 := by
  simpa only [gradient, Real.norm_eq_abs, NNReal.coe_one] using
    norm_deriv_le_of_lipschitz (x₀ := x) (phi_lipschitz W γ ht)

lemma OrderParameter.tail_cutoff_eq (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) : (∫ s in t..1, γ.cutoff s) = ∫ s in t..1, γ.coeff s := by
  apply intervalIntegral.integral_congr_Ioo_of_le ht.2
  intro s hs
  have hs' : s∈Ico (0 : ℝ) 1 := ⟨ht.1.trans hs.1.le,hs.2⟩
  exact Set.indicator_of_mem hs' γ.coeff

noncomputable def terminalError (γ : OrderParameter) (t : ℝ) : ℝ :=
  Real.sqrt (1-t)+(1/2 : ℝ)*(∫ s in t..1, γ.cutoff s)

lemma terminalError_continuous (γ : OrderParameter) : Continuous (terminalError γ) := by
  have hi : Continuous (fun t ↦ ∫ s in t..1, γ.cutoff s) := by
    convert (γ.cutoff_integrable.continuous_primitive 1).neg using 1
    funext t
    simpa only [Pi.neg_apply] using intervalIntegral.integral_symm (μ := volume) (f := γ.cutoff) 1 t
  exact (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).add (continuous_const.mul hi)

@[simp] lemma terminalError_one (γ : OrderParameter) : terminalError γ 1=0 := by
  simp [terminalError]

lemma phi_terminal (W : BrownianSpace) (γ : OrderParameter) (x : ℝ) : phi W γ 1 x=|x| := by
  have h := phi_terminal_bound W γ (show (1 : ℝ)∈Icc (0 : ℝ) 1 by norm_num) x
  simp only [sub_self, Real.sqrt_zero, intervalIntegral.integral_same, mul_zero, add_zero] at h
  linarith

lemma phi_terminal_error_tendsto {ι : Type*} {l : Filter ι}
    (W : BrownianSpace) (γ : OrderParameter) (t x : ι → ℝ)
    (ht : Tendsto t l (𝓝 (1 : ℝ))) (hI : ∀ᶠ i in l, t i∈Icc (0 : ℝ) 1) :
    Tendsto (fun i ↦ phi W γ (t i) (x i)-|x i|) l (𝓝 (0 : ℝ)) := by
  have he : Tendsto (fun i ↦ terminalError γ (t i)) l (𝓝 (0 : ℝ)) := by
    simpa only [terminalError_one, Function.comp_def] using (terminalError_continuous γ).continuousAt.tendsto.comp ht
  apply squeeze_zero' _ _ he
  · filter_upwards [hI] with i hi using (phi_terminal_bound W γ hi (x i)).1
  · filter_upwards [hI] with i hi using (phi_terminal_bound W γ hi (x i)).2

lemma phi_terminal_tendsto {ι : Type*} {l : Filter ι}
    (W : BrownianSpace) (γ : OrderParameter) (t x : ι → ℝ) (x₁ : ℝ)
    (ht : Tendsto t l (𝓝 (1 : ℝ))) (hI : ∀ᶠ i in l, t i∈Icc (0 : ℝ) 1)
    (hx : Tendsto x l (𝓝 x₁)) :
    Tendsto (fun i ↦ phi W γ (t i) (x i)) l (𝓝 |x₁|) := by
  have h := (phi_terminal_error_tendsto W γ t x ht hI).add hx.abs
  simpa only [sub_add_cancel, zero_add] using h

lemma gradient_lower_of_pos (W : BrownianSpace) (γ : OrderParameter) {t x h : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (hh : 0<h) (hx : h≤x)
    (hd : DifferentiableAt ℝ (phi W γ t) x) :
    1-terminalError γ t/h ≤ gradient W γ t x := by
  have hs := (phi_convex W γ ht).slope_le_deriv (mem_univ (x-h)) (mem_univ x) (by linarith) hd
  have hl := phi_lower W γ ht x
  have hu := (phi_terminal_bound W γ ht (x-h)).2
  rw [abs_of_nonneg (hh.le.trans hx)] at hl
  rw [abs_of_nonneg (sub_nonneg.mpr hx)] at hu
  change phi W γ t (x-h)-(x-h)≤terminalError γ t at hu
  change _ ≤ gradient W γ t x at hs
  rw [slope_def_field] at hs
  have hden : x-(x-h)=h := by ring
  rw [hden] at hs
  apply le_trans _ hs
  apply (le_div_iff₀ hh).mpr
  have he : (1-terminalError γ t/h)*h = h-terminalError γ t := by
    field_simp
  rw [he]
  linarith

lemma gradient_upper_of_neg (W : BrownianSpace) (γ : OrderParameter) {t x h : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (hh : 0<h) (hx : x≤-h)
    (hd : DifferentiableAt ℝ (phi W γ t) x) :
    gradient W γ t x ≤ -1+terminalError γ t/h := by
  have hs := (phi_convex W γ ht).deriv_le_slope (mem_univ x) (mem_univ (x+h)) (by linarith) hd
  have hl := phi_lower W γ ht x
  have hu := (phi_terminal_bound W γ ht (x+h)).2
  rw [abs_of_nonpos (by linarith : x≤0)] at hl
  rw [abs_of_nonpos (by linarith : x+h≤0)] at hu
  change phi W γ t (x+h)-(-(x+h))≤terminalError γ t at hu
  change gradient W γ t x≤_ at hs
  rw [slope_def_field] at hs
  have hden : (x+h)-x=h := by ring
  rw [hden] at hs
  apply hs.trans
  apply (div_le_iff₀ hh).mpr
  have he : (-1+terminalError γ t/h)*h = -h+terminalError γ t := by
    field_simp
  rw [he]
  linarith

lemma gradient_terminal_tendsto {ι : Type*} {l : Filter ι}
    (W : BrownianSpace) (γ : OrderParameter) (t x : ι → ℝ) {x₁ : ℝ}
    (ht : Tendsto t l (𝓝 (1 : ℝ))) (hI : ∀ᶠ i in l, t i∈Icc (0 : ℝ) 1)
    (hx : Tendsto x l (𝓝 x₁)) (hne : x₁≠0)
    (hd : ∀ᶠ i in l, DifferentiableAt ℝ (phi W γ (t i)) (x i)) :
    Tendsto (fun i ↦ gradient W γ (t i) (x i)) l (𝓝 (Real.sign x₁)) := by
  have he : Tendsto (fun i ↦ terminalError γ (t i)) l (𝓝 (0 : ℝ)) := by
    simpa only [terminalError_one, Function.comp_def] using (terminalError_continuous γ).continuousAt.tendsto.comp ht
  rcases lt_or_gt_of_ne hne with hn | hp
  · rw [Real.sign_of_neg hn]
    have hhalf : 0 < -x₁/2 := by linarith
    have hx' : ∀ᶠ i in l, x i≤-(-x₁/2) :=
      (hx.eventually (gt_mem_nhds (by linarith : x₁ < -(-x₁/2)))).mono (fun i hi ↦ hi.le)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using tendsto_const_nhds.add (he.div_const (-x₁/2)))
    · filter_upwards [hI] with i hi using (abs_le.mp (gradient_bound W γ hi (x i))).1
    · filter_upwards [hI,hx',hd] with i hi hxi hdi using gradient_upper_of_neg W γ hi hhalf hxi hdi
  · rw [Real.sign_of_pos hp]
    have hhalf : 0<x₁/2 := by linarith
    have hx' : ∀ᶠ i in l, x₁/2≤x i :=
      (hx.eventually (lt_mem_nhds (by linarith : x₁/2<x₁))).mono (fun i hi ↦ hi.le)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using tendsto_const_nhds.sub (he.div_const (x₁/2))) tendsto_const_nhds
    · filter_upwards [hI,hx',hd] with i hi hxi hdi using gradient_lower_of_pos W γ hi hhalf hxi hdi
    · filter_upwards [hI] with i hi using (abs_le.mp (gradient_bound W γ hi (x i))).2

end SKValue

end

end OAI
