import Mathlib
import OAI.Probability.SKSupport.Parabolic.ForwardRegularity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma AffineSmoothFamily.mul_bounded {F G : ℝ → ℝ → ℝ}
    (hF : AffineSmoothFamily F) (hG : BoundedSmoothFamily G)
    (hcG : Continuous (fun p : ℝ × ℝ => G p.1 p.2)) :
    AffineSmoothFamily (fun t x => F t x*G t x) := by
  obtain ⟨A,B,hA,hAc,hB,hBc,rfl⟩ := hF
  refine ⟨fun t x => A t x*G t x,fun t x => B t x*G t x,
    hA.mul hG,hAc.mul hcG,hB.mul hG,hBc.mul hcG,?_⟩
  funext t x
  ring

lemma integral_affine_rate {F R : ℝ → ℝ → ℝ}
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (hR : AffineSmoothFamily R)
    (ht : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (R t x) t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (x : ℝ) :
    (∫ t in a..b, R t x) = F b x-F a x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact (hc.comp (continuous_id.prodMk continuous_const)).continuousOn
  · intro t htt
    exact ht t (ha.trans_lt htt.1) x
  · exact hR.intervalIntegrable x a b

lemma integral_affine_rate_derivative {F R : ℝ → ℝ → ℝ}
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (hR : AffineSmoothFamily R)
    (hs : ∀ t, ContDiff ℝ ∞ (F t))
    (ht : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (R t x) t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) (x : ℝ) :
    (∫ t in a..b, iteratedDeriv n (R t) x) = iteratedDeriv n (F b) x-iteratedDeriv n (F a) x := by
  have he : (fun z => ∫ t in a..b, R t z) = fun z => F b z-F a z :=
    funext (integral_affine_rate hc hR ht ha hab)
  have hh := hR.iteratedDeriv_integral n a b x
  rw [he,iteratedDeriv_fun_sub (n := n)
    ((hs b).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)
    ((hs a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n) |>.contDiffAt)] at hh
  exact hh.symm

lemma hasDerivAt_affine_evolution_jet {F R : ℝ → ℝ → ℝ}
    (hc : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (hR : AffineSmoothFamily R)
    (hs : ∀ t, ContDiff ℝ ∞ (F t))
    (ht : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (R t x) t)
    {t : ℝ} (htp : 0 < t) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun s => iteratedDeriv n (F s) x) (iteratedDeriv n (R t) x) t := by
  have hJ := hR.iteratedDeriv n
  have hcont : Continuous (fun s => iteratedDeriv n (R s) x) :=
    hJ.continuous.comp (continuous_id.prodMk continuous_const)
  have hi := intervalIntegral.integral_hasDerivAt_right (hJ.intervalIntegrable x 0 t)
    (hcont.measurable.stronglyMeasurable.stronglyMeasurableAtFilter) hcont.continuousAt
  apply (hi.const_add (iteratedDeriv n (F 0) x)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds htp] with s hsp
  rw [integral_affine_rate_derivative hc hR hs ht le_rfl hsp.le n x]
  ring

end ZeroTemperatureSK.Heat

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma tiltedMean_add {f g q : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : BoundedSmooth g) (hq : BoundedSmooth q)
    (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    tiltedMean c h f (fun z => g z+q z) x = tiltedMean c h f g x+tiltedMean c h f q x := by
  obtain ⟨G,hG⟩ := hg.bound
  obtain ⟨Q,hQ⟩ := hq.bound
  have hgI := integrable_weight_exp_translate hf hg.smooth.continuous.measurable hG c h x
  have hqI := integrable_weight_exp_translate hf hq.smooth.continuous.measurable hQ c h x
  unfold tiltedMean semigroup
  simp_rw [add_mul]
  rw [integral_add hgI hqI,add_div]

lemma tiltedMean_const_mul (f g : ℝ → ℝ) (c d : ℝ) (h : ℝ≥0) (x : ℝ) :
    tiltedMean c h f (fun z => d*g z) x = d*tiltedMean c h f g x := by
  unfold tiltedMean semigroup
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

lemma tiltedMean_const {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (c d : ℝ) (h : ℝ≥0) (x : ℝ) : tiltedMean c h f (fun _ => d) x = d := by
  unfold tiltedMean
  have he : semigroup h (fun z => d*Real.exp (c*f z)) x =
      d*semigroup h (fun z => Real.exp (c*f z)) x := integral_const_mul d _
  rw [he]
  exact mul_div_cancel_right₀ d (ne_of_gt (semigroup_exp_pos hf c h x))

lemma tiltedMean_nonneg {f g : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hg : ∀ x, 0 ≤ g x) (c : ℝ) (h : ℝ≥0) (x : ℝ) : 0 ≤ tiltedMean c h f g x := by
  apply div_nonneg _ (semigroup_exp_pos hf c h x).le
  exact integral_nonneg (fun y => mul_nonneg (hg _) (Real.exp_nonneg _))

lemma tiltedMean_pos {f g : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hg : BoundedSmooth g) (hpos : ∀ x, 0 < g x) (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    0 < tiltedMean c h f g x := by
  obtain ⟨G,hG⟩ := hg.bound
  apply div_pos _ (semigroup_exp_pos hf c h x)
  apply (integral_pos_iff_support_of_nonneg (fun y =>
    (mul_pos (hpos (x+y)) (Real.exp_pos _)).le)
    (integrable_weight_exp_translate hf hg.smooth.continuous.measurable hG c h x)).mpr
  have he : Function.support (fun y => g (x+y)*Real.exp (c*f (x+y))) = univ := by
    ext y
    simp only [Function.mem_support,mem_univ,iff_true]
    exact ne_of_gt (mul_pos (hpos _) (Real.exp_pos _))
  rw [he,measure_univ]
  norm_num

lemma tiltedMean_variance_nonneg {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : BoundedSmooth g) (c : ℝ) (h : ℝ≥0) (x : ℝ) :
    0 ≤ tiltedMean c h f (fun z => (g z)^2) x-(tiltedMean c h f g x)^2 := by
  let m := tiltedMean c h f g x
  have he : (fun z => (g z-m)^2) = fun z => (g z*g z+(-2*m)*g z)+m*m := by
    funext z; ring
  have hh := tiltedMean_nonneg hf (fun z => sq_nonneg (g z-m)) c h x
  rw [he,tiltedMean_add hf ((hg.mul hg).add (hg.const_mul (-2*m))) (BoundedSmooth.const (m*m)),
    tiltedMean_add hf (hg.mul hg) (hg.const_mul (-2*m)),tiltedMean_const_mul,
    tiltedMean_const hf] at hh
  change 0 ≤ tiltedMean c h f (fun z => g z^2) x-m^2
  have hpow : (fun z => g z*g z) = fun z => g z^2 := by funext z; ring
  rw [hpow] at hh
  dsimp only [m] at hh ⊢
  nlinarith

lemma deriv_logSemigroup_tilted {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) :
    deriv (logSemigroup c h f) = tiltedMean c h f (deriv f) := by
  funext x
  by_cases hc0 : c = 0
  · subst c
    have he : logSemigroup 0 h f = semigroup h f := by funext z; simp [logSemigroup]
    rw [he,(hasDerivAt_semigroup (hf.smooth.of_le (by simp)) hLip h x).deriv]
    simp [tiltedMean,semigroup]
  · exact (hasDerivAt_logSemigroup (hf.smooth.of_le (by simp)) hLip
      (lt_of_le_of_ne hc (Ne.symm hc0)) h x).deriv

lemma logSemigroup_curvature_pos {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hpos : ∀ x, 0 < deriv (deriv f) x)
    {c : ℝ} (hc : 0 ≤ c) (h : ℝ≥0) (x : ℝ) :
    0 < deriv (deriv (logSemigroup c h f)) x := by
  rw [deriv_logSemigroup_tilted hf hLip hc,
    (hasDerivAt_tiltedMean hf hLip hf.deriv_bounded hc h x).deriv]
  have he : (fun z => deriv (deriv f) z+c*deriv f z*deriv f z) =
      fun z => deriv (deriv f) z+c*(deriv f z*deriv f z) := by funext z; ring
  rw [he,tiltedMean_add hLip hf.deriv_bounded.deriv
    ((hf.deriv_bounded.mul hf.deriv_bounded).const_mul c),tiltedMean_const_mul]
  have hp := tiltedMean_pos hLip hf.deriv_bounded.deriv hpos c h x
  have hv := mul_nonneg hc (tiltedMean_variance_nonneg hLip hf.deriv_bounded c h x)
  have hpow : (fun z => deriv f z*deriv f z) = fun z => (deriv f z)^2 := by funext z; ring
  rw [hpow]
  nlinarith

end ZeroTemperatureSK.Heat

end
end

end OAI
