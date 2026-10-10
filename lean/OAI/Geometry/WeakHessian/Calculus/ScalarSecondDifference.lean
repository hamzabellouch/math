import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.AddConst

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
open Set Filter MeasureTheory
open scoped Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian

def secondDifference (f : ℝ → ℝ) (h x : ℝ) : ℝ :=
  (f (x + h) + f (x - h) - 2 * f x) / h ^ 2

lemma taylorPolynomial_two {f : ℝ → ℝ} (x y : ℝ) :
    taylorWithinEval f 2 univ x y =
      f x + (y - x) * deriv f x + (y - x) ^ 2 / 2 * deriv (deriv f) x := by
  norm_num only [taylorWithinEval_succ, taylor_within_zero_eval,
    iteratedDerivWithin_univ, iteratedDeriv_succ, iteratedDeriv_zero,
    smul_eq_mul, Nat.factorial]
  ring

lemma secondDifference_tendsto {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    Tendsto (fun h => secondDifference f h x) (𝓝[≠] 0) (𝓝 (deriv (deriv f) x)) := by
  have ht : Tendsto
      (fun y => (f y - (f x + (y - x) * deriv f x +
        (y - x) ^ 2 / 2 * deriv (deriv f) x)) / (y - x) ^ 2)
      (𝓝 x) (𝓝 0) := by
    simpa only [nhdsWithin_univ, taylorPolynomial_two, smul_eq_mul, div_eq_inv_mul] using
      (Real.taylor_tendsto convex_univ (mem_univ x) hf.contDiffOn)
  have hap : Tendsto (fun h : ℝ => x + h) (𝓝[≠] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : ℝ => x + h) (𝓝[≠] 0) (𝓝 (x + 0)))
  have ham : Tendsto (fun h : ℝ => x - h) (𝓝[≠] 0) (𝓝 x) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun h : ℝ => x - h) (𝓝[≠] 0) (𝓝 (x - 0)))
  have hp := ht.comp hap
  have hm := ht.comp ham
  have hc := (hp.add hm).add_const (deriv (deriv f) x)
  simp only [zero_add] at hc
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hn : h ≠ 0 := hh
  dsimp only [Function.comp_def, secondDifference]
  field_simp [hn]
  ring

lemma taylor_remainder_one {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {x y : ℝ}
    (hxy : x ≠ y) :
    ∃ z ∈ uIoo x y, f y - (f x + (y - x) * deriv f x) =
      deriv (deriv f) z * (y - x) ^ 2 / 2 := by
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hxy hf.contDiffOn
  refine ⟨z, hz, ?_⟩
  have hd : derivWithin f (uIcc x y) x = deriv f x :=
    (hf.differentiable (by norm_num) x).hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_uIcc hxy x left_mem_uIcc)
  simpa [taylorWithinEval_succ, iteratedDerivWithin_one, hd,
    iteratedDeriv_succ, smul_eq_mul] using he

lemma norm_secondDifference_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, |deriv (deriv f) x| ≤ M) (h x : ℝ) :
    |secondDifference f h x| ≤ M := by
  by_cases hh : h = 0
  · simp [secondDifference, hh, hM]
  have hp : x ≠ x + h := by intro he; apply hh; linarith
  have hm : x ≠ x - h := by intro he; apply hh; linarith
  obtain ⟨z, _, hz⟩ := taylor_remainder_one hf hp
  obtain ⟨w, _, hw⟩ := taylor_remainder_one hf hm
  have he : secondDifference f h x = (deriv (deriv f) z + deriv (deriv f) w) / 2 := by
    simp only [secondDifference]
    apply (div_eq_iff (pow_ne_zero 2 hh)).2
    simp only [add_sub_cancel_left, sub_sub_cancel_left, neg_sq] at hz hw
    nlinarith
  rw [he, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have := (abs_add_le (deriv (deriv f) z) (deriv (deriv f) w)).trans
    (add_le_add (hbound z) (hbound w))
  linarith

lemma integral_mul_translate (f φ : ℝ → ℝ) (h : ℝ) :
    (∫ x, f x * φ (x + h)) = ∫ x, f (x - h) * φ x := by
  simpa only [add_sub_cancel_right] using
    integral_add_right_eq_self (fun x => f (x - h) * φ x) h

lemma integrable_mul_translate {f φ : ℝ → ℝ} (hf : Continuous f)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (h : ℝ) :
    Integrable (fun x => f x * φ (x + h)) := by
  apply (hf.mul (hφ.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
  exact (hc.comp_homeomorph (Homeomorph.addRight h)).mul_left

lemma integrable_translate_mul {f φ : ℝ → ℝ} (hf : Continuous f)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (h : ℝ) :
    Integrable (fun x => f (x + h) * φ x) := by
  apply ((hf.comp (continuous_id.add continuous_const)).mul hφ).integrable_of_hasCompactSupport
  exact hc.mul_left

lemma integral_mul_secondDifference {f φ : ℝ → ℝ} (hf : Continuous f)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (h : ℝ) :
    (∫ x, f x * secondDifference φ h x) = ∫ x, secondDifference f h x * φ x := by
  have hi := integrable_mul_translate hf hφ hc h
  have hj : Integrable (fun x => f x * φ (x - h)) := by
    simpa only [sub_eq_add_neg] using integrable_mul_translate hf hφ hc (-h)
  have hk : Integrable (fun x => f x * φ x) := by
    simpa only [add_zero] using integrable_mul_translate hf hφ hc 0
  have Hil := integrable_translate_mul hf hφ hc h
  have Hjl : Integrable (fun x => f (x - h) * φ x) := by
    simpa only [sub_eq_add_neg] using integrable_translate_mul hf hφ hc (-h)
  have e₁ := integral_mul_translate f φ h
  have e₂ : (∫ x, f x * φ (x - h)) = ∫ x, f (x + h) * φ x := by
    simpa only [sub_neg_eq_add, ← sub_eq_add_neg] using integral_mul_translate f φ (-h)
  have ea : (fun x => f x * secondDifference φ h x) =
      (fun x => (f x * φ (x + h) + f x * φ (x - h) - 2 * (f x * φ x)) / h ^ 2) := by
    funext x
    dsimp [secondDifference]
    ring
  have eb : (fun x => secondDifference f h x * φ x) =
      (fun x => (f (x + h) * φ x + f (x - h) * φ x - 2 * (f x * φ x)) / h ^ 2) := by
    funext x
    dsimp [secondDifference]
    ring
  have hia : Integrable (fun x => f x * φ (x + h) + f x * φ (x - h)) := hi.add hj
  have hib : Integrable (fun x => f (x + h) * φ x + f (x - h) * φ x) := Hil.add Hjl
  rw [ea, eb, integral_div, integral_div, integral_sub hia (hk.const_mul 2),
    integral_add hi hj, integral_sub hib (hk.const_mul 2),
    integral_add Hil Hjl, e₁, e₂, add_comm]

lemma secondDifference_eq_zero_outside {φ : ℝ → ℝ}
    (hs : tsupport φ ⊆ Ioo (0 : ℝ) 1) {h x : ℝ} (hh : |h| < 1)
    (hx : x ∉ Icc (-1 : ℝ) 2) : secondDifference φ h x = 0 := by
  have he {y : ℝ} (hy : y ∉ Ioo (0 : ℝ) 1) : φ y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hp => hy (hs hp))
  have hh' := abs_lt.mp hh
  have hp : φ (x + h) = 0 := by
    apply he
    intro hy
    apply hx
    constructor <;> linarith [hy.1, hy.2]
  have hm : φ (x - h) = 0 := by
    apply he
    intro hy
    apply hx
    constructor <;> linarith [hy.1, hy.2]
  have hz : φ x = 0 := by
    apply he
    intro hy
    apply hx
    constructor <;> linarith [hy.1, hy.2]
  simp only [secondDifference, hp, hm, hz, mul_zero, add_zero, sub_zero, zero_div]

lemma secondDifference_nonpos_of_concave {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Ioo (0 : ℝ) 1) f) {h x : ℝ}
    (hp : x + h ∈ Ioo (0 : ℝ) 1) (hm : x - h ∈ Ioo (0 : ℝ) 1) :
    secondDifference f h x ≤ 0 := by
  have he := hf.2 hp hm (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  have ht : (1/2 : ℝ) • (x + h) + (1/2 : ℝ) • (x - h) = x := by
    simp only [smul_eq_mul]
    ring
  rw [ht] at he
  simp only [smul_eq_mul] at he
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg h)
  linarith

lemma integral_secondDifference_tendsto {f φ : ℝ → ℝ} (hf : Continuous f)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ioo (0 : ℝ) 1) :
    Tendsto (fun h => ∫ x, f x * secondDifference φ h x) (𝓝[≠] 0)
      (𝓝 (∫ x, f x * deriv (deriv φ) x)) := by
  have hdφ : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hddφ := hdφ.continuous_deriv_one
  obtain ⟨M, hM⟩ := hddφ.bounded_above_of_compact_support hc.deriv.deriv
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn : ContinuousOn f (Icc (-1 : ℝ) 2))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by norm_num))
  have hcF (h : ℝ) : Continuous (fun x => f x * secondDifference φ h x) := by
    dsimp only [secondDifference]
    have := hφ.continuous
    fun_prop
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc (-1 : ℝ) 2)) (l := 𝓝[≠] (0 : ℝ))
    (fun _ => B * M)
    (Eventually.of_forall fun h => (hcF h).aestronglyMeasurable)
    (Eventually.of_forall fun h => ?_)
    (integrable_const (B * M))
    (Eventually.of_forall fun x => tendsto_const_nhds.mul (secondDifference_tendsto hφ x))
  · have he : (∫ x in Icc (-1 : ℝ) 2, f x * deriv (deriv φ) x) =
        ∫ x, f x * deriv (deriv φ) x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hn : x ∉ tsupport (deriv (deriv φ)) := by
        intro hp
        have hp' := hs (tsupport_deriv_subset (tsupport_deriv_subset hp))
        exact hx ⟨by linarith [hp'.1], by linarith [hp'.2]⟩
      rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
    rw [he] at hlim
    apply hlim.congr'
    have hev : ∀ᶠ h : ℝ in 𝓝[≠] 0, |h| < 1 := by
      simpa only [sub_zero] using (eventually_abs_sub_lt (0 : ℝ) zero_lt_one).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hev] with h hh
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [secondDifference_eq_zero_outside hs hh hx, mul_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_mul, Real.norm_eq_abs (secondDifference φ h x)]
    apply mul_le_mul (hB x hx) (norm_secondDifference_le hφ hM0 (by simpa using hM) h x)
      (abs_nonneg _) hB0

end WeakHessian

end
end

end OAI
