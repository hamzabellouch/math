import Mathlib

namespace OAI

noncomputable section

open Set Filter Polynomial
open scoped Topology

namespace Problem336AdditiveD139

lemma analytic_eq_zero_of_im_nonpos_of_zero {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U)
    (him : ∀ z ∈ U, (f z).im ≤ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hzero : f z₀ = 0) :
    ∀ z ∈ U, f z = 0 := by
  rcases hf.is_constant_or_isOpen hUc with ⟨c, hc⟩ | hopen
  · have hc0 : c = 0 := (hc z₀ hz₀).symm.trans hzero
    simpa [hc0] using hc
  · have hiopen : IsOpen (f '' U) := hopen U Subset.rfl hU
    have hmem : (0 : ℂ) ∈ f '' U := ⟨z₀, hz₀, hzero⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hiopen.mem_nhds hmem)
    have hpoint : ((ε / 2 : ℝ) : ℂ) * Complex.I ∈ Metric.ball (0 : ℂ) ε := by
      simp only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    obtain ⟨z, hz, heq⟩ := hball hpoint
    have h := him z hz
    rw [heq] at h
    norm_num at h
    linarith

lemma affine_stable_normalized_slope_im_neg (a b : ℂ)
    (hstable : ∀ w : ℂ, 0 < w.im → a + w * b ≠ 0) (hb : b ≠ 0) :
    (b / (a + Complex.I * b)).im < 0 := by
  have hr : 0 ≤ (a / b).im := by
    by_contra! hneg
    have hw : 0 < (-(a / b)).im := by simpa using neg_pos.mpr hneg
    apply hstable (-(a / b)) hw
    rw [neg_mul, div_mul_cancel₀ _ hb]
    ring
  have him : 0 < (a / b + Complex.I).im := by
    simp only [Complex.add_im, Complex.I_im]
    linarith
  have hne : a / b + Complex.I ≠ 0 := by
    intro h
    rw [h] at him
    norm_num at him
  have hid : b / (a + Complex.I * b) = (a / b + Complex.I)⁻¹ := by
    rw [show a / b + Complex.I = (a + Complex.I * b) / b by
      rw [add_div, mul_div_cancel_right₀ _ hb], inv_div]
  rw [hid, Complex.inv_im]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos him) (Complex.normSq_pos.mpr hne)

theorem affine_stable_analytic_slope_zero_or_nonvanishing
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (A B : ℂ → ℂ) (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hstable : ∀ z ∈ U, ∀ w : ℂ, 0 < w.im → A z + w * B z ≠ 0) :
    (∀ z ∈ U, B z = 0) ∨ (∀ z ∈ U, B z ≠ 0) := by
  classical
  by_cases hzero : ∀ z ∈ U, B z = 0
  · exact Or.inl hzero
  right
  intro z₀ hz₀ hBzero
  let f : ℂ → ℂ := fun z => B z / (A z + Complex.I * B z)
  have hden : ∀ z ∈ U, A z + Complex.I * B z ≠ 0 := by
    intro z hz
    exact hstable z hz Complex.I (by norm_num)
  have hf : AnalyticOnNhd ℂ f U := by
    intro z hz
    exact (hB z hz).div ((hA z hz).add (analyticAt_const.mul (hB z hz))) (hden z hz)
  have him : ∀ z ∈ U, (f z).im ≤ 0 := by
    intro z hz
    by_cases hb : B z = 0
    · simp [f, hb]
    · exact (affine_stable_normalized_slope_im_neg (A z) (B z) (hstable z hz) hb).le
  have hfzero : f z₀ = 0 := by simp [f, hBzero]
  have hfall := analytic_eq_zero_of_im_nonpos_of_zero hU hUc hf him hz₀ hfzero
  apply hzero
  intro z hz
  have h := hfall z hz
  exact (div_eq_zero_iff.mp h).resolve_right (hden z hz)

theorem affine_stable_entire_slope_nonvanishing
    (A B : ℂ → ℂ)
    (hA : AnalyticOnNhd ℂ A {z : ℂ | 0 < z.im})
    (hB : AnalyticOnNhd ℂ B Set.univ)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im → A z + w * B z ≠ 0)
    {z₁ : ℂ} (hne : B z₁ ≠ 0) :
    ∀ z : ℂ, 0 < z.im → B z ≠ 0 := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  rcases affine_stable_analytic_slope_zero_or_nonvanishing hU hUc A B hA
    (hB.mono (subset_univ _)) (fun z hz w hw => hstable z w hz hw) with hzero | hnonzero
  · have hevent : ∀ᶠ z in 𝓝 Complex.I, B z = 0 := by
      filter_upwards [hU.mem_nhds (by norm_num : Complex.I ∈ {z : ℂ | 0 < z.im})]
        with z hz using hzero z hz
    have hall := hB.eqOn_of_preconnected_of_eventuallyEq
      (g := fun _ : ℂ => 0) analyticOnNhd_const isPreconnected_univ
      (mem_univ Complex.I) hevent
    exact (hne (hall (mem_univ z₁))).elim
  · exact hnonzero

theorem polynomial_slope_stable_of_affine_stable (p q : ℝ[X]) (hq : q ≠ 0)
    (hstable : ∀ z w : ℂ, 0 < z.im → 0 < w.im →
      aeval z p + w * aeval z q ≠ 0) :
    ∀ z : ℂ, 0 < z.im → aeval z q ≠ 0 := by
  have hex : ∃ t : ℝ, q.eval t ≠ 0 := by
    by_contra! h
    apply hq
    apply Polynomial.funext
    intro t
    simpa using h t
  obtain ⟨t, ht⟩ := hex
  apply affine_stable_entire_slope_nonvanishing
    (fun z : ℂ => aeval z p) (fun z : ℂ => aeval z q)
    (fun z _ => analyticAt_id.aeval_polynomial p)
    (fun z _ => analyticAt_id.aeval_polynomial q) hstable (z₁ := (t : ℂ))
  have heq : aeval (t : ℂ) q = ((q.eval t : ℝ) : ℂ) :=
    Polynomial.aeval_ofReal (K := ℂ) q t
  exact heq.trans_ne (by exact_mod_cast ht)

end Problem336AdditiveD139

end

end OAI
