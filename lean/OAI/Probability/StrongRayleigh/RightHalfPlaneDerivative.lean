import Mathlib

namespace OAI

noncomputable section
open Set Metric

namespace Problem336AdditiveD139

lemma cayley_rightHalfPlane (z : ℂ) (hz : ‖z‖ < 1) :
    0 < ((1 + z) / (1 - z)).re := by
  have hn : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hd : 1 - z ≠ 0 := by
    intro he
    have : z = 1 := by linear_combination -he
    simp [this] at hz
  rw [Complex.div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hd)
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re,
    Complex.add_im, Complex.one_im, Complex.sub_im, zero_add, zero_sub]
  rw [Complex.normSq_apply] at hn
  nlinarith

lemma cayley_norm_le_one (z : ℂ) (r : ℝ) (hr : 0 < r) (hz : 0 < z.re) :
    ‖(z - r) / (z + r)‖ ≤ 1 := by
  have hd : z + (r : ℂ) ≠ 0 := by
    intro hh
    have := congrArg Complex.re hh
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
    linarith
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hd), one_mul]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, add_zero]
  nlinarith

theorem rightHalfPlane_derivative_bound
    (f : ℂ → ℂ) (f' : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f {z | 0 < z.re})
    (hmap : ∀ z : ℂ, 0 < z.re → 0 < (f z).re)
    (hvalue : f 1 = (r : ℂ)) (hderiv : HasDerivAt f f' 1) :
    ‖f'‖ ≤ r := by
  let T : ℂ → ℂ := fun z => (1 + z) / (1 - z)
  let g : ℂ → ℂ := fun z => (f (T z) - r) / (f (T z) + r)
  have hTmap : MapsTo T (ball 0 1) {z | 0 < z.re} := by
    intro z hz
    exact cayley_rightHalfPlane z (by simpa using hz)
  have hTden : ∀ z ∈ ball (0 : ℂ) 1, 1 - z ≠ 0 := by
    intro z hz he
    have hze : z = 1 := by linear_combination -he
    simp [hze] at hz
  have hTd : DifferentiableOn ℂ T (ball 0 1) := by
    exact (differentiableOn_id.const_add 1).div
      (differentiableOn_id.const_sub 1) hTden
  have hfd : DifferentiableOn ℂ (fun z => f (T z)) (ball 0 1) :=
    hf.comp hTd hTmap
  have hden : ∀ z ∈ ball (0 : ℂ) 1, f (T z) + (r : ℂ) ≠ 0 := by
    intro z hz he
    have hp := hmap (T z) (hTmap hz)
    have he' := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at he'
    linarith
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    (hfd.sub_const _).div (hfd.add_const _) hden
  have hg0 : g 0 = 0 := by simp [g, T, hvalue]
  have hgmap : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
    intro z hz
    rw [hg0, mem_closedBall_zero_iff]
    exact cayley_norm_le_one (f (T z)) r hr (hmap _ (hTmap hz))
  have hTderiv : HasDerivAt T 2 0 := by
    have hp : HasDerivAt (fun z : ℂ => 1 + z) 1 0 :=
      (hasDerivAt_id (0 : ℂ)).const_add 1
    have hm : HasDerivAt (fun z : ℂ => 1 - z) (-1) 0 :=
      (hasDerivAt_id (0 : ℂ)).const_sub 1
    have hd := hp.div hm (by norm_num : (1 : ℂ) - 0 ≠ 0)
    norm_num at hd
    exact hd
  have hfderiv : HasDerivAt (fun z => f (T z)) (f' * 2) 0 := by
    have hd' : HasDerivAt f f' (T 0) := by simpa [T] using hderiv
    exact hd'.comp 0 hTderiv
  have hgderiv : HasDerivAt g (f' / r) 0 := by
    have hd := (hfderiv.sub_const (r : ℂ)).div (hfderiv.add_const (r : ℂ))
      (hden 0 (by simp))
    have he : (f' * 2 * (f (T 0) + r) - (f (T 0) - r) * (f' * 2)) /
        (f (T 0) + r) ^ 2 = f' / r := by
      simp only [T, add_zero, sub_zero, div_one, hvalue]
      field_simp
      ring
    rw [he] at hd
    exact hd
  have hb := Complex.norm_deriv_le_one_of_mapsTo_ball hgd hgmap (by norm_num : (0 : ℝ) < 1)
  rw [hgderiv.deriv, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hb
  exact (div_le_one hr).mp hb

end Problem336AdditiveD139

end

end OAI
