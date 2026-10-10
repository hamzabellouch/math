import OAI.Probability.StrongRayleigh.RightHalfPlaneDerivative

namespace OAI

noncomputable section
open Set

namespace Problem336AdditiveD139

lemma sq_mem_slitPlane_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z ^ 2 ∈ Complex.slitPlane := by
  by_cases hi : z.im = 0
  · left
    simp only [pow_two, Complex.mul_re, hi, mul_zero, sub_zero]
    exact mul_pos hz hz
  · right
    simp only [pow_two, Complex.mul_im]
    rw [mul_comm z.im z.re, ← two_mul]
    exact mul_ne_zero (by norm_num) (mul_ne_zero (ne_of_gt hz) hi)

lemma sqrt_re_pos_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.2
  apply div_pos _ (by norm_num)
  rcases hz with hr | hi
  · linarith [norm_nonneg z]
  · have hab := Complex.abs_re_lt_norm.mpr hi
    have hneg := neg_abs_le z.re
    linarith

lemma complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  rw [Complex.sqrt, ← Complex.cpow_mul_nat]
  norm_num

theorem slitPlane_derivative_bound
    (f : ℂ → ℂ) (f' : ℂ) (r : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f Complex.slitPlane)
    (hmap : MapsTo f Complex.slitPlane Complex.slitPlane)
    (hvalue : f 1 = (r : ℂ)) (hderiv : HasDerivAt f f' 1) :
    ‖f'‖ ≤ r := by
  let H : ℂ → ℂ := fun z => Complex.sqrt (f (z ^ 2))
  have hsquare : MapsTo (fun z : ℂ => z ^ 2) {z | 0 < z.re}
      Complex.slitPlane := fun _ hz => sq_mem_slitPlane_of_re_pos hz
  have hHd : DifferentiableOn ℂ H {z | 0 < z.re} :=
    Complex.differentiableOn_sqrt.comp
      (hf.comp (differentiableOn_id.pow 2) hsquare)
      (hmap.comp hsquare)
  have hHmap : ∀ z : ℂ, 0 < z.re → 0 < (H z).re := by
    intro z hz
    exact sqrt_re_pos_of_mem_slitPlane (hmap (hsquare hz))
  have hHvalue : H 1 = (Real.sqrt r : ℂ) := by
    dsimp [H]
    rw [one_pow, hvalue]
    exact Complex.sqrt_of_nonneg (by exact_mod_cast hr.le)
  have hone : (1 : ℂ) ∈ {z : ℂ | 0 < z.re} := by norm_num
  have hopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hHderiv := (hHd.differentiableAt (hopen.mem_nhds hone)).hasDerivAt
  have hbound := rightHalfPlane_derivative_bound H (deriv H 1) (Real.sqrt r)
    (Real.sqrt_pos.2 hr) hHd hHmap hHvalue hHderiv
  have hsquarederiv : HasDerivAt (fun z : ℂ => z ^ 2) 2 1 := by
    simpa using (hasDerivAt_pow 2 (1 : ℂ))
  have hcomp : HasDerivAt (fun z : ℂ => f (z ^ 2)) (f' * 2) 1 := by
    have hd : HasDerivAt f f' ((1 : ℂ) ^ 2) := by simpa using hderiv
    exact hd.comp 1 hsquarederiv
  have hprod : HasDerivAt (fun z : ℂ => f (z ^ 2))
      (2 * H 1 * deriv H 1) 1 := by
    have hh := hHderiv.pow 2
    have hfun : H ^ 2 = (fun z : ℂ => f (z ^ 2)) := by
      funext z
      exact complex_sqrt_sq _
    rw [hfun] at hh
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hh
  have heq : (Real.sqrt r : ℂ) * deriv H 1 = f' := by
    have hh := hprod.unique hcomp
    rw [hHvalue] at hh
    linear_combination hh / 2
  rw [← heq, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg r)]
  calc
    Real.sqrt r * ‖deriv H 1‖ ≤ Real.sqrt r * Real.sqrt r :=
      mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg r)
    _ = r := Real.mul_self_sqrt hr.le

theorem weakPick_derivative_re_le
    (f : ℂ → ℂ) (f' : ℂ)
    (hf : DifferentiableOn ℂ f Complex.slitPlane)
    (hupper : ∀ z : ℂ, 0 < z.im → 0 ≤ (f z).im)
    (hlower : ∀ z : ℂ, z.im < 0 → (f z).im ≤ 0)
    (hreal : ∀ x : ℝ, 0 < x →
      0 ≤ (f (x : ℂ)).re ∧ (f (x : ℂ)).im = 0)
    (hderiv : HasDerivAt f f' 1) :
    f'.re ≤ (f 1).re := by
  let g : ℂ → ℂ := fun z => f z + z
  have hmap : MapsTo g Complex.slitPlane Complex.slitPlane := by
    intro z hz
    rcases lt_trichotomy z.im 0 with hi | hi | hi
    · right
      have hfi := hlower z hi
      change (f z).im + z.im ≠ 0
      linarith
    · left
      have hzr : 0 < z.re := hz.resolve_right (not_not.mpr hi)
      have hzreal : (z.re : ℂ) = z := by
        apply Complex.ext <;> simp [hi]
      have hnonneg := (hreal z.re hzr).1
      rw [hzreal] at hnonneg
      change 0 < (f z).re + z.re
      linarith
    · right
      have hfi := hupper z hi
      change (f z).im + z.im ≠ 0
      linarith
  have h1 := hreal 1 (by norm_num)
  have hr : 0 < (f 1).re + 1 := by norm_num at h1 ⊢; linarith [h1.1]
  have hvalue : g 1 = (((f 1).re + 1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [g]
    · simpa [g] using h1.2
  have hb := slitPlane_derivative_bound g (f' + 1) ((f 1).re + 1) hr
    (hf.add differentiableOn_id) hmap hvalue (hderiv.add (hasDerivAt_id 1))
  have hre := Complex.re_le_norm (f' + 1)
  simp only [Complex.add_re, Complex.one_re] at hre
  linarith

theorem reflectedPick_derivative_re_le
    (f : ℂ → ℂ) (f' : ℂ)
    (hf : DifferentiableOn ℂ f Complex.slitPlane)
    (hupper : ∀ z : ℂ, 0 < z.im → 0 ≤ (f z).im)
    (hconj : ∀ z : ℂ, f (star z) = star (f z))
    (hreal : ∀ x : ℝ, 0 < x → 0 ≤ (f (x : ℂ)).re)
    (hderiv : HasDerivAt f f' 1) :
    f'.re ≤ (f 1).re := by
  apply weakPick_derivative_re_le f f' hf hupper
  · intro z hz
    have hh := hupper (star z) (by simpa using neg_pos.mpr hz)
    rw [hconj] at hh
    simpa using hh
  · intro x hx
    refine ⟨hreal x hx, ?_⟩
    have hh := congrArg Complex.im (hconj (x : ℂ))
    simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_im] at hh
    linarith
  · exact hderiv

end Problem336AdditiveD139

end

end OAI
