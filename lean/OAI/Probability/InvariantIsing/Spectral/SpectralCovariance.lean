import OAI.Probability.InvariantIsing.Spectral.SpectralCalculus

namespace OAI

/-! Translation and positive scaling of the finite spectral transform. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteInverse_constant (ρ : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) (c : ℝ) :
    finiteInverse ρ (fun _ => c) hρ hρsum x = c + 1 / x := by
  have hs := finiteInverse_spec ρ (fun _ => c) hρ hρsum hx
  apply finiteResolvent_solution_unique (fun a => (hρ a).le) hρsum hs.1
    (fun _ => by linarith [one_div_pos.mpr hx]) hs.2
  exact constant_spectrum_solution hρsum hx

theorem finiteR_constant (ρ : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (x c : ℝ) :
    finiteR ρ (fun _ => c) hρ hρsum x = c := by
  by_cases hx : 0 < x
  · simp only [finiteR, ite_eq_left hx, finiteInverse_constant ρ hρ hρsum hx c]
    ring
  · simp only [finiteR, ite_eq_right hx]
    rw [← Finset.sum_mul, hρsum, one_mul]

theorem finiteResolvent_scale (ρ eig : ι → ℝ) (b t : ℝ) :
    finiteResolvent ρ (fun a => t * eig a) (t * b) =
      (1 / t) * finiteResolvent ρ eig b := by
  unfold finiteResolvent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_sub, div_mul_eq_div_div]
  ring

theorem finiteInverse_translate (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 < x) (c : ℝ) :
    finiteInverse ρ (fun a => eig a + c) hρ hρsum x =
      finiteInverse ρ eig hρ hρsum x + c := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have ht := finiteInverse_spec ρ (fun a => eig a + c) hρ hρsum hx
  apply finiteResolvent_solution_unique (fun a => (hρ a).le) hρsum ht.1
    (fun a => by linarith [hs.1 a]) ht.2
  rw [finiteResolvent_translate, hs.2]

theorem finiteInverse_scale (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    finiteInverse ρ (fun a => t * eig a) hρ hρsum x =
      t * finiteInverse ρ eig hρ hρsum (t * x) := by
  have hs := finiteInverse_spec ρ eig hρ hρsum (mul_pos ht hx)
  have hs' := finiteInverse_spec ρ (fun a => t * eig a) hρ hρsum hx
  apply finiteResolvent_solution_unique (fun a => (hρ a).le) hρsum hs'.1
    (fun a => mul_lt_mul_of_pos_left (hs.1 a) ht) hs'.2
  rw [finiteResolvent_scale ρ eig _ t, hs.2]
  field_simp

theorem finiteR_translate (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) (c : ℝ) :
    finiteR ρ (fun a => eig a + c) hρ hρsum x =
      finiteR ρ eig hρ hρsum x + c := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [finiteR, lt_self_iff_false, ite_false, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul, hρsum, one_mul]
  · simp only [finiteR, ite_eq_left h, finiteInverse_translate ρ eig hρ hρsum h c]
    ring

theorem finiteR_scale (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    finiteR ρ (fun a => t * eig a) hρ hρsum x =
      t * finiteR ρ eig hρ hρsum (t * x) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [finiteR, mul_zero, lt_self_iff_false, ite_false]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · simp only [finiteR, ite_eq_left h, ite_eq_left (mul_pos ht h),
      finiteInverse_scale ρ eig hρ hρsum h ht]
    field_simp

end InvariantIsing

end

end OAI
