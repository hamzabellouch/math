import OAI.NumberTheory.Ostmann.Supply.FiniteSpectralProjection

namespace OAI

/-! # The centered support projections in the contracting local kernel -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def finiteSupportMean {α : Type*} (S : Finset α) (f : α → ℂ) : ℂ :=
  (S.card : ℂ)⁻¹ * ∑ x ∈ S, f x

noncomputable def centeredSupportProjection {α : Type*}
    (S : Finset α) (f : α → ℂ) (x : α) : ℂ :=
  if x ∈ S then f x - finiteSupportMean S f else 0

theorem finiteSupportMean_spec {α : Type*} (S : Finset α) (f : α → ℂ) :
    (S.card : ℂ) * finiteSupportMean S f = ∑ x ∈ S, f x := by
  by_cases hs : S.card = 0
  · have he : S = ∅ := Finset.card_eq_zero.mp hs
    simp [he, finiteSupportMean]
  · unfold finiteSupportMean
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

theorem centered_support_energy {α : Type*} (S : Finset α) (f : α → ℂ) (c : ℂ)
    (hc : ∑ x ∈ S, f x = (S.card : ℂ) * c) :
    (∑ x ∈ S, ‖f x - c‖ ^ 2) = (∑ x ∈ S, ‖f x‖ ^ 2) - S.card * ‖c‖ ^ 2 := by
  have hr := congrArg Complex.re hc
  have hi := congrArg Complex.im hc
  simp only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, add_zero] at hr hi
  have he (x : α) : ‖f x - c‖ ^ 2 = ‖f x‖ ^ 2 -
      2 * (f x).re * c.re - 2 * (f x).im * c.im + ‖c‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  rw [hr, hi, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem centeredSupportProjection_energy {α : Type*} [Fintype α]
    (S : Finset α) (f : α → ℂ) :
    (∑ x, ‖centeredSupportProjection S f x‖ ^ 2) =
      (∑ x ∈ S, ‖f x‖ ^ 2) - S.card * ‖finiteSupportMean S f‖ ^ 2 := by
  calc
    _ = ∑ x ∈ S, ‖f x - finiteSupportMean S f‖ ^ 2 := by
      simp only [centeredSupportProjection, apply_ite, norm_zero, ite_pow,
        zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_mem, Finset.univ_inter]
    _ = _ := centered_support_energy S f _ (finiteSupportMean_spec S f).symm

theorem centeredSupportProjection_energy_le {α : Type*} [Fintype α]
    (S : Finset α) (f : α → ℂ) :
    (∑ x, ‖centeredSupportProjection S f x‖ ^ 2) ≤ ∑ x, ‖f x‖ ^ 2 := by
  rw [centeredSupportProjection_energy]
  exact (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).trans
    (Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _))

theorem centeredSupportProjection_eq_of_eqOn {α : Type*}
    (S : Finset α) (f g : α → ℂ) (h : ∀ x ∈ S, f x = g x) :
    centeredSupportProjection S f = centeredSupportProjection S g := by
  have hm : finiteSupportMean S f = finiteSupportMean S g := by
    unfold finiteSupportMean
    rw [Finset.sum_congr rfl h]
  funext x
  by_cases hx : x ∈ S
  · simp only [centeredSupportProjection, ite_eq_left hx, h x hx, hm]
  · simp only [centeredSupportProjection, ite_eq_right hx]

theorem centeredSupportProjection_disjoint {α : Type*}
    (S T : Finset α) (h : Disjoint S T) (f : α → ℂ) (x : α) (hx : x ∈ S) :
    centeredSupportProjection T f x = 0 := by
  exact ite_eq_right (fun ht => Finset.disjoint_left.mp h hx ht)

/-- The off-diagonal compression has norm at most one half. This uses only
orthogonal support and the exact half-identity spectral bound. -/
theorem centeredSupportProjection_spectral_energy {p : ℕ} [NeZero p]
    (S T E : Finset (ZMod p)) (hST : Disjoint S T) (f : ZMod p → ℂ) :
    (∑ x, ‖centeredSupportProjection S
      (finiteSpectralProjection E (centeredSupportProjection T f)) x‖ ^ 2) ≤
      (1 / 4 : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
  let g := centeredSupportProjection T f
  have he : centeredSupportProjection S (finiteSpectralProjection E g) =
      centeredSupportProjection S (fun x => finiteSpectralProjection E g x - (1 / 2 : ℂ) * g x) := by
    apply centeredSupportProjection_eq_of_eqOn
    intro x hx
    rw [show g x = 0 from centeredSupportProjection_disjoint S T hST f x hx]
    simp
  rw [he]
  calc
    _ ≤ ∑ x, ‖finiteSpectralProjection E g x - (1 / 2 : ℂ) * g x‖ ^ 2 :=
      centeredSupportProjection_energy_le S _
    _ = (1 / 4 : ℝ) * ∑ x, ‖g x‖ ^ 2 := finiteSpectralProjection_half_energy E g
    _ ≤ _ := mul_le_mul_of_nonneg_left (centeredSupportProjection_energy_le T f) (by norm_num)

end Ostmann

end OAI
