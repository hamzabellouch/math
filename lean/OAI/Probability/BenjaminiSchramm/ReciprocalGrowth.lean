import Mathlib

namespace OAI

open Set

namespace Percolation.BenjaminiSchramm

theorem reciprocal_lower_of_derivative_upper
    (f : ℝ → ℝ) (a b K : ℝ) (hK : 0 < K)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ Ioo a b, deriv f x ≤ K * (f x) ^ 2)
    (hunbounded : ∀ x ∈ Ioo a b, ∀ B : ℝ,
      ∃ y, x ≤ y ∧ y < b ∧ B < f y)
    (x : ℝ) (hx : x ∈ Ioo a b) : 1 / (K * (b - x)) ≤ f x := by
  have hinverse : 1 / f x ≤ K * (b - x) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y,hxy,hyb,hfy⟩ := hunbounded x hx (1 / ε)
    have hy : y ∈ Ioo a b := ⟨hx.1.trans_le hxy,hyb⟩
    have hsub : Icc x y ⊆ Ioo a b := fun z hz =>
      ⟨hx.1.trans_le hz.1,hz.2.trans_lt hyb⟩
    have hg (z : ℝ) (hz : z ∈ Icc x y) :
        HasDerivAt (fun t => 1 / f t) (-deriv f z / (f z) ^ 2) z := by
      simpa only [one_div,Pi.inv_apply] using!
        (hdiff z (hsub hz)).hasDerivAt.inv (hpos z (hsub hz)).ne'
    have hbound (z : ℝ) (hz : z ∈ interior (Icc x y)) :
        -K ≤ deriv (fun t => 1 / f t) z := by
      rw [(hg z (interior_subset hz)).deriv,neg_div]
      apply neg_le_neg
      exact (div_le_iff₀ (sq_pos_of_pos (hpos z (hsub (interior_subset hz))))).mpr
        (hderiv z (hsub (interior_subset hz)))
    have hdist := (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
      (fun z hz => (hg z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hg z (interior_subset hz)).differentiableAt.differentiableWithinAt)
      hbound x ⟨le_rfl,hxy⟩ y ⟨hxy,le_rfl⟩ hxy
    have hinv : 1 / f y < ε := by
      apply (div_lt_iff₀ (hpos y hy)).mpr
      have hh := (div_lt_iff₀ hε).mp hfy
      nlinarith
    have hKdist := mul_le_mul_of_nonneg_left (show y - x ≤ b - x by linarith) hK.le
    linarith
  have hmul := mul_le_mul_of_nonneg_right hinverse (hpos x hx).le
  rw [div_mul_cancel₀ 1 (hpos x hx).ne'] at hmul
  apply (div_le_iff₀ (mul_pos hK (sub_pos.mpr hx.2))).mpr
  nlinarith

end Percolation.BenjaminiSchramm

end OAI
