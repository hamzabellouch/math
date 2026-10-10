import Mathlib

namespace OAI

open Set

namespace Percolation.BenjaminiSchramm

theorem reciprocal_upper_of_derivative_lower
    (f : ℝ → ℝ) (a b k : ℝ) (hk : 0 < k)
    (hpos : ∀ x ∈ Ioo a b, 0 < f x)
    (hdiff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ Ioo a b, k * (f x)^2 ≤ deriv f x)
    (x : ℝ) (hx : x ∈ Ioo a b) : f x ≤ 1 / (k * (b-x)) := by
  have hinv : k * (b-x) ≤ 1 / f x := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := min ((b-x)/2) (ε/(2*k))
    have hδ : 0 < δ := lt_min (div_pos (sub_pos.mpr hx.2) (by norm_num))
      (div_pos hε (by positivity))
    have hδx : δ ≤ (b-x)/2 := min_le_left _ _
    have hδε : δ ≤ ε/(2*k) := min_le_right _ _
    let y := b-δ
    have hxy : x < y := by dsimp [y]; linarith
    have hyb : y < b := by dsimp [y]; linarith
    have hsub : Icc x y ⊆ Ioo a b := fun z hz =>
      ⟨hx.1.trans_le hz.1,hz.2.trans_lt hyb⟩
    have hg (z : ℝ) (hz : z ∈ Icc x y) :
        HasDerivAt (fun t => -(1 / f t)) (deriv f z / (f z)^2) z := by
      have hh := ((hdiff z (hsub hz)).hasDerivAt.inv (hpos z (hsub hz)).ne').neg
      simpa only [one_div,Pi.inv_apply,Pi.neg_apply,neg_div,neg_neg] using! hh
    have hbound (z : ℝ) (hz : z ∈ interior (Icc x y)) :
        k ≤ deriv (fun t => -(1 / f t)) z := by
      rw [(hg z (interior_subset hz)).deriv]
      exact (le_div_iff₀ (sq_pos_of_pos (hpos z (hsub (interior_subset hz))))).mpr
        (hderiv z (hsub (interior_subset hz)))
    have hdist := (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
      (fun z hz => (hg z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hg z (interior_subset hz)).differentiableAt.differentiableWithinAt)
      hbound x ⟨le_rfl,hxy.le⟩ y ⟨hxy.le,le_rfl⟩ hxy.le
    have hn : 0 ≤ 1 / f y := (div_pos zero_lt_one (hpos y (hsub ⟨hxy.le,le_rfl⟩))).le
    have he : 2*k*δ ≤ ε := by
      simpa only [mul_comm δ] using (le_div_iff₀ (by positivity : 0 < 2*k)).mp hδε
    dsimp only [y] at hdist
    nlinarith
  apply (le_div_iff₀ (mul_pos hk (sub_pos.mpr hx.2))).mpr
  have hh := (le_div_iff₀ (hpos x hx)).mp hinv
  nlinarith

end Percolation.BenjaminiSchramm

end OAI
