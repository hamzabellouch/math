import OAI.Analysis.WeakInfiniteness.ElementaryCP

namespace OAI

/-! The finite coefficient identity in KR02 Proposition 7.14. Relative copies
of the commuting compressed coefficients turn the finite sum into one inner
compression. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {D M : Type*} [NonUnitalCStarAlgebra D] [Fintype M] [DecidableEq M]

lemma collapse_compression_of_relative_copies (d r : M → D) (z b : D)
    (hcomm : ∀ i j, Commute (star z * (star (d i) * b * d j) * z) (r j))
    (hrel : ∀ i j, (star (r i) * r j) * (star z * (star (d i) * b * d j) * z) =
      if i = j then star z * (star (d i) * b * d j) * z else 0) :
    star (∑ i, d i * z * r i) * b * (∑ i, d i * z * r i) =
      star z * (∑ i, star (d i) * b * d i) * z := by
  have hterm (i j : M) :
      star (r i) * (star z * (star (d i) * b * d j) * z) * r j =
        if i = j then star z * (star (d i) * b * d j) * z else 0 := by
    calc
      _ = star (r i) * ((star z * (star (d i) * b * d j) * z) * r j) := mul_assoc _ _ _
      _ = star (r i) * (r j * (star z * (star (d i) * b * d j) * z)) := by
        rw [(hcomm i j).eq]
      _ = (star (r i) * r j) * (star z * (star (d i) * b * d j) * z) := (mul_assoc _ _ _).symm
      _ = _ := hrel i j
  calc
    _ = ∑ i, ∑ j, star (r i) * (star z * (star (d i) * b * d j) * z) * r j := by
      simp only [star_sum, Finset.sum_mul, Finset.mul_sum, star_mul, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, if i = j then star z * (star (d i) * b * d j) * z else 0 := by
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hterm i j))
    _ = ∑ i, star z * (star (d i) * b * d i) * z := by simp
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

lemma collapse_compression_error_le (d r : M → D) (z a b : D) (hz : ‖z‖ ≤ 1)
    (hfix : star z * a * z = a)
    (hcomm : ∀ i j, Commute (star z * (star (d i) * b * d j) * z) (r j))
    (hrel : ∀ i j, (star (r i) * r j) * (star z * (star (d i) * b * d j) * z) =
      if i = j then star z * (star (d i) * b * d j) * z else 0) :
    ‖star (∑ i, d i * z * r i) * b * (∑ i, d i * z * r i) - a‖ ≤
      ‖(∑ i, star (d i) * b * d i) - a‖ := by
  rw [collapse_compression_of_relative_copies d r z b hcomm hrel]
  have he : star z * (∑ i, star (d i) * b * d i) * z - a =
      star z * ((∑ i, star (d i) * b * d i) - a) * z := by
    rw [mul_sub, sub_mul, hfix]
  rw [he]
  calc
    _ ≤ (‖star z‖ * ‖(∑ i, star (d i) * b * d i) - a‖) * ‖z‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖(∑ i, star (d i) * b * d i) - a‖) * 1 := by
      rw [norm_star]
      gcongr
    _ = _ := by ring

end WeakPureInfiniteness

end

end OAI
