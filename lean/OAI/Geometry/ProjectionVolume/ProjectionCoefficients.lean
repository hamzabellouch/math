import OAI.Geometry.ProjectionVolume.SimplexProjection

namespace OAI

universe uι

open scoped BigOperators

namespace Paper092

theorem twice_sum_negative_eq_sum_abs {ι : Type uι} [Fintype ι] (v : ι → ℝ)
    (hv : ∑ i, v i = 0) :
    2 * (∑ i : {i // v i < 0}, -v i.val) = ∑ i, |v i| := by
  classical
  have hpoint (i : ι) : 2 * (if v i < 0 then -v i else 0) = |v i| - v i := by
    by_cases hi : v i < 0
    · simp [hi, abs_of_neg hi]
      ring
    · simp [hi, abs_of_nonneg (le_of_not_gt hi)]
  have hsum := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hpoint)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, hv, sub_zero] at hsum
  convert hsum using 1
  congr 1
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i => v i < 0)) (by simp)
    (fun i => -v i)).symm

theorem simplexVelocity_sum {d : ℕ} (u : Euclidean d) :
    ∑ a, simplexVelocity u a = 0 := by
  simp [simplexVelocity, Fintype.sum_option]

theorem simplex_front_coefficient {d : ℕ} (u : Euclidean d) :
    (∑ a : {a : Option (Fin d) // simplexVelocity u a < 0}, -simplexVelocity u a.val) =
      ((∑ i, |u i|) + |∑ i, u i|) / 2 := by
  have h := twice_sum_negative_eq_sum_abs (simplexVelocity u) (simplexVelocity_sum u)
  have habs : (∑ a, |simplexVelocity u a|) = |∑ i, u i| + ∑ i, |u i| := by
    simp only [Fintype.sum_option, simplexVelocity, abs_neg]
  rw [habs] at h
  linarith

end Paper092

end OAI
