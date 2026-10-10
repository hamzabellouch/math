import OAI.Geometry.EinsteinFour.CP2Overlap

namespace OAI

/-! The odd-dimensional linear obstruction to an involution sending every
complex projective line to an orthogonal line. -/

namespace PositiveEinsteinFour

open EinsteinFour Matrix
open scoped BigOperators ComplexConjugate

noncomputable section

theorem cp2_odd_orthogonality_obstruction (v : Fin 3 → CP2Vector)
    (hnorm : ∀ i, ‖v i‖ = 1)
    (horth : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0)
    (hdiag : ∀ i, v i i = 0)
    (hsym : ∀ i j, ‖v i j‖ = ‖v j i‖) : False := by
  have hn (i : Fin 3) : ∑ k : Fin 3, ‖v i k‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hnorm]
    norm_num
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  simp only [Fin.sum_univ_three] at h0 h1 h2
  simp only [hdiag, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, add_zero] at h0 h1 h2
  have hs01 := congrArg (fun r : ℝ => r ^ 2) (hsym 0 1)
  have hs02 := congrArg (fun r : ℝ => r ^ 2) (hsym 0 2)
  have hs12 := congrArg (fun r : ℝ => r ^ 2) (hsym 1 2)
  have ha : ‖v 0 2‖ ^ 2 = 1 / 2 := by nlinarith
  have hb : ‖v 1 2‖ ^ 2 = 1 / 2 := by nlinarith
  have hc : v 1 2 = 0 ∨ v 0 2 = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, hdiag]
      using horth 0 1 (by decide)
  rcases hc with hc | hc
  · rw [hc, norm_zero] at hb
    norm_num at hb
  · rw [hc, norm_zero] at ha
    norm_num at ha

end
end PositiveEinsteinFour

end OAI
