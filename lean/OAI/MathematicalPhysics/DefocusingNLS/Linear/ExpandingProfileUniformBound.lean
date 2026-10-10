import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfilePropagator

namespace OAI

/-! # The constructed propagator has one norm bound for every starting radius -/

namespace DefocusingNLS

theorem exists_expandingProfileTrajectory_bound (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T)
      (q : C(Set.Icc (0 : ℝ) T, FourierL2)) (hq : ∀ t, ‖q t‖ ≤ Q) (f : FourierL2),
      ‖expandingProfileTrajectory a b k L T ha ha1 hk hL hT m Q hQ q hq f‖ ≤
        (K + 1) * Real.exp ((K + 1) * T) * ‖f‖ := by
  obtain ⟨K, hK, hb⟩ := exists_expandingProfile_propagator a b k ha ha1 hk m Q hQ
  refine ⟨K, hK, fun L T hL hT q hq f => ?_⟩
  obtain ⟨U, hU, hUb⟩ := hb L T hL hT q hq
  have he := expandingProfileTrajectory_unique a b k L T ha ha1 hk hL hT m Q hQ q hq f (U f) (hU f)
  rw [← he]
  exact (U.le_opNorm f).trans (mul_le_mul_of_nonneg_right hUb (norm_nonneg f))

end DefocusingNLS

end OAI
