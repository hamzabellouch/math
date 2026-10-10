import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileDifference

namespace OAI

/-! # Lipschitz remainder after a fixed nonlinear step

Subtracting the homogeneous linearized difference leaves only the difference
of the quadratic sources.  The resulting constant depends on the fixed step
length and profile bound, and is uniform in the starting torus radius.
-/

open Set

namespace DefocusingNLS

theorem exists_expandingNonlinearStep_difference_error (a b k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hM : 0 ≤ M)
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L)
      (q g u v w : C(Icc (0 : ℝ) M, FourierL2)) (u₀ v₀ : FourierL2) (d : ℝ),
      0 ≤ d → d ≤ 1 → (∀ t, ‖q t‖ ≤ R) → (∀ t, ‖u t‖ ≤ d) → (∀ t, ‖v t‖ ≤ d) →
      u = expandingPicard a b k L M ha hk hL hM
        (expandingPerturbationReaction a k L M ha ha1 hk hL m q g) u₀ u →
      v = expandingPicard a b k L M ha hk hL hM
        (expandingPerturbationReaction a k L M ha ha1 hk hL m q g) v₀ v →
      (∀ t : Icc (0 : ℝ) M, w t =
        expandingFreeStep a b k L t ha hk hL t.2.1 (u₀ - v₀) +
          expandingDuhamel a b k L ha hk hL t
            (expandingReactionHistory M hM
              (expandingProfileReaction a k M ha ha1 hk m (expandingRadiusCurve L M hL) q 0) w)) →
      dist (u - v) w ≤ C * d * dist u₀ v₀ := by
  obtain ⟨A, hA, hresponse⟩ := exists_expandingProfile_response_bound a b k ha ha1 hk m R hR
  obtain ⟨B, hB, hreaction⟩ := exists_expandingPerturbationReaction_local_lipschitz
    a k ha ha1 hk m R hR
  obtain ⟨D, hD, hsource⟩ := exists_expandingPerturbationSource_lipschitz a k ha ha1 hk m R hR
  let C := Real.exp ((A + 1) * M) * (2 * D) * (Real.exp ((B + 1) * M) * (B + 1))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro L hL q g u v w u₀ v₀ d hd hd1 hq hu_bound hv_bound hu hv hw
  let F := expandingPerturbationReaction a k L M ha ha1 hk hL m q g
  have hdist : dist u v ≤ Real.exp ((B + 1) * M) * ((B + 1) * dist u₀ v₀) :=
    expandingMild_finiteSlab_local_data_bound a b k L M ha hk hL hM F u₀ v₀ B hB u v
      (fun t => hreaction L M hL q g hq t (u t) (v t)
        ((hu_bound t).trans hd1) ((hv_bound t).trans hd1)) hu hv
  let r := expandingPerturbationSource a k L M ha ha1 hk hL m q g u -
    expandingPerturbationSource a k L M ha ha1 hk hL m q g v
  let G := (2 * D * d) * dist u v
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hr : ∀ t, ‖r t‖ ≤ G := by
    intro t
    exact hsource L M hL q g u v d hd hd1 hq hu_bound hv_bound t
  have hp := hresponse L M hL hM q r (u₀ - v₀) G hG hq hr (u - v) w
    (expandingPerturbation_difference_linear_mild a b k L M ha ha1 hk hL hM m
      q g u v u₀ v₀ hu hv) hw
  calc
    dist (u - v) w ≤ Real.exp ((A + 1) * M) * G := hp
    _ ≤ Real.exp ((A + 1) * M) *
        ((2 * D * d) * (Real.exp ((B + 1) * M) * ((B + 1) * dist u₀ v₀))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdist (by positivity)) (Real.exp_pos _).le
    _ = C * d * dist u₀ v₀ := by dsimp [C]; ring

end DefocusingNLS

end OAI
