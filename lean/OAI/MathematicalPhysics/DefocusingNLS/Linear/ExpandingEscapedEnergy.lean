import OAI.MathematicalPhysics.DefocusingNLS.Linear.SpacetimeObservationIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileUniformBound

namespace OAI

/-! # The full initial energy survives passage to a local physical limit -/

open Set Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] expandingProfileTrajectory expandingSpacetimePath

theorem expandingProfile_escaped_energy (a b k T Q M c C R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hc : 0 ≤ c) (hC : 0 ≤ C) (m : ℕ)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (q : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ n s, ‖q n s‖ ≤ Q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M)
    (henergy : ∀ n (s : Icc (0 : ℝ) T) (w : FourierL2),
      let l := expandingRadiusCurve (L n) T (hL n) s;
      -a * ‖expandingLowEnergy a k l.1 l.2 w‖ ^ 2 +
        (6 - 2 * a - k) * ‖expandingHighEnergy a k l.1 l.2 w‖ ^ 2 +
        2 * inner ℝ w (expandingLinearizedPotential a k l.1 ha ha1 hk l.2 m (q n s) w) ≤
      -c * ‖w‖ ^ 2 + C * ‖expandingPhysicalBall a k l.1 R ha ha1 hk l.2 w‖ ^ 2)
    (v : C(Icc (0 : ℝ) T × E, ℂ))
    (hv : Tendsto (fun n => expandingSpacetimePath a k (L n) T ha ha1 hk (hL n)
      (expandingProfileTrajectory a b k (L n) T ha ha1 hk (hL n) hT m Q hQ (q n) (hq n) (f n)))
      atTop (𝓝 v)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ‖expandingProfileTrajectory a b k (L n) T ha ha1 hk (hL n) hT m Q hQ (q n) (hq n)
        (f n) ⟨T, hT, le_rfl⟩‖ ^ 2 ≤ Real.exp (-c * T) * M ^ 2 +
        (∫ s in (0 : ℝ)..T, Real.exp (-c * (T - s)) *
          (C * ‖spacetimeBallPath T R v (projIcc 0 T hT s)‖ ^ 2)) + ε := by
  let S := fun n => expandingProfileTrajectory a b k (L n) T ha ha1 hk (hL n) hT
    m Q hQ (q n) (hq n) (f n)
  let F := fun n => expandingSpacetimePath a k (L n) T ha ha1 hk (hL n) (S n)
  obtain ⟨K, hK, hKb⟩ := exists_expandingProfileTrajectory_bound a b k ha ha1 hk m Q hQ
  let A := (K + 1) * Real.exp ((K + 1) * T) * M
  let B := expandingEmbeddingBound a k * A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B, expandingEmbeddingBound]; positivity
  have hSb (n : ℕ) (s : Icc (0 : ℝ) T) : ‖S n s‖ ≤ A :=
    ((ContinuousMap.norm_coe_le_norm (S n) s).trans
      (hKb (L n) T (hL n) hT (q n) (hq n) (f n))).trans
      (mul_le_mul_of_nonneg_left (hf n) (by positivity))
  have hI := tendsto_spacetime_observation_integral T R B c C hT hB hc hC F v
    (fun n s y => expandingSpacetimePath_norm_le a k (L n) T A ha ha1 hk (hL n) (S n)
      (hSb n) (s, y)) hv
  intro ε hε
  have hnear := (tendsto_order.mp hI).2 _ (lt_add_of_pos_right _ hε)
  filter_upwards [hnear] with n hn
  have he := expandingProfileTrajectory_observation_estimate a b k (L n) T ha ha1 hk
    (hL n) hT m Q hQ (q n) (hq n) c C R (henergy n) (f n) ⟨T, hT, le_rfl⟩
  have hi : (∫ s in (0 : ℝ)..T, Real.exp (-c * (T - s)) *
      (C * ‖spacetimeBallPath T R (F n) (projIcc 0 T hT s)‖ ^ 2)) =
      (∫ s in (0 : ℝ)..T, let p := projIcc 0 T hT s;
        Real.exp (-c * (T - s)) * (C * ‖expandingPhysicalBall a k
          (expandingRadius (L n) p) R ha ha1 hk
          ((hL n).trans (expandingRadius_ge (L n) p (hL n) p.2.1)) (S n p)‖ ^ 2)) := by
    simp only [F, spacetimeBallPath_expanding]
  rw [hi] at hn
  change ‖S n ⟨T, hT, le_rfl⟩‖ ^ 2 ≤ Real.exp (-c * T) * ‖f n‖ ^ 2 +
    (∫ s in (0 : ℝ)..T, let p := projIcc 0 T hT s;
      Real.exp (-c * (T - s)) * (C * ‖expandingPhysicalBall a k
        (expandingRadius (L n) p) R ha ha1 hk
        ((hL n).trans (expandingRadius_ge (L n) p (hL n) p.2.1)) (S n p)‖ ^ 2)) at he
  calc
    _ ≤ Real.exp (-c * T) * ‖f n‖ ^ 2 + _ := he
    _ ≤ Real.exp (-c * T) * M ^ 2 + _ := by
      gcongr
      exact hf n
    _ ≤ _ := by linarith

end DefocusingNLS

end OAI
