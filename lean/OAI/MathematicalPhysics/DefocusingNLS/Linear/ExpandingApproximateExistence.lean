import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingResidualStability

namespace OAI

/-! # Exact trajectories in a neighborhood of an approximate mild solution

The contraction is restricted to a closed ball of paths, so only the actual
local Lipschitz estimate for the polynomial reaction is used.
-/

open Set Metric

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem expandingMildSolution_initial (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (u : C(Icc (0 : ℝ) T, FourierL2))
    (hu : u = expandingPicard a b k L T ha hk hL hT F u₀ u) :
    u ⟨0, le_rfl, hT⟩ = u₀ := by
  have h := congrArg (fun v : C(Icc (0 : ℝ) T, FourierL2) => v ⟨0, le_rfl, hT⟩) hu
  simpa [expandingPicard, expandingDuhamel] using h

theorem expandingMild_neighborhood_unique (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (u v : C(Icc (0 : ℝ) T, FourierL2)) (K : ℝ) (hK : 0 ≤ K) (hTK : T * K < 1)
    (hF : ∀ t, ‖F (t, u t) - F (t, v t)‖ ≤ K * ‖u t - v t‖)
    (hu : u = expandingPicard a b k L T ha hk hL hT F u₀ u)
    (hv : v = expandingPicard a b k L T ha hk hL hT F u₀ v) : u = v := by
  have h := expandingPicard_pair_dist_le a b k L T ha hk hL hT F u₀ K hK u v hF
  rw [← hu, ← hv] at h
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := u) (y := v)]

theorem exists_expandingMild_near_approximation (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (v : C(Icc (0 : ℝ) T, FourierL2)) (ρ K ε : ℝ)
    (hρ : 0 ≤ ρ) (hK : 0 ≤ K) (hTK : T * K < 1)
    (hF : ∀ u ∈ closedBall v ρ, ∀ w ∈ closedBall v ρ, ∀ t,
      ‖F (t, u t) - F (t, w t)‖ ≤ K * ‖u t - w t‖)
    (hdef : dist v (expandingPicard a b k L T ha hk hL hT F u₀ v) ≤ ε)
    (hsmall : ε ≤ (1 - T * K) * ρ) :
    ∃ u : C(Icc (0 : ℝ) T, FourierL2),
      u = expandingPicard a b k L T ha hk hL hT F u₀ u ∧
      dist u v ≤ ρ ∧ dist u v ≤ ε / (1 - T * K) := by
  let P := expandingPicard a b k L T ha hk hL hT F u₀
  have hv : v ∈ closedBall v ρ := by simpa using hρ
  have hmap : MapsTo P (closedBall v ρ) (closedBall v ρ) := by
    intro u hu
    have hp := expandingPicard_pair_dist_le a b k L T ha hk hL hT F u₀ K hK u v
      (hF u hu v hv)
    have hd : dist u v ≤ ρ := hu
    change dist (P u) v ≤ ρ
    calc
      dist (P u) v ≤ dist (P u) (P v) + dist (P v) v := dist_triangle _ _ _
      _ ≤ T * K * dist u v + ε := add_le_add hp (by simpa only [dist_comm] using hdef)
      _ ≤ ρ := by nlinarith [mul_le_mul_of_nonneg_left hd (mul_nonneg hT hK)]
  have hcontract : ContractingWith ⟨T * K, mul_nonneg hT hK⟩
      (hmap.restrict P (closedBall v ρ) (closedBall v ρ)) := by
    refine ⟨hTK, LipschitzWith.of_dist_le_mul ?_⟩
    intro u w
    exact expandingPicard_pair_dist_le a b k L T ha hk hL hT F u₀ K hK u.1 w.1
      (hF u.1 u.2 w.1 w.2)
  obtain ⟨u, hu, hfix, _⟩ := hcontract.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hv (edist_ne_top _ _)
  have heq : u = P u := hfix.symm
  refine ⟨u, heq, hu, ?_⟩
  have hb := expandingMild_residual_stability a b k L T ha hk hL hT F u₀ u₀
    K hK hTK u v (hF u hu v hv) heq ε hdef
  simpa only [dist_self, zero_add] using hb

/-- The local existence radius and Lipschitz constant are independent of the
starting torus scale. The reaction is the actual odd-power nonlinearity. -/
theorem exists_expandingNonlinear_near_approximation (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (R ρ : ℝ) (hR : 0 ≤ R) (hρ : 0 ≤ ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T), T * K < 1 →
      ∀ (v : C(Icc (0 : ℝ) T, FourierL2)), (∀ t, ‖v t‖ ≤ R) →
      ∀ (u₀ : FourierL2) (ε : ℝ),
      dist v (expandingPicard a b k L T ha hk hL hT
        (expandingNonlinearReaction a k L T ha ha1 hk hL m) u₀ v) ≤ ε →
      ε ≤ (1 - T * K) * ρ →
      ∃ u : C(Icc (0 : ℝ) T, FourierL2),
        u = expandingPicard a b k L T ha hk hL hT
          (expandingNonlinearReaction a k L T ha ha1 hk hL m) u₀ u ∧
        dist u v ≤ ρ ∧ dist u v ≤ ε / (1 - T * K) := by
  obtain ⟨K, hK, hb⟩ := exists_expandingOddPower_lipschitz_on_ball a k ha ha1 hk m
    (R + ρ) (add_nonneg hR hρ)
  refine ⟨K, hK, ?_⟩
  intro L T hL hT hTK v hv u₀ ε hdef hsmall
  apply exists_expandingMild_near_approximation a b k L T ha hk hL hT _ u₀ v
    ρ K ε hρ hK hTK _ hdef hsmall
  intro u hu w hw t
  have hnorm (z : C(Icc (0 : ℝ) T, FourierL2)) (hz : z ∈ closedBall v ρ) :
      ‖z t‖ ≤ R + ρ := by
    have hd := ContinuousMap.dist_apply_le_dist (f := z) (g := v) t
    have hz' : dist z v ≤ ρ := hz
    calc
      ‖z t‖ ≤ ‖v t‖ + ‖z t - v t‖ := by
        have he : v t + (z t - v t) = z t := by abel
        simpa only [he] using norm_add_le (v t) (z t - v t)
      _ ≤ R + ρ := add_le_add (hv t) (by simpa only [dist_eq_norm] using hd.trans hz')
  change ‖(-Complex.I) • expandingOddPower a k (expandingRadiusCurve L T hL t).1
      ha ha1 hk (expandingRadiusCurve L T hL t).2 m (u t) -
    (-Complex.I) • expandingOddPower a k (expandingRadiusCurve L T hL t).1
      ha ha1 hk (expandingRadiusCurve L T hL t).2 m (w t)‖ ≤ _
  rw [← smul_sub, norm_smul]
  simp only [norm_neg, Complex.norm_I, one_mul]
  exact hb _ (expandingRadiusCurve L T hL t).2 _ _ (hnorm u hu) (hnorm w hw)

end DefocusingNLS

end OAI
