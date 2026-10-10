import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMildContraction
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDerivativeBounds
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingNonlinearityTransport
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPotentialContinuity

namespace OAI

/-! # Short-slab stability from the actual nonlinear mild defect

The Lipschitz estimate is required only along the two bounded trajectories.
No global Lipschitz hypothesis is imposed on the odd-power polynomial.
-/

open Set Metric

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem exists_expandingOddPower_lipschitz_on_ball (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (f g : FourierL2),
      ‖f‖ ≤ R → ‖g‖ ≤ R →
      ‖expandingOddPower a k L ha ha1 hk hL m f -
        expandingOddPower a k L ha ha1 hk hL m g‖ ≤ K * ‖f - g‖ := by
  obtain ⟨K, hK, hb⟩ := exists_expandingOddPower_two_jet_bound a k ha ha1 hk m R hR
  refine ⟨K, hK, ?_⟩
  intro L hL f g hf hg
  apply (convex_closedBall (0 : FourierL2) R).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (contDiff_expandingOddPower a k L ha ha1 hk hL m).differentiable (by simp) x)
  · intro x hx
    rw [← norm_iteratedFDeriv_one]
    exact hb L hL x (by simpa using hx) 1 (by omega)
  · simpa using hg
  · simpa using hf

noncomputable def expandingNonlinearReaction (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) :
    C((Icc (0 : ℝ) T) × FourierL2, FourierL2) where
  toFun p := (-Complex.I) • expandingOddPower a k (expandingRadiusCurve L T hL p.1).1
    ha ha1 hk (expandingRadiusCurve L T hL p.1).2 m p.2
  continuous_toFun := ((continuous_expandingOddPower_scale a k ha ha1 hk m).comp
    (((expandingRadiusCurve L T hL).continuous.comp continuous_fst).prodMk continuous_snd)).const_smul
      (-Complex.I)

theorem expandingPicard_pair_dist_le (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (K : ℝ) (hK : 0 ≤ K) (u v : C(Icc (0 : ℝ) T, FourierL2))
    (hF : ∀ t, ‖F (t, u t) - F (t, v t)‖ ≤ K * ‖u t - v t‖) :
    dist (expandingPicard a b k L T ha hk hL hT F u₀ u)
      (expandingPicard a b k L T ha hk hL hT F u₀ v) ≤ T * K * dist u v := by
  apply (ContinuousMap.dist_le (by positivity)).2
  intro t
  let ru := expandingReactionHistory T hT F u
  let rv := expandingReactionHistory T hT F v
  have hru : Continuous ru := continuous_expandingReactionHistory T hT F u
  have hrv : Continuous rv := continuous_expandingReactionHistory T hT F v
  have hb : ∀ s ∈ Icc (0 : ℝ) t, ‖ru s - rv s‖ ≤ K * dist u v := by
    intro s _
    exact (hF (projIcc 0 T hT s)).trans (mul_le_mul_of_nonneg_left
      (by simpa only [dist_eq_norm] using
        ContinuousMap.dist_apply_le_dist (f := u) (g := v) (projIcc 0 T hT s)) hK)
  have hbound := expandingDuhamel_norm_le_mul a b k L ha hk hL t
    (K * dist u v) t.2.1 (fun s => ru s - rv s) (hru.sub hrv).continuousOn hb
  change dist
    (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ + expandingDuhamel a b k L ha hk hL t ru)
    (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ + expandingDuhamel a b k L ha hk hL t rv) ≤ _
  rw [dist_add_left, dist_eq_norm,
    ← expandingDuhamel_sub a b k L ha hk hL t ru rv hru.continuousOn hrv.continuousOn]
  apply hbound.trans
  calc
    (t : ℝ) * (K * dist u v) ≤ T * (K * dist u v) :=
      mul_le_mul_of_nonneg_right t.2.2 (mul_nonneg hK dist_nonneg)
    _ = T * K * dist u v := by ring

theorem expandingPicard_initial_dist_le (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ v₀ : FourierL2)
    (v : C(Icc (0 : ℝ) T, FourierL2)) :
    dist (expandingPicard a b k L T ha hk hL hT F u₀ v)
      (expandingPicard a b k L T ha hk hL hT F v₀ v) ≤ dist u₀ v₀ := by
  apply (ContinuousMap.dist_le dist_nonneg).2
  intro t
  change dist
    (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ + _)
    (expandingFreeStep a b k L t ha hk hL t.2.1 v₀ + _) ≤ _
  rw [dist_add_right, dist_eq_norm, ← map_sub]
  apply (expandingFreeStep_norm_bound a b k L t ha hk hL t.2.1 (u₀ - v₀)).trans
  rw [dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (by nlinarith [t.2.1]))

theorem expandingMild_residual_stability (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ v₀ : FourierL2)
    (K : ℝ) (hK : 0 ≤ K) (hTK : T * K < 1)
    (u v : C(Icc (0 : ℝ) T, FourierL2))
    (hF : ∀ t, ‖F (t, u t) - F (t, v t)‖ ≤ K * ‖u t - v t‖)
    (hu : u = expandingPicard a b k L T ha hk hL hT F u₀ u)
    (ε : ℝ) (hε : dist v (expandingPicard a b k L T ha hk hL hT F v₀ v) ≤ ε) :
    dist u v ≤ (dist u₀ v₀ + ε) / (1 - T * K) := by
  have hpair := expandingPicard_pair_dist_le a b k L T ha hk hL hT F u₀ K hK u v hF
  have hinit : dist (expandingPicard a b k L T ha hk hL hT F u₀ v)
      (expandingPicard a b k L T ha hk hL hT F v₀ v) ≤ dist u₀ v₀ :=
    expandingPicard_initial_dist_le a b k L T ha hk hL hT F u₀ v₀ v
  have hdist : dist u v ≤ T * K * dist u v + dist u₀ v₀ + ε := by
    calc
      dist u v = dist (expandingPicard a b k L T ha hk hL hT F u₀ u) v := by rw [← hu]
      _ ≤ dist (expandingPicard a b k L T ha hk hL hT F u₀ u)
          (expandingPicard a b k L T ha hk hL hT F u₀ v) +
        dist (expandingPicard a b k L T ha hk hL hT F u₀ v) v := dist_triangle _ _ _
      _ ≤ T * K * dist u v + (dist u₀ v₀ + ε) := by
        apply add_le_add hpair
        exact (dist_triangle _ (expandingPicard a b k L T ha hk hL hT F v₀ v) _).trans
          (add_le_add hinit (by simpa only [dist_comm] using hε))
      _ = _ := by ring
  apply (le_div_iff₀ (by linarith : 0 < 1 - T * K)).mpr
  nlinarith

/-- The short-time stability constant for the actual odd-power equation is
independent of the starting scale. -/
theorem exists_expandingNonlinear_residual_stability (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T), T * K < 1 →
      ∀ (u v : C(Icc (0 : ℝ) T, FourierL2)),
      (∀ t, ‖u t‖ ≤ R) → (∀ t, ‖v t‖ ≤ R) → ∀ (u₀ v₀ : FourierL2) (ε : ℝ),
      u = expandingPicard a b k L T ha hk hL hT
        (expandingNonlinearReaction a k L T ha ha1 hk hL m) u₀ u →
      dist v (expandingPicard a b k L T ha hk hL hT
        (expandingNonlinearReaction a k L T ha ha1 hk hL m) v₀ v) ≤ ε →
      dist u v ≤ (dist u₀ v₀ + ε) / (1 - T * K) := by
  obtain ⟨K, hK, hb⟩ := exists_expandingOddPower_lipschitz_on_ball a k ha ha1 hk m R hR
  refine ⟨K, hK, ?_⟩
  intro L T hL hT hTK u v huR hvR u₀ v₀ ε hu hv
  apply expandingMild_residual_stability a b k L T ha hk hL hT _ u₀ v₀ K hK hTK u v
    _ hu ε hv
  intro t
  change ‖(-Complex.I) • expandingOddPower a k (expandingRadiusCurve L T hL t).1
      ha ha1 hk (expandingRadiusCurve L T hL t).2 m (u t) -
    (-Complex.I) • expandingOddPower a k (expandingRadiusCurve L T hL t).1
      ha ha1 hk (expandingRadiusCurve L T hL t).2 m (v t)‖ ≤ _
  rw [← smul_sub, norm_smul]
  simp only [norm_neg, Complex.norm_I, one_mul]
  exact hb _ (expandingRadiusCurve L T hL t).2 _ _ (huR t) (hvR t)

end DefocusingNLS

end OAI
