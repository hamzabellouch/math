import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingBielecki
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPotentialContinuity

namespace OAI

/-! # Uniform finite-slab bounds for the actual moving potential

The Bielecki construction applies on every finite interval.  Its initial-data
bound depends only on the slab length and the uniform bound on the profile,
not on the initial radius of the expanding torus.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem expandingTimeWeight_dist_le (T η : ℝ) (hη : 0 ≤ η)
    (u v : C(Icc (0 : ℝ) T, FourierL2)) :
    dist (expandingTimeWeight T η u) (expandingTimeWeight T η v) ≤
      Real.exp (η * T) * dist u v := by
  apply (ContinuousMap.dist_le (mul_nonneg (Real.exp_pos _).le dist_nonneg)).2
  intro t
  change dist (Real.exp (η * t) • u t) (Real.exp (η * t) • v t) ≤ _
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.2.2 hη))
    (by simpa only [dist_eq_norm] using
      (ContinuousMap.dist_apply_le_dist (f := u) (g := v) t))
    (norm_nonneg _) (Real.exp_pos _).le

/-- Every mild trajectory becomes a fixed point of the weighted Picard map. -/
theorem expandingBielecki_isFixedPt (a b k L T η : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (u : C(Icc (0 : ℝ) T, FourierL2))
    (hu : ∀ t : Icc (0 : ℝ) T, u t =
      expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F u)) :
    Function.IsFixedPt (expandingBieleckiPicard a b k L T η ha hk hL hT F u₀)
      (expandingTimeWeight T (-η) u) := by
  apply ContinuousMap.ext
  intro t
  change Real.exp (-η * t) •
    (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t
        (expandingReactionHistory T hT F
          (expandingTimeWeight T η (expandingTimeWeight T (-η) u)))) = _
  rw [expandingTimeWeight_cancel, ← hu t]
  rfl

/-- Dependence on the initial datum, uniformly in `L`, on an arbitrary finite slab. -/
theorem expandingMildSolution_finiteSlab_initialData_bound (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2))
    (u₀ v₀ : FourierL2) (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ t x y, ‖F (t, x) - F (t, y)‖ ≤ K * ‖x - y‖)
    (u v : C(Icc (0 : ℝ) T, FourierL2))
    (hu : ∀ t : Icc (0 : ℝ) T, u t =
      expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F u))
    (hv : ∀ t : Icc (0 : ℝ) T, v t =
      expandingFreeStep a b k L t ha hk hL t.2.1 v₀ +
        expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT F v)) :
    dist u v ≤ (K + 1) * Real.exp ((K + 1) * T) * dist u₀ v₀ := by
  let η := K + 1
  have hη : 0 < η := by dsimp [η]; linarith
  let P := expandingBieleckiPicard a b k L T η ha hk hL hT F u₀
  let Q := expandingBieleckiPicard a b k L T η ha hk hL hT F v₀
  let u' := expandingTimeWeight T (-η) u
  let v' := expandingTimeWeight T (-η) v
  have hP : ContractingWith ⟨K / η, div_nonneg hK hη.le⟩ P :=
    ⟨(div_lt_one hη).2 (by dsimp [η]; linarith), LipschitzWith.of_dist_le_mul
      (expandingBieleckiPicard_dist_le a b k L T η ha hk hL hT hη F u₀ K hK hF)⟩
  have huP : Function.IsFixedPt P u' :=
    expandingBielecki_isFixedPt a b k L T η ha hk hL hT F u₀ u hu
  have hvQ : Function.IsFixedPt Q v' :=
    expandingBielecki_isFixedPt a b k L T η ha hk hL hT F v₀ v hv
  have hd : dist u' v' ≤ dist u₀ v₀ / (1 - K / η) := by
    apply hP.dist_fixedPoint_fixedPoint_of_dist_le' Q huP hvQ
    intro z
    apply (ContinuousMap.dist_le dist_nonneg).2
    intro t
    change dist
      (Real.exp (-η * t) • (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL t
          (expandingReactionHistory T hT F (expandingTimeWeight T η z))))
      (Real.exp (-η * t) • (expandingFreeStep a b k L t ha hk hL t.2.1 v₀ +
        expandingDuhamel a b k L ha hk hL t
          (expandingReactionHistory T hT F (expandingTimeWeight T η z)))) ≤ _
    rw [dist_eq_norm, ← smul_sub, add_sub_add_right_eq_sub, ← map_sub,
      norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hfree : ‖expandingFreeStep a b k L t ha hk hL t.2.1 (u₀ - v₀)‖ ≤ dist u₀ v₀ := by
      apply (expandingFreeStep_norm_bound a b k L t ha hk hL t.2.1 _).trans
      rw [dist_eq_norm]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (by nlinarith [t.2.1]))
    exact (mul_le_mul_of_nonneg_left hfree (Real.exp_pos _).le).trans
      (mul_le_of_le_one_left dist_nonneg (Real.exp_le_one_iff.mpr (by
        nlinarith [t.2.1])))
  have hden : 1 - K / η = 1 / η := by
    apply (eq_div_iff hη.ne').2
    rw [sub_mul, div_mul_cancel₀ _ hη.ne', one_mul]
    dsimp [η]
    ring
  rw [hden, div_div_eq_mul_div, div_one] at hd
  have hout := expandingTimeWeight_dist_le T η hη.le u' v'
  have heq : dist u v ≤ Real.exp (η * T) * dist u' v' := by
    simpa only [u', v', expandingTimeWeight_cancel] using hout
  calc
    dist u v ≤ Real.exp (η * T) * dist u' v' := heq
    _ ≤ Real.exp (η * T) * (dist u₀ v₀ * η) :=
      mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
    _ = _ := by dsimp [η]; ring

/-- The actual odd-power linearization along a bounded profile has a unique
solution on every finite slab, at every permitted starting radius. -/
theorem existsUnique_expandingProfile_finiteSlab (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (q g : C(Icc (0 : ℝ) T, FourierL2)) (u₀ : FourierL2) (hq : ∀ t, ‖q t‖ ≤ R) :
    ∃! u : C(Icc (0 : ℝ) T, FourierL2), ∀ t : Icc (0 : ℝ) T,
      u t = expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL t
          (expandingReactionHistory T hT
            (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q g) u) := by
  obtain ⟨K, hK, hbound⟩ := exists_expandingProfileReaction_lipschitz a k ha ha1 hk m R hR
  exact existsUnique_expandingMildSolution_finiteSlab a b k L T ha hk hL hT _ u₀ K hK
    (hbound T (expandingRadiusCurve L T hL) q g hq)

end DefocusingNLS

end OAI
