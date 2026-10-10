import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightedLocal

namespace OAI

/-! # Finite-step dependence using only the two actual trajectories

The odd-power reaction need not be globally Lipschitz.  A uniform bound on
its difference along the two solutions gives the required finite-step
Lipschitz estimate for their initial data.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem expandingBieleckiPicard_initial_dist_le (a b k L T η : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T) (hη : 0 ≤ η)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ v₀ : FourierL2)
    (z : C(Icc (0 : ℝ) T, FourierL2)) :
    dist (expandingBieleckiPicard a b k L T η ha hk hL hT F u₀ z)
      (expandingBieleckiPicard a b k L T η ha hk hL hT F v₀ z) ≤ dist u₀ v₀ := by
  apply (ContinuousMap.dist_le dist_nonneg).2
  intro t
  change dist (Real.exp (-η * t) •
      (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ + _))
    (Real.exp (-η * t) •
      (expandingFreeStep a b k L t ha hk hL t.2.1 v₀ + _)) ≤ _
  rw [dist_eq_norm, ← smul_sub, add_sub_add_right_eq_sub, ← map_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hb := expandingFreeStep_norm_bound a b k L t ha hk hL t.2.1 (u₀ - v₀)
  have hfree : Real.exp (-a * (t : ℝ) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [t.2.1])
  have hweight : Real.exp (-η * (t : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [t.2.1])
  rw [dist_eq_norm]
  exact (mul_le_mul_of_nonneg_left (hb.trans
    (mul_le_of_le_one_left (norm_nonneg _) hfree)) (Real.exp_pos _).le).trans
      (mul_le_of_le_one_left (norm_nonneg _) hweight)

theorem expandingMild_finiteSlab_local_data_bound (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ v₀ : FourierL2)
    (K : ℝ) (hK : 0 ≤ K) (u v : C(Icc (0 : ℝ) T, FourierL2))
    (hF : ∀ t, ‖F (t, u t) - F (t, v t)‖ ≤ K * ‖u t - v t‖)
    (hu : u = expandingPicard a b k L T ha hk hL hT F u₀ u)
    (hv : v = expandingPicard a b k L T ha hk hL hT F v₀ v) :
    dist u v ≤ Real.exp ((K + 1) * T) * ((K + 1) * dist u₀ v₀) := by
  let η := K + 1
  have hη : 0 < η := by dsimp [η]; linarith
  let u' := expandingTimeWeight T (-η) u
  let v' := expandingTimeWeight T (-η) v
  let P := expandingBieleckiPicard a b k L T η ha hk hL hT F u₀
  let Q := expandingBieleckiPicard a b k L T η ha hk hL hT F v₀
  have huP : P u' = u' := by
    apply expandingBielecki_isFixedPt a b k L T η ha hk hL hT F u₀ u
    intro t
    exact congrArg (fun w : C(Icc (0 : ℝ) T, FourierL2) => w t) hu
  have hvQ : Q v' = v' := by
    apply expandingBielecki_isFixedPt a b k L T η ha hk hL hT F v₀ v
    intro t
    exact congrArg (fun w : C(Icc (0 : ℝ) T, FourierL2) => w t) hv
  have hp := expandingBieleckiPicard_pair_dist_le a b k L T η ha hk hL hT hη F u₀ K hK u' v'
    (by simpa only [u', v', expandingTimeWeight_cancel] using hF)
  have hq := expandingBieleckiPicard_initial_dist_le a b k L T η ha hk hL hT hη.le F u₀ v₀ v'
  have hi : dist u' v' ≤ K / η * dist u' v' + dist u₀ v₀ := by
    calc
      dist u' v' = dist (P u') (Q v') := by rw [huP, hvQ]
      _ ≤ dist (P u') (P v') + dist (P v') (Q v') := dist_triangle _ _ _
      _ ≤ _ := add_le_add hp hq
  have hd : dist u' v' ≤ η * dist u₀ v₀ := by
    have hm := mul_le_mul_of_nonneg_right hi hη.le
    have he : (K / η * dist u' v' + dist u₀ v₀) * η =
        K * dist u' v' + η * dist u₀ v₀ := by
      calc
        _ = (K / η * η) * dist u' v' + η * dist u₀ v₀ := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hη.ne']
    rw [he] at hm
    dsimp [η] at hm ⊢
    nlinarith
  have he := expandingTimeWeight_dist_le T η hη.le u' v'
  have hout : dist u v ≤ Real.exp (η * T) * dist u' v' := by
    simpa only [u', v', expandingTimeWeight_cancel] using he
  exact hout.trans (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le)

end DefocusingNLS

end OAI
