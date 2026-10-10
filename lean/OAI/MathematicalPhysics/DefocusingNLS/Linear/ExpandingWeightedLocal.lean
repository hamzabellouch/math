import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileResponse

namespace OAI

/-! # Local estimates for the exponentially weighted Picard map

The Lipschitz estimate is needed only along the two paths being compared.
This permits the polynomial nonlinearity to be used on a bounded path ball
without replacing it by a globally Lipschitz map.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem expandingBieleckiPicard_pair_dist_le (a b k L T η : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T) (hη : 0 < η)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (K : ℝ) (hK : 0 ≤ K) (u v : C(Icc (0 : ℝ) T, FourierL2))
    (hF : ∀ t,
      ‖F (t, expandingTimeWeight T η u t) - F (t, expandingTimeWeight T η v t)‖ ≤
        K * ‖expandingTimeWeight T η u t - expandingTimeWeight T η v t‖) :
    dist (expandingBieleckiPicard a b k L T η ha hk hL hT F u₀ u)
      (expandingBieleckiPicard a b k L T η ha hk hL hT F u₀ v) ≤ K / η * dist u v := by
  apply (ContinuousMap.dist_le (mul_nonneg (div_nonneg hK hη.le) dist_nonneg)).2
  intro t
  let ru := expandingBieleckiHistory T η hT F u
  let rv := expandingBieleckiHistory T η hT F v
  have hru : Continuous ru := continuous_expandingBieleckiHistory T η hT F u
  have hrv : Continuous rv := continuous_expandingBieleckiHistory T η hT F v
  have hbound : ∀ τ ∈ Icc (0 : ℝ) t, ‖ru τ - rv τ‖ ≤ (K * dist u v) * Real.exp (η * τ) := by
    intro τ hτ
    let τ' : Icc (0 : ℝ) T := ⟨τ, hτ.1, hτ.2.trans t.2.2⟩
    have hτT : τ ∈ Icc 0 T := τ'.2
    have hnorm : ‖expandingTimeWeight T η u (projIcc 0 T hT τ) -
        expandingTimeWeight T η v (projIcc 0 T hT τ)‖ ≤
        Real.exp (η * τ) * dist u v := by
      rw [projIcc_of_mem _ hτT]
      change ‖Real.exp (η * τ) • u τ' - Real.exp (η * τ) • v τ'‖ ≤ _
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using ContinuousMap.dist_apply_le_dist (f := u) (g := v) τ')
        (Real.exp_pos _).le
    change ‖F (projIcc 0 T hT τ, _) - F (projIcc 0 T hT τ, _)‖ ≤ _
    calc
      _ ≤ K * ‖expandingTimeWeight T η u (projIcc 0 T hT τ) -
          expandingTimeWeight T η v (projIcc 0 T hT τ)‖ := hF _
      _ ≤ K * (Real.exp (η * τ) * dist u v) := mul_le_mul_of_nonneg_left hnorm hK
      _ = _ := by ring
  have hb := expandingDuhamel_weighted_norm_le a b k L η t (K * dist u v)
    ha hk hL hη t.2.1 (mul_nonneg hK dist_nonneg) (fun τ => ru τ - rv τ) hbound
  change dist
    (Real.exp (-η * t) • (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t ru))
    (Real.exp (-η * t) • (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t rv)) ≤ _
  rw [dist_eq_norm, ← smul_sub, add_sub_add_left_eq_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),
    ← expandingDuhamel_sub a b k L ha hk hL t ru rv hru.continuousOn hrv.continuousOn]
  exact hb.trans_eq (by ring)

@[simp] theorem expandingTimeWeight_zero (T η : ℝ) :
    expandingTimeWeight T η (0 : C(Icc (0 : ℝ) T, FourierL2)) = 0 := by
  apply ContinuousMap.ext
  intro t
  change Real.exp (η * t) • (0 : FourierL2) = 0
  exact smul_zero _

theorem expandingBieleckiPicard_zero_bound (a b k L T η : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T) (hη : 0 < η)
    (F : C((Icc (0 : ℝ) T) × FourierL2, FourierL2)) (u₀ : FourierL2)
    (ε : ℝ) (hε : 0 ≤ ε) (hF : ∀ t, ‖F (t, 0)‖ ≤ ε) :
    ‖expandingBieleckiPicard a b k L T η ha hk hL hT F u₀ 0‖ ≤ ‖u₀‖ + ε / η := by
  apply (ContinuousMap.norm_le _ (add_nonneg (norm_nonneg _) (div_nonneg hε hη.le))).2
  intro t
  change ‖Real.exp (-η * t) •
    (expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
      expandingDuhamel a b k L ha hk hL t
        (expandingReactionHistory T hT F (expandingTimeWeight T η 0)))‖ ≤ _
  rw [expandingTimeWeight_zero, smul_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_left
      (expandingFreeStep_norm_bound a b k L t ha hk hL t.2.1 u₀) (Real.exp_pos _).le).trans
    have hfree : Real.exp (-a * (t : ℝ) / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [t.2.1])
    have hweight : Real.exp (-η * (t : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [t.2.1])
    exact (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) hfree) (Real.exp_pos _).le).trans
        (mul_le_of_le_one_left (norm_nonneg _) hweight)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply expandingDuhamel_weighted_norm_le a b k L η t ε ha hk hL hη t.2.1 hε
    intro τ hτ
    change ‖F (projIcc 0 T hT τ, 0)‖ ≤ _
    exact (hF _).trans (le_mul_of_one_le_right hε
      (Real.one_le_exp_iff.mpr (mul_nonneg hη.le hτ.1)))

end DefocusingNLS

end OAI
