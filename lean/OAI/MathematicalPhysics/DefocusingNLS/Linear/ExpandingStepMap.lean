import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingStepLipschitz
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingStepExistence

namespace OAI

/-! # The actual nonlinear endpoint map and its small Lipschitz remainder

For a bounded profile and small forcing, this constructs the nonlinear
step map on one uniform initial-data ball. Its linear part is the actual
profile-linearized evolution, with the quantitative remainder estimates
required in the manuscript's nonlinear iteration.
-/

open Set

namespace DefocusingNLS

theorem expandingPerturbation_unique_of_small (a b k L M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hM : 0 ≤ M)
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) (q g u v : C(Icc (0 : ℝ) M, FourierL2))
    (v₀ : FourierL2) (hq : ∀ t, ‖q t‖ ≤ R) (hu_bound : ‖u‖ ≤ 1) (hv_bound : ‖v‖ ≤ 1)
    (hu : u = expandingPicard a b k L M ha hk hL hM
      (expandingPerturbationReaction a k L M ha ha1 hk hL m q g) v₀ u)
    (hv : v = expandingPicard a b k L M ha hk hL hM
      (expandingPerturbationReaction a k L M ha ha1 hk hL m q g) v₀ v) : u = v := by
  obtain ⟨K, hK, hlip⟩ := exists_expandingPerturbationReaction_local_lipschitz
    a k ha ha1 hk m R hR
  have hb := expandingMild_finiteSlab_local_data_bound a b k L M ha hk hL hM
    (expandingPerturbationReaction a k L M ha ha1 hk hL m q g) v₀ v₀ K hK u v
    (fun t => hlip L M hL q g hq t (u t) (v t)
      ((ContinuousMap.norm_coe_le_norm u t).trans hu_bound)
      ((ContinuousMap.norm_coe_le_norm v t).trans hv_bound)) hu hv
  simp only [dist_self, mul_zero] at hb
  exact dist_eq_zero.mp (le_antisymm hb dist_nonneg)

theorem exists_expandingNonlinear_stepMap (a b k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hM : 0 ≤ M)
    (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (L : ℝ) (hL : 1 ≤ L)
      (q g : C(Icc (0 : ℝ) M, FourierL2)) (G : ℝ),
      0 ≤ G → G ≤ δ → (hq : ∀ t, ‖q t‖ ≤ R) → (∀ t, ‖g t‖ ≤ G) →
      ∃ (V : {f : FourierL2 // ‖f‖ ≤ δ} → C(Icc (0 : ℝ) M, FourierL2))
        (h : {f : FourierL2 // ‖f‖ ≤ δ} → FourierL2),
        (∀ f, V f = expandingPicard a b k L M ha hk hL hM
          (expandingPerturbationReaction a k L M ha ha1 hk hL m q g) f.1 (V f)) ∧
        (∀ f, ‖V f‖ ≤ C * (‖f.1‖ + G)) ∧
        (∀ f, V f ⟨M, hM, le_rfl⟩ =
          expandingProfileTrajectory a b k L M ha ha1 hk hL hM m R hR q hq f.1
            ⟨M, hM, le_rfl⟩ + h f) ∧
        (∀ z, z.1 = 0 → ‖h z‖ ≤ C * G) ∧
        (∀ (d : ℝ), 0 < d → d ≤ δ → ∀ f j,
          ‖f.1‖ ≤ d → ‖j.1‖ ≤ d → ‖h f - h j‖ ≤ C * (d + G) * ‖f.1 - j.1‖) := by
  obtain ⟨δ, A, hδ, hA, hAδ, hexists⟩ :=
    exists_expandingPerturbation_step_radius a b k M ha ha1 hk hM m R hR
  obtain ⟨B, hB, herror⟩ := exists_expandingNonlinearStep_difference_error
    a b k M ha ha1 hk hM m R hR
  let C := A + B * A
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; nlinarith [mul_nonneg hB hA.le]
  have hBC : B * A ≤ C := by dsimp [C]; linarith
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro L hL q g G hG hGδ hq hg
  choose V hV hV_bound hV_half using
    (fun f : {f : FourierL2 // ‖f‖ ≤ δ} => hexists L hL q g G hG hGδ hq hg f.1 f.2)
  let S := expandingProfileTrajectory a b k L M ha ha1 hk hL hM m R hR q hq
  let h : {f : FourierL2 // ‖f‖ ≤ δ} → FourierL2 :=
    fun f => V f ⟨M, hM, le_rfl⟩ - S f.1 ⟨M, hM, le_rfl⟩
  refine ⟨V, h, hV, ?_, ?_, ?_, ?_⟩
  · intro f
    exact (hV_bound f).trans (mul_le_mul_of_nonneg_right hAC (by positivity))
  · intro f
    dsimp [h, S]
    abel
  · intro z hz0
    have hz : S z.1 = 0 := by
      rw [hz0]
      exact expandingProfileTrajectory_zero a b k L M ha ha1 hk hL hM m R hR q hq
    change ‖V z ⟨M, hM, le_rfl⟩ - S z.1 ⟨M, hM, le_rfl⟩‖ ≤ C * G
    rw [hz]
    simp only [ContinuousMap.zero_apply, sub_zero]
    apply (ContinuousMap.norm_coe_le_norm (V z) _).trans
    exact (hV_bound z).trans (by
      simpa only [hz0, norm_zero, zero_add] using
        mul_le_mul_of_nonneg_right hAC hG)
  · intro d hd hdδ f j hf hj
    let D := A * (d + G)
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hD1 : D ≤ 1 := by
      have hl := mul_le_mul_of_nonneg_left (add_le_add hdδ hGδ) hA.le
      dsimp [D]
      nlinarith
    have hf_bound : ∀ t, ‖V f t‖ ≤ D := by
      intro t
      exact (ContinuousMap.norm_coe_le_norm (V f) t).trans
        ((hV_bound f).trans (mul_le_mul_of_nonneg_left (add_le_add hf le_rfl) hA.le))
    have hj_bound : ∀ t, ‖V j t‖ ≤ D := by
      intro t
      exact (ContinuousMap.norm_coe_le_norm (V j) t).trans
        ((hV_bound j).trans (mul_le_mul_of_nonneg_left (add_le_add hj le_rfl) hA.le))
    have hb := herror L hL q g (V f) (V j) (S (f.1 - j.1)) f.1 j.1 D hD hD1
      hq hf_bound hj_bound (hV f) (hV j)
      (expandingProfileTrajectory_eq a b k L M ha ha1 hk hL hM m R hR q hq (f.1 - j.1))
    have he : h f - h j = (V f - V j) ⟨M, hM, le_rfl⟩ -
        S (f.1 - j.1) ⟨M, hM, le_rfl⟩ := by
      dsimp [h, S]
      rw [expandingProfileTrajectory_sub]
      simp only [ContinuousMap.sub_apply]
      abel
    rw [he, ← dist_eq_norm]
    apply (ContinuousMap.dist_apply_le_dist (f := V f - V j) (g := S (f.1 - j.1)) _).trans
    apply hb.trans
    rw [dist_eq_norm]
    dsimp [D]
    calc
      B * (A * (d + G)) * ‖f.1 - j.1‖ = (B * A) * ((d + G) * ‖f.1 - j.1‖) := by ring
      _ ≤ C * ((d + G) * ‖f.1 - j.1‖) := mul_le_mul_of_nonneg_right hBC
        (mul_nonneg (add_nonneg hd.le hG) (norm_nonneg (f.1 - j.1)))
      _ = C * (d + G) * ‖f.1 - j.1‖ := by ring

end DefocusingNLS

end OAI
