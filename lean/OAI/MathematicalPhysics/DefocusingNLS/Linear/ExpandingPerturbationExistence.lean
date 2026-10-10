import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFiniteLocalExistence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPerturbationReaction
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingResidualStability

namespace OAI

/-! # Small nonlinear perturbations on an arbitrary fixed step

The nonlinear reaction is the actual odd-power increment around a bounded
profile.  Its local Lipschitz constant and its admissible forcing size are
uniform in the starting torus radius.
-/

open Set

namespace DefocusingNLS

theorem exists_expandingPerturbationReaction_local_lipschitz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L T : ℝ) (hL : 1 ≤ L)
      (q g : C(Icc (0 : ℝ) T, FourierL2)), (∀ t, ‖q t‖ ≤ R) →
      ∀ t x y, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖expandingPerturbationReaction a k L T ha ha1 hk hL m q g (t, x) -
        expandingPerturbationReaction a k L T ha ha1 hk hL m q g (t, y)‖ ≤ K * ‖x - y‖ := by
  obtain ⟨K, hK, hb⟩ := exists_expandingOddPower_lipschitz_on_ball a k ha ha1 hk m
    (R + 1) (by linarith)
  refine ⟨K, hK, ?_⟩
  intro L T hL q g hq t x y hx hy
  change ‖((-Complex.I) • (_ - _) - g t) - ((-Complex.I) • (_ - _) - g t)‖ ≤ _
  rw [sub_sub_sub_cancel_right, ← smul_sub, sub_sub_sub_cancel_right,
    norm_smul, norm_neg, Complex.norm_I, one_mul]
  have h := hb (expandingRadiusCurve L T hL t).1 (expandingRadiusCurve L T hL t).2
    (q t + x) (q t + y) ((norm_add_le _ _).trans (add_le_add (hq t) hx))
    ((norm_add_le _ _).trans (add_le_add (hq t) hy))
  simpa only [add_sub_add_left_eq_sub] using h

@[simp] theorem expandingPerturbationReaction_zero (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (q g : C(Icc (0 : ℝ) T, FourierL2)) (t : Icc (0 : ℝ) T) :
    expandingPerturbationReaction a k L T ha ha1 hk hL m q g (t, 0) = -g t := by
  change (-Complex.I) • (_ - _) - g t = -g t
  simp only [add_zero, sub_self, smul_zero, zero_sub]

/-- The step length may be fixed arbitrarily. Smallness depends on that
length and the fixed profile bound, not on the starting torus radius. -/
theorem exists_expandingPerturbation_finiteSlab (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T)
      (q g : C(Icc (0 : ℝ) T, FourierL2)) (v₀ : FourierL2) (G : ℝ),
      0 ≤ G → (∀ t, ‖q t‖ ≤ R) → (∀ t, ‖g t‖ ≤ G) →
      (K + 1) * ‖v₀‖ + G ≤ Real.exp (-(K + 1) * T) →
      ∃ v : C(Icc (0 : ℝ) T, FourierL2),
        v = expandingPicard a b k L T ha hk hL hT
          (expandingPerturbationReaction a k L T ha ha1 hk hL m q g) v₀ v ∧
        ‖v‖ ≤ Real.exp ((K + 1) * T) * ((K + 1) * ‖v₀‖ + G) ∧ ‖v‖ ≤ 1 := by
  obtain ⟨K, hK, hlip⟩ := exists_expandingPerturbationReaction_local_lipschitz
    a k ha ha1 hk m R hR
  refine ⟨K, hK, ?_⟩
  intro L T hL hT q g v₀ G hG hq hg hsmall
  apply exists_expandingMild_local_finiteSlab a b k L T ha hk hL hT
    (expandingPerturbationReaction a k L T ha ha1 hk hL m q g) v₀ K
    (Real.exp (-(K + 1) * T)) 1 G hK (Real.exp_pos _).le hG
    (hlip L T hL q g hq) _ _ hsmall
  · intro t
    rw [expandingPerturbationReaction_zero, norm_neg]
    exact hg t
  · rw [← Real.exp_add, show (K + 1) * T + -(K + 1) * T = 0 by ring, Real.exp_zero]

end DefocusingNLS

end OAI
