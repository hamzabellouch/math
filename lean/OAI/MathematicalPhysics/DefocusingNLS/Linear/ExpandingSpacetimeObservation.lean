import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingContinuousRealization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalTimeBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalSpaceBound

namespace OAI

/-! # Physical space-time realization of a moving Fourier path -/

open Set

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] expandingTorusFunction

noncomputable def expandingSpacetimePath (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) : C(Icc (0 : ℝ) T × E, ℂ) :=
  let obs : C(({R : ℝ // 1 ≤ R} × FourierL2) × E, ℂ) :=
    ⟨_, continuous_expandingPhysical_observation a k ha ha1 hk⟩
  let l := expandingRadiusCurve L T hL
  let input : C(Icc (0 : ℝ) T × E, ({R : ℝ // 1 ≤ R} × FourierL2) × E) :=
    ⟨fun p => ((l p.1, u p.1), p.2),
      ((l.continuous.comp continuous_fst).prodMk
        (u.continuous.comp continuous_fst)).prodMk continuous_snd⟩
  obs.comp input

@[simp] theorem expandingSpacetimePath_apply (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (p : Icc (0 : ℝ) T × E) :
    expandingSpacetimePath a k L T ha ha1 hk hL u p =
      expandingTorusFunction a k (expandingRadius L p.1) (u p.1)
        (euclideanToTorus ((expandingRadius L p.1)⁻¹ • p.2)) := rfl

theorem expandingSpacetimePath_norm_le (a k L T M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (hu : ∀ t, ‖u t‖ ≤ M)
    (p : Icc (0 : ℝ) T × E) :
    ‖expandingSpacetimePath a k L T ha ha1 hk hL u p‖ ≤ expandingEmbeddingBound a k * M := by
  exact ((expandingTorusFunction a k (expandingRadius L p.1) (u p.1)).norm_coe_le_norm _).trans
    ((expandingTorusFunction_norm_le a k _ ha ha1 hk
      (hL.trans (expandingRadius_ge L p.1 hL p.1.2.1)) _).trans
      (mul_le_mul_of_nonneg_left (hu p.1) (by dsimp [expandingEmbeddingBound]; positivity)))

theorem expandingSpacetimePath_space_bound (a k L T M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (hu : ∀ t, ‖u t‖ ≤ M)
    (t : Icc (0 : ℝ) T) (x y : E) :
    ‖expandingSpacetimePath a (k + 2) L T ha ha1 (by linarith) hL u (t, x) -
      expandingSpacetimePath a (k + 2) L T ha ha1 (by linarith) hL u (t, y)‖ ≤
      expandingJetBound a k * M * ‖x - y‖ := by
  apply (expandingPhysical_space_bound a k (expandingRadius L t) ha ha1 hk
    (hL.trans (expandingRadius_ge L t hL t.2.1)) (u t) x y).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hu t) (by
      dsimp [expandingJetBound, expandingEmbeddingBound]; positivity)) (norm_nonneg _)

end DefocusingNLS

end OAI
