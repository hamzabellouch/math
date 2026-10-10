import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffMildResidual
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingResidualStability

namespace OAI

/-! # The sampled cutoff is a quantitative approximate Picard fixed point -/

open Set
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem cutoffNonlinearHistory_eq_reaction (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (m : ℕ) :
    sampledCutoffNonlinearHistory a k L T ha ha1 hk hL hT χ hχ Q hQ m =
      expandingReactionHistory T hT (expandingNonlinearReaction a k L T ha ha1 hk hL m)
        (sampledCutoffProfilePath a k L T ha ha1 hk hL
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ) := rfl

/-- The approximate fixed-point error has no dependence on the slab length. -/
theorem exists_cutoffPicard_residual_bound (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1) :
    ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      (∀ y, stationarySimilarityDefect a b m Q y = 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T),
        let q := sampledCutoffProfilePath a k L T ha ha1 hk hL
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
        let q₀ := sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ 0
        dist q (expandingPicard a b k L T ha hk hL hT
          (expandingNonlinearReaction a k L T ha ha1 hk hL m) q₀ q) ≤ C * L ^ (-2 - a) := by
  obtain ⟨N, hN⟩ := exists_cutoffProfile_mild_residual_bound a b k ha ha1 hk
    χ hχ hχone hχzero m ham
  refine ⟨N, ?_⟩
  intro Q hQ D hD hsymbol hstationary
  obtain ⟨C, hC, hCb⟩ := hN Q hQ D hD hsymbol hstationary
  refine ⟨C, hC, ?_⟩
  intro L T hL hT q q₀
  have hCL : 0 ≤ C * L ^ (-2 - a) := mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  apply (ContinuousMap.dist_le hCL).2
  intro t
  have hb := hCb L T hL hT t t.2
  change ‖sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ t -
    expandingFreeStep a b k L t ha hk hL t.2.1 q₀ -
    expandingDuhamel a b k L ha hk hL t
      (sampledCutoffNonlinearHistory a k L T ha ha1 hk hL hT χ hχ Q hQ m)‖ ≤
    C * L ^ (-2 - a) * Real.exp (-a * (t : ℝ) / 2) at hb
  have hq : sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ t = q t := by
    unfold sampledCutoffProfileHistory
    rw [projIcc_of_mem _ t.2]
  rw [hq, cutoffNonlinearHistory_eq_reaction] at hb
  rw [dist_eq_norm]
  change ‖q t - (expandingFreeStep a b k L t ha hk hL t.2.1 q₀ +
    expandingDuhamel a b k L ha hk hL t
      (expandingReactionHistory T hT (expandingNonlinearReaction a k L T ha ha1 hk hL m) q))‖ ≤ _
  rw [sub_add_eq_sub_sub]
  apply hb.trans
  exact mul_le_of_le_one_right hCL (Real.exp_le_one_iff.mpr (by nlinarith [t.2.1]))

/-- On a short slab, every bounded exact trajectory close to the sampled
stationary cutoff remains close with the actual `L^(-2-a)` forcing error. -/
theorem exists_cutoffProfile_shortSlab_stability (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      (∀ y, stationarySimilarityDefect a b m Q y = 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T), T * K < 1 →
        let q := sampledCutoffProfilePath a k L T ha ha1 hk hL
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
        let q₀ := sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ 0
        ∀ (u : C(Icc (0 : ℝ) T, FourierL2)) (u₀ : FourierL2),
          (∀ t, ‖u t‖ ≤ R) → (∀ t, ‖q t‖ ≤ R) →
          u = expandingPicard a b k L T ha hk hL hT
            (expandingNonlinearReaction a k L T ha ha1 hk hL m) u₀ u →
          dist u q ≤ (dist u₀ q₀ + C * L ^ (-2 - a)) / (1 - T * K) := by
  obtain ⟨K, hK, hstable⟩ := exists_expandingNonlinear_residual_stability a b k
    ha ha1 hk m R hR
  obtain ⟨N, hN⟩ := exists_cutoffPicard_residual_bound a b k ha ha1 hk
    χ hχ hχone hχzero m ham
  refine ⟨K, hK, N, ?_⟩
  intro Q hQ D hD hsymbol hstationary
  obtain ⟨C, hC, hbound⟩ := hN Q hQ D hD hsymbol hstationary
  refine ⟨C, hC, ?_⟩
  intro L T hL hT hTK q q₀ u u₀ huR hqR hu
  exact hstable L T hL hT hTK u q huR hqR u₀ q₀ (C * L ^ (-2 - a)) hu
    (hbound L T hL hT)

end DefocusingNLS

end OAI
