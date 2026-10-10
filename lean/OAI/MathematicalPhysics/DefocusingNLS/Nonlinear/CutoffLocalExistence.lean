import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffPicardResidual
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingApproximateExistence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzProfileSampling

namespace OAI

/-! # Exact local evolution near the sampled stationary cutoff

Finite symbol jets control the whole cutoff path and its true mild residual.
The starting-scale smallness gives a genuine solution of the nonlinear
equation, with no globally Lipschitz extension of that equation.
-/

open Set Metric
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_cutoffProfile_localSolution (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 1 ≤ ‖x‖ → χ x = 0)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1) :
    ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      (∀ y, stationarySimilarityDefect a b m Q y = 0) →
      ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T),
        T * K < 1 →
        let q := sampledCutoffProfilePath a k L T ha ha1 hk hL
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
        let q₀ := sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ 0
        ∀ u₀ : FourierL2, dist u₀ q₀ + C * L ^ (-2 - a) ≤ 1 - T * K →
        ∃ u : C(Icc (0 : ℝ) T, FourierL2),
          u = expandingPicard a b k L T ha hk hL hT
            (expandingNonlinearReaction a k L T ha ha1 hk hL m) u₀ u ∧
          dist u q ≤ 1 ∧
          dist u q ≤ (dist u₀ q₀ + C * L ^ (-2 - a)) / (1 - T * K) := by
  have hzero₂ : ∀ x : E, 2 < ‖x‖ → χ x = 0 := fun x hx => hχzero x (by linarith)
  have hzeroC : ∀ x : E, 1 ≤ ‖x‖ → (χ.postcompCLM Complex.ofRealCLM) x = 0 := by
    intro x hx
    simp only [SchwartzMap.postcompCLM_apply, hχzero x hx, map_zero]
  obtain ⟨N₁, hsamp⟩ := exists_cutoffProfile_sampling_bound a k ha ha1 hk
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) hzeroC
  obtain ⟨N₂, hres⟩ := exists_cutoffPicard_residual_bound a b k ha ha1 hk
    χ hχ hχone hzero₂ m ham
  refine ⟨max N₁ N₂, ?_⟩
  intro Q hQ D hD hsymbol hstationary
  obtain ⟨R, hR, hbR⟩ := hsamp Q hQ D hD
    (fun n hn => hsymbol n (hn.trans (le_max_left _ _)))
  obtain ⟨C, hC, hbC⟩ := hres Q hQ D hD
    (fun n hn => hsymbol n (hn.trans (le_max_right _ _))) hstationary
  obtain ⟨K, hK, hex⟩ := exists_expandingNonlinear_near_approximation a b k ha ha1 hk
    m R 1 hR (by norm_num)
  refine ⟨C, K, hC, hK, ?_⟩
  intro L T hL hT hTK q q₀ u₀ hsmall
  have hqR : ∀ t, ‖q t‖ ≤ R := by
    intro t
    exact hbR (expandingRadius L t) (expandingRadiusCurve L T hL t).2
  have hdef : dist q (expandingPicard a b k L T ha hk hL hT
      (expandingNonlinearReaction a k L T ha ha1 hk hL m) u₀ q) ≤
      dist u₀ q₀ + C * L ^ (-2 - a) := by
    calc
      _ ≤ dist q (expandingPicard a b k L T ha hk hL hT
          (expandingNonlinearReaction a k L T ha ha1 hk hL m) q₀ q) +
        dist (expandingPicard a b k L T ha hk hL hT
          (expandingNonlinearReaction a k L T ha ha1 hk hL m) q₀ q)
          (expandingPicard a b k L T ha hk hL hT
            (expandingNonlinearReaction a k L T ha ha1 hk hL m) u₀ q) := dist_triangle _ _ _
      _ ≤ C * L ^ (-2 - a) + dist q₀ u₀ := add_le_add (hbC L T hL hT)
        (expandingPicard_initial_dist_le a b k L T ha hk hL hT _ q₀ u₀ q)
      _ = _ := by rw [dist_comm q₀ u₀, add_comm]
  exact hex L T hL hT hTK q hqR u₀ (dist u₀ q₀ + C * L ^ (-2 - a)) hdef
    (by simpa only [mul_one] using hsmall)

end DefocusingNLS

end OAI
