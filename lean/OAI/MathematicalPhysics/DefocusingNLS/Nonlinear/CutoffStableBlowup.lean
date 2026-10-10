import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStableOrbit

namespace OAI

/-! # Finite-time blowup of the constructed stable cutoff orbits

The conclusion retains the stable initial coordinates. The additional physical
parameter argument is needed to obtain an open set of initial data.
-/

open Set Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem sampledCutoffProfileOrbit_center (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ y : E, ‖y‖ < 1 / 2 → χ y = 1)
    (hχzero : ∀ y : E, 2 < ‖y‖ → χ y = 0)
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (s : ℝ) (hs : 0 ≤ s) :
    expandingTorusFunction a k (expandingRadius L s)
      (sampledCutoffProfileOrbit a k L ha1 hk hL
        (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp s) 0 =
      Qp 0 := by
  unfold sampledCutoffProfileOrbit sampledCutoffProfileAtRadius
  simp only [max_eq_right hs]
  exact sampledCutoffProfile_center a k (expandingRadius L s) ha ha1 hk
    (hL.trans (expandingRadius_ge L s hL hs)) χ hχ hχone hχzero Qp hQp

theorem cutoffGlobal_blowup (a b k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (m : ℕ) (ham : 2 * a * m = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ y : E, ‖y‖ < 1 / 2 → χ y = 1)
    (hχzero : ∀ y : E, 2 < ‖y‖ → χ y = 0)
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (hQzero : Qp 0 ≠ 0)
    (u : ℝ → FourierL2) (hu : ContinuousOn u (Ici 0))
    (hsol : ∀ (S : ℝ) (hS : 0 < S), expandingSlabRestriction u hu S =
      expandingPicard a b k L S ha hk hL hS.le
        (expandingNonlinearReaction a k L S ha ha1 hk hL m) (u 0)
        (expandingSlabRestriction u hu S))
    (hdecay : Tendsto (fun s => ‖u s - sampledCutoffProfileOrbit a k L ha1 hk hL
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp s‖)
        atTop (𝓝 0)) :
    let f := expandingPhysicalInitialEquiv a k L ha ha1 hk hL (u 0)
    BddAbove (maximalSobolevInteractionDomain k (by linarith) m f) ∧
      sSup (maximalSobolevInteractionDomain k (by linarith) m f) = L ^ (-2 : ℝ) ∧
      Tendsto (fun t => (L ^ (-2 : ℝ) - t) ^ a *
        ‖sobolevTorusFunction k (maximalSobolevSchrodingerFlow k (by linarith) m f t) 0‖)
        (𝓝[<] (L ^ (-2 : ℝ))) (𝓝 ‖Qp 0‖) := by
  let q := sampledCutoffProfileOrbit a k L ha1 hk hL
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp
  have hq : ∀ s, 0 ≤ s → expandingTorusFunction a k (expandingRadius L s) (q s) 0 = Qp 0 :=
    sampledCutoffProfileOrbit_center a k L ha ha1 hk hL χ hχ hχone hχzero Qp hQp
  have htime := expandingGlobal_lifespan a b k L ha ha1 hk hL m ham u hu hsol
    q 0 (Qp 0) hQzero hq hdecay
  exact ⟨htime.1, htime.2, expandingGlobal_rescaled_limit a b k L ha ha1 hk hL m ham
    u hu hsol q 0 (Qp 0) hq hdecay⟩

theorem exists_cutoffStable_blowup {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (m : ℕ) (ham : 2 * a * m = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ y : E, ‖y‖ < 1 / 2 → χ y = 1)
    (hχzero : ∀ y : E, 2 < ‖y‖ → χ y = 0)
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (hQzero : Qp 0 ≠ 0)
    (hstable : HasCutoffStableOrbits (F := F) a b k ha ha1 hk m
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
      ∃ ζ : F →L[ℝ] FourierL2, ∃ π : FourierL2 →L[ℝ] F,
        (∀ v, π (ζ v) = v) ∧ ∀ w : FourierL2, ‖w‖ ≤ ρ / 4 → π w = 0 →
          ∃ f : FourierL2,
            stableFrameProjection ζ π ((expandingPhysicalInitialEquiv a k L.1 ha ha1 hk L.2).symm f -
              sampledCutoffProfileOrbit a k L.1 ha1 hk L.2
                (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp 0) = w ∧
            BddAbove (maximalSobolevInteractionDomain k (by linarith) m f) ∧
            sSup (maximalSobolevInteractionDomain k (by linarith) m f) = L.1 ^ (-2 : ℝ) ∧
            Tendsto (fun t => (L.1 ^ (-2 : ℝ) - t) ^ a *
              ‖sobolevTorusFunction k (maximalSobolevSchrodingerFlow k (by linarith) m f t) 0‖)
              (𝓝[<] (L.1 ^ (-2 : ℝ))) (𝓝 ‖Qp 0‖) := by
  obtain ⟨ρ, hρ, L₀, hs⟩ := hstable
  refine ⟨ρ, hρ, L₀, fun L hL => ?_⟩
  obtain ⟨ζ, π, hπζ, hw⟩ := hs L hL
  refine ⟨ζ, π, hπζ, fun w hwb hwz => ?_⟩
  obtain ⟨u, hu, hu0, hsol, hdecay⟩ := hw w hwb hwz
  refine ⟨expandingPhysicalInitialEquiv a k L.1 ha ha1 hk L.2 (u 0), ?_, ?_⟩
  · simpa only [ContinuousLinearEquiv.symm_apply_apply] using hu0
  · exact cutoffGlobal_blowup a b k L.1 ha ha1 hk L.2 m ham χ hχ hχone hχzero Qp hQp
      hQzero u hu hsol hdecay

end DefocusingNLS

end OAI
