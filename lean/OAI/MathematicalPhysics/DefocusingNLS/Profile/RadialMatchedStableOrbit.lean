import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedLinearStep
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedNonlinearStep
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.DiagonalCutoffStableOrbit

namespace OAI

/-! # The constructed matched profile has actual global stable orbits -/

open Filter Topology
open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] homogeneousStableCoordinates
  HasFiniteDiagonalCutoffStableOrbits

theorem radialMatched_exists_stable_orbits (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z = 0) →
      ∀ (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ)),
      (∀ y : E, 1 ≤ ‖y‖ → χ y = 0) → (∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1) →
      ∃ N : ℕ, ∃ hk10 : 10 < ((N + 1 : ℕ) : ℝ),
        let hk : 8 < ((N + 1 : ℕ) : ℝ) := lt_trans (by norm_num) hk10
        let a := radialShootingA n
        let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
        let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
        let b := radialShootingB (profileMatchingParameter z)
        let m := n + radialInnerShootingThreshold
        let Qp := radialMatchedCartesian n z
        let hQp := radialMatchedCartesian_contDiff n z hX hz
        ∃ q : HomogeneousY a ((N + 1 : ℕ) : ℝ),
          (∀ x : E, homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x = Qp x) ∧
          ∃ P : (HomogeneousY a ((N + 1 : ℕ) : ℝ) × HomogeneousY a ((N + 1 : ℕ) : ℝ)) →L[ℂ]
              (HomogeneousY a ((N + 1 : ℕ) : ℝ) × HomogeneousY a ((N + 1 : ℕ) : ℝ)),
            IsIdempotentElem P ∧ ∃ hfin : FiniteDimensional ℂ P.range,
            letI := hfin
            HasFiniteDiagonalCutoffStableOrbits a b (N + 1 : ℕ) ha ha1 hk m
              (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp
              (homogeneousStableCoordinates a (N + 1 : ℕ) ha ha1 hk P) := by
  filter_upwards [radialMatched_exists_linear_step hRou] with n hn
  intro z hX hz χ hχ hχzero hχone
  have hc0 : ∀ y : E, 1 ≤ ‖y‖ → (χ.postcompCLM Complex.ofRealCLM) y = 0 := by
    intro y hy
    simp only [SchwartzMap.postcompCLM_apply, hχzero y hy, map_zero]
  have hc1 : ∀ y : E, ‖y‖ ≤ 1 / 2 → (χ.postcompCLM Complex.ofRealCLM) y = 1 := by
    intro y hy
    simp only [SchwartzMap.postcompCLM_apply, hχone y hy, Complex.ofRealCLM_apply, Complex.ofReal_one]
  obtain ⟨N, hk10, q, hq, P, hP, hfin, Q, hQ, hqb, hlinear⟩ := hn z hX hz
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) hc0 hc1
  let : FiniteDimensional ℂ P.range := hfin
  refine ⟨N, hk10, q, hq, P, hP, hfin, ?_⟩
  apply cutoffStableOrbits_of_linear_steps _ _ _ _ _ _ _ _ _ _ _ Q hQ hqb _ hlinear
  exact fun T => radialMatched_nonlinear_steps n z hX hz _ _ χ hχ
    (fun y hy => hχone y hy.le) hχzero T Q hQ hqb

end DefocusingNLS

end OAI
