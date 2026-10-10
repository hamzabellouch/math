import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedStableTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffDiagonalLinearStep

namespace OAI

/-! # All linear stable-graph bounds for the constructed matched profile -/

open Set Filter Topology
open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

attribute [local irreducible] homogeneousComplexLinearizedStep homogeneousStableCoordinates
  diagonalRealCoordinates cutoffProfileEndpoint HasFiniteDiagonalTorusLinearSteps

theorem radialMatched_exists_linear_step (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z = 0) →
      ∀ (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ)),
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
            ∃ Q : ℝ, ∃ hQ : 0 ≤ Q,
            ∃ hqb : ∀ L : Radius,
              ‖cutoffProfileCoefficient a (N + 1 : ℕ) ha1 hk χ hχ Qp hQp L‖ ≤ Q,
            HasFiniteDiagonalTorusLinearSteps
              (homogeneousStableCoordinates a (N + 1 : ℕ) ha ha1 hk P)
              (cutoffProfileEndpoint a b (N + 1 : ℕ) ha ha1 hk m χ hχ Qp hQp Q hQ hqb) := by
  filter_upwards [radialMatched_exists_stable_transfer hRou] with n hn
  intro z hX hz χ hχ hχzero hχone
  obtain ⟨N, hk10, q, hq, P, hP, hfin, hcomm, hgen, Q, hQ, hqb, hstable⟩ :=
    hn z hX hz χ hχ hχzero hχone
  obtain ⟨G, hG, hspec, hspan⟩ := hgen
  let : FiniteDimensional ℂ P.range := hfin
  refine ⟨N, hk10, q, hq, P, hP, hfin, Q, hQ, hqb, ?_⟩
  apply cutoffProfile_diagonal_linear_steps _ _ _ _ _ hk10 _ χ hχ hχzero hχone
    _ _ q hq Q hQ hqb P hcomm G hG hspan hspec
  intro β hβ
  obtain ⟨T₀, hT₀, hT⟩ := hstable β hβ
  refine ⟨T₀, hT₀, fun T hTT => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hT T T.2 hTT
  refine ⟨L₀, fun L hL f hf hz => ?_⟩
  simpa only [cutoffProfileEndpoint_apply] using hL₀ L hL f hf hz

end DefocusingNLS

end OAI
