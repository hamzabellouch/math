import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedFlow
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialSymbols

namespace OAI

/-! # The matched stationary profile supplies the actual whole-space evolution

The Y representative is obtained from the proved profile symbol estimates.
Its bounded real-linear potential has exactly the two physical coefficients
in the manuscript, and its finite-slab propagators have explicit bounds.
-/

open Set

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_matched_homogeneousLinearized_propagator
    (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (k : ℝ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < k) :
    let a := radialShootingA n
    let b := radialShootingB (profileMatchingParameter z)
    let m := n + radialInnerShootingThreshold
    ∃ q : HomogeneousY a k,
      (∀ y : E, homogeneousPhysicalCLM a k ha ha1 hk q y = radialMatchedCartesian n z y) ∧
      (∀ v : HomogeneousY a k, ∀ y : E,
        homogeneousPhysicalCLM a k ha ha1 hk (homogeneousLinearizedPotential a k ha ha1 hk m q v) y =
          -Complex.I *
            (radialPotentialDiagonal m (radialMatchedCartesian n z) y *
                homogeneousPhysicalCLM a k ha ha1 hk v y +
              radialPotentialAntilinear m (radialMatchedCartesian n z) y *
                star (homogeneousPhysicalCLM a k ha ha1 hk v y))) ∧
      ∀ (T : ℝ) (hT : 0 ≤ T), ∃ U : HomogeneousY a k →L[ℝ] C(Icc (0 : ℝ) T, HomogeneousY a k),
        (∀ u₀ t, U u₀ t = homogeneousFreeOperator a b k t ha ha1 hk u₀ +
          homogeneousDuhamel a b k ha ha1 hk t
            (homogeneousPotentialHistory T hT (homogeneousLinearizedPotential a k ha ha1 hk m q)
              (U u₀))) ∧
        ‖U‖ ≤ 2 * Real.exp
          ((2 * (‖homogeneousLinearizedPotential a k ha ha1 hk m q‖ + 1)) * T) := by
  dsimp only
  obtain ⟨q, hq⟩ := radialMatchedCartesian_homogeneous n z hX hz k ha ha1 hk
  refine ⟨q, hq, ?_, ?_⟩
  · intro v y
    rw [homogeneousLinearizedPotential_physical, hq y, radialPotential_decomposition]
  · intro T hT
    refine ⟨homogeneousLinearizedPropagator (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) k T ha ha1 hk hT
      (n + radialInnerShootingThreshold) q, ?_,
        homogeneousLinearizedPropagator_norm_le _ _ _ _ _ _ _ _ _ _⟩
    intro u₀ t
    exact homogeneousLinearizedTrajectory_eq _ _ _ _ _ _ _ _ _ _ u₀ t

end DefocusingNLS

end OAI
