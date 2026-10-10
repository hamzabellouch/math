import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedProfileBounds
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffMovingPath
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfilePropagator

namespace OAI

/-! # Uniform finite-slab evolution for the actual cutoff profile

The matched profile's proved symbol bounds give a single norm bound on
all of its expanding-torus samples. The actual linearized potential then
has bounded real-linear propagators uniformly in the starting radius.
-/

open Set
open scoped SchwartzMap ContDiff

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_matchedCutoffProfile_uniform_bound (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (k : ℝ) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0) :
    let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
    let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
    let hQ := radialMatchedCartesian_contDiff n z hX hz
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (t : Icc (0 : ℝ) T),
      ‖sampledCutoffProfilePath (radialShootingA n) k L T ha ha1 hk hL
        χ hχ (radialMatchedCartesian n z) hQ t‖ ≤ R := by
  intro ha ha1 hQ
  obtain ⟨R, hR, hbound⟩ := radialMatchedCutoff_sampling_bound n z hX hz k hk χ hχ hχzero
  refine ⟨R, hR, ?_⟩
  intro L T hL t
  exact hbound (expandingRadiusCurve L T hL t).1 (expandingRadiusCurve L T hL t).2

theorem exists_matchedCutoffLinearized_propagator (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (k : ℝ) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0) :
    let a := radialShootingA n
    let b := radialShootingB (profileMatchingParameter z)
    let m := n + radialInnerShootingThreshold
    let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
    let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
    let hQ := radialMatchedCartesian_contDiff n z hX hz
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T),
      let q := sampledCutoffProfilePath a k L T ha ha1 hk hL χ hχ (radialMatchedCartesian n z) hQ
      ∃ U : FourierL2 →L[ℝ] C(Icc (0 : ℝ) T, FourierL2),
        (∀ u₀ t, U u₀ t = expandingFreeStep a b k L t ha hk hL t.2.1 u₀ +
          expandingDuhamel a b k L ha hk hL t (expandingReactionHistory T hT
            (expandingProfileReaction a k T ha ha1 hk m (expandingRadiusCurve L T hL) q 0)
            (U u₀))) ∧
        ‖U‖ ≤ (K + 1) * Real.exp ((K + 1) * T) := by
  intro a b m ha ha1 hQ
  obtain ⟨R, hR, hbound⟩ := exists_matchedCutoffProfile_uniform_bound n z hX hz k hk χ hχ hχzero
  obtain ⟨K, hK, hprop⟩ := exists_expandingProfile_propagator a b k ha ha1 hk m R hR
  refine ⟨K, hK, ?_⟩
  intro L T hL hT
  exact hprop L T hL hT _ (hbound L T hL)

end DefocusingNLS

end OAI
