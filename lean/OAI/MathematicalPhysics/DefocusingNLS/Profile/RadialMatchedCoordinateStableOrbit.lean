import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalCoordinateStableOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedStableTransferContour
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPhysicalContour
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalDiagonalCoordinates
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffCoordinateLinearData
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.DiagonalCoordinateStableOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedContinuousNonlinearStep

namespace OAI

/-! # The actual global stable graph and the fourteen physical coordinates -/

open Filter Topology
open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] homogeneousStableCoordinates
  HasContinuousCoordinateStableOrbits HasContinuousDiagonalCoordinateOrbits
  HasPhysicalDiagonalFrame HasPhysicalCoordinateFrame HasContinuousDiagonalCoordinateData
  homogeneousPhysicalCLM homogeneousComplexLinearizedStep cutoffProfileEndpoint
  HasPhysicalCoordinateStableOrbits

theorem radialMatched_exists_coordinate_stable_orbits (hRou : RectangleRouche) :
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
            HasPhysicalCoordinateStableOrbits a b (N + 1 : ℕ) ha ha1 hk m
              (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp
              (homogeneousStableCoordinates a (N + 1 : ℕ) ha ha1 hk P) := by
  filter_upwards [radialMatched_exists_stable_transfer_with_contour hRou,
    radialMatched_contour_physical_frame hRou] with n hn hphysical
  intro z hX hz χ hχ hχzero hχone
  let χc := χ.postcompCLM Complex.ofRealCLM
  have hχc := hasCompactSupport_complexCutoff χ hχ
  have hc0 : ∀ y : E, 1 ≤ ‖y‖ → χc y = 0 := by
    intro y hy
    simp only [χc, SchwartzMap.postcompCLM_apply, hχzero y hy, map_zero]
  have hc1 : ∀ y : E, ‖y‖ ≤ 1 / 2 → χc y = 1 := by
    intro y hy
    simp only [χc, SchwartzMap.postcompCLM_apply, hχone y hy,
      Complex.ofRealCLM_apply, Complex.ofReal_one]
  obtain ⟨N, hk10, q, hq, P, hP, hfin, hcomm, hgen, D, δ, hδ, hdecay,
    Q, hQ, hqb, hkernel⟩ := hn z hX hz χc hχc hc0 hc1
  let : FiniteDimensional ℂ P.range := hfin
  let k : ℝ := (N + 1 : ℕ)
  have hk : 8 < k := lt_trans (by norm_num) hk10
  let a := radialShootingA n
  let b := radialShootingB (profileMatchingParameter z)
  let m := n + radialInnerShootingThreshold
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  let Qp := radialMatchedCartesian n z
  have hQp := radialMatchedCartesian_contDiff n z hX hz
  obtain ⟨G, hG, hspec, hspan⟩ := hgen
  have hlinear := cutoffProfile_continuous_coordinate_steps a b k ha ha1 hk10 m
    χc hχc hc0 hc1 Qp hQp q hq Q hQ hqb P hcomm G hG hspan hspec
  have hlin : HasContinuousDiagonalCoordinateData a k ha ha1 hk
      (homogeneousStableCoordinates a k ha ha1 hk P) G hspan hspec χc
      (cutoffProfileEndpoint a b k ha ha1 hk m χc hχc Qp hQp Q hQ hqb) := by
    apply hlinear
    intro β hβ
    obtain ⟨T₀, hT₀, hT⟩ := hkernel β hβ
    refine ⟨T₀, hT₀, fun T hTT => ?_⟩
    obtain ⟨L₀, hL₀⟩ := hT T T.2 hTT
    refine ⟨L₀, fun L hL f hf hzero => ?_⟩
    simpa only [cutoffProfileEndpoint_apply] using hL₀ L hL f hf hzero
  have horbit := continuousDiagonalCoordinateOrbits_of_linear a b k ha ha1 hk m
    χc hχc Qp hQp Q hQ hqb (homogeneousStableCoordinates a k ha ha1 hk P) G hspan hspec hlin
    (fun T => radialMatched_continuous_nonlinear_steps n z hX hz k hk χ hχ
      (fun y hy => hχone y hy.le) hχzero T Q hQ hqb)
  obtain ⟨F, hF, hphys, hFspan⟩ := hphysical z hX hz (N + 1) ha ha1 hk q hq
    P hP hcomm hfin ⟨G, hG, hspec, hspan⟩ D δ hδ hdecay
  have hfix := radialMatched_projection_fixes_physical_frame n z hX hz ((N + 1 : ℕ) : ℝ)
    ha ha1 hk q hq P hP hcomm D δ hδ hdecay F hphys
  have hrange := homogeneous_projection_real_frame_range a b k ha ha1 hk m q P hP hcomm
    ⟨G, hG, hspec, hspan⟩ D δ hδ hdecay F hFspan
  have hB := physicalDiagonal_coordinate_equiv a k ha ha1 hk P G hspan hspec
    F hF hfix hrange
  refine ⟨N, hk10, q, hq, P, hP, hfin, ?_⟩
  unfold HasPhysicalCoordinateStableOrbits
  exact ⟨G, hspan, hspec, F, hF, hphys, hB, horbit⟩

end DefocusingNLS

end OAI
