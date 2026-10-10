import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedStableOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.DiagonalCutoffBlowup
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingLimit

namespace OAI

/-! # Actual finite-time blowup data at every sufficiently large odd power

The constructed stable orbits give finite-time blowup with the profile's
self-similar growth rate.
-/

open Filter Topology Set
open scoped SchwartzMap ContDiff

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousRealCoreCutoff : 𝓢(E, ℝ) :=
  homogeneousCoreBump.hasCompactSupport.toSchwartzMap homogeneousCoreBump.contDiff

theorem homogeneousRealCoreCutoff_support : HasCompactSupport (homogeneousRealCoreCutoff : E → ℝ) :=
  homogeneousCoreBump.hasCompactSupport

theorem homogeneousRealCoreCutoff_one (y : E) (hy : ‖y‖ ≤ 1 / 2) :
    homogeneousRealCoreCutoff y = 1 := by
  apply homogeneousCoreBump.one_of_mem_closedBall
  simpa only [homogeneousCoreBump, Metric.mem_closedBall, dist_zero_right] using hy

theorem homogeneousRealCoreCutoff_zero (y : E) (hy : 1 ≤ ‖y‖) :
    homogeneousRealCoreCutoff y = 0 := by
  apply homogeneousCoreBump.zero_of_le_dist
  simpa only [homogeneousCoreBump, dist_zero_right] using hy

theorem radialShootingA_scaling (n : ℕ) (z : ProfileMatchingBall) :
    2 * radialShootingA n * ((n + radialInnerShootingThreshold : ℕ) : ℝ) = 1 := by
  have hm : ((n + radialInnerShootingThreshold : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (radialShootingInner_power_pos n (profileMatchingParameter z)).ne'
  unfold radialShootingA
  push_cast at hm
  push_cast
  field_simp [hm]

attribute [local irreducible] homogeneousStableCoordinates diagonalRealCoordinates
  HasFiniteDiagonalCutoffStableOrbits

theorem radialMatched_exists_finite_blowup (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∃ (N : ℕ) (hk : 8 < ((N + 1 : ℕ) : ℝ))
      (f : FourierL2) (T c : ℝ),
      0 < T ∧ 0 < c ∧
      BddAbove (maximalSobolevInteractionDomain (N + 1 : ℕ) (by linarith) (n + radialInnerShootingThreshold) f) ∧
      sSup (maximalSobolevInteractionDomain (N + 1 : ℕ) (by linarith) (n + radialInnerShootingThreshold) f) = T ∧
      Tendsto (fun t => (T - t) ^ (radialShootingA n) *
        ‖sobolevTorusFunction (N + 1 : ℕ)
          (maximalSobolevSchrodingerFlow (N + 1 : ℕ) (by linarith)
            (n + radialInnerShootingThreshold) f t) 0‖) (𝓝[<] T) (𝓝 c) := by
  have hs : Tendsto (fun n : ℕ => n + radialInnerShootingThreshold) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n _) tendsto_id
  filter_upwards [radialMatched_exists_stable_orbits hRou,
    exists_radialMatchingMap_zero, hs.eventually radialShootingExterior_exists] with n hn hz hX
  obtain ⟨z, hz⟩ := hz
  obtain ⟨N, hk10, q, _, P, _, hfin, hstable⟩ := hn z (hX z) hz
    homogeneousRealCoreCutoff homogeneousRealCoreCutoff_support
    homogeneousRealCoreCutoff_zero homogeneousRealCoreCutoff_one
  let : FiniteDimensional ℂ P.range := hfin
  have hk : 8 < ((N + 1 : ℕ) : ℝ) := lt_trans (by norm_num) hk10
  have hQzero : radialMatchedCartesian n z 0 ≠ 0 := by
    simpa only [radialMatchedCartesian, norm_zero] using radialMatchedProfile_ne_zero n z (hX z) 0 le_rfl
  obtain ⟨L₀, hL₀⟩ := exists_diagonalCutoff_blowup
    (radialShootingA n) (radialShootingB (profileMatchingParameter z)) (N + 1 : ℕ)
    (radialShootingA_bounds n (profileMatchingParameter z)).1
    (radialShootingA_bounds n (profileMatchingParameter z)).2 hk
    (n + radialInnerShootingThreshold) (radialShootingA_scaling n z)
    homogeneousRealCoreCutoff homogeneousRealCoreCutoff_support
    (fun y hy => homogeneousRealCoreCutoff_one y hy.le)
    (fun y hy => homogeneousRealCoreCutoff_zero y (by linarith))
    (radialMatchedCartesian n z) (radialMatchedCartesian_contDiff n z (hX z) hz) hQzero
    (homogeneousStableCoordinates (radialShootingA n) (N + 1 : ℕ)
      (radialShootingA_bounds n (profileMatchingParameter z)).1
      (radialShootingA_bounds n (profileMatchingParameter z)).2 hk P) hstable
  let L : {L : ℝ // 1 ≤ L} := ⟨max 1 L₀, le_max_left _ _⟩
  obtain ⟨f, hbound, htime, hlimit⟩ := hL₀ L (le_max_right _ _)
  exact ⟨N, hk, f, L.1 ^ (-2 : ℝ), ‖radialMatchedCartesian n z 0‖,
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one L.2) _, norm_pos_iff.mpr hQzero,
    hbound, htime, hlimit⟩

end DefocusingNLS

end OAI
