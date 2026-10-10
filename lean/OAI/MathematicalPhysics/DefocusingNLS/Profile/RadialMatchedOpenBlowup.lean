import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalCoordinateOpen
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalCutoffBlowup
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCoordinateStableOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedBlowup

namespace OAI

/-! # The matched profiles give open sets of physical finite-time blowup data -/

open Set Filter Topology
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] HasFiniteTimeSelfSimilarBlowup HasPhysicalCutoffOrbit
  HasPhysicalCoordinateStableOrbits homogeneousStableCoordinates

theorem radialMatched_exists_open_blowup (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∃ (N : ℕ) (hk : 8 < ((N + 1 : ℕ) : ℝ)),
      ∃ U : Set FourierL2, U.Nonempty ∧ IsOpen U ∧ ∀ f ∈ U,
        HasFiniteTimeSelfSimilarBlowup (N + 1 : ℕ) (by linarith)
          (n + radialInnerShootingThreshold) (radialShootingA n) f := by
  have hs : Tendsto (fun n : ℕ => n + radialInnerShootingThreshold) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n _) tendsto_id
  filter_upwards [radialMatched_exists_coordinate_stable_orbits hRou,
    exists_radialMatchingMap_zero, hs.eventually radialShootingExterior_exists] with n hn hz hX
  obtain ⟨z, hz⟩ := hz
  obtain ⟨N, hk10, q, _, P, _, hfin, hstable⟩ := hn z (hX z) hz
    homogeneousRealCoreCutoff homogeneousRealCoreCutoff_support
    homogeneousRealCoreCutoff_zero homogeneousRealCoreCutoff_one
  let : FiniteDimensional ℂ P.range := hfin
  have hk : 8 < ((N + 1 : ℕ) : ℝ) := lt_trans (by norm_num) hk10
  let a := radialShootingA n
  let b := radialShootingB (profileMatchingParameter z)
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  let Q := radialMatchedCartesian n z
  have hQ := radialMatchedCartesian_contDiff n z (hX z) hz
  have hS : HasCartesianSymbol (-2 * a) Q :=
    ⟨hQ, fun j => radialMatchedCartesian_symbol n z (hX z) hz j⟩
  let χ := homogeneousRealCoreCutoff.postcompCLM Complex.ofRealCLM
  have hχ := hasCompactSupport_complexCutoff homogeneousRealCoreCutoff homogeneousRealCoreCutoff_support
  have hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0 := by
    intro y hy
    simp only [χ, SchwartzMap.postcompCLM_apply,
      homogeneousRealCoreCutoff_zero y hy, map_zero]
  have hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1 := by
    intro y hy
    simp only [χ, SchwartzMap.postcompCLM_apply,
      homogeneousRealCoreCutoff_one y hy, Complex.ofRealCLM_apply, Complex.ofReal_one]
  obtain ⟨U, hUn, hUo, hU⟩ := physicalCoordinateStableOrbits_open a b (N + 1 : ℕ) ha ha1 hk
    (n + radialInnerShootingThreshold) χ hχ hχzero hχone Q hQ hS
    (homogeneousStableCoordinates a (N + 1 : ℕ) ha ha1 hk P) hstable
  refine ⟨N, hk, U, hUn, hUo, fun f hf => ?_⟩
  have hQzero : Q 0 ≠ 0 := by
    simpa only [Q, radialMatchedCartesian, norm_zero] using
      radialMatchedProfile_ne_zero n z (hX z) 0 le_rfl
  exact (hU f hf).blowup a b (N + 1 : ℕ) ha ha1 hk (n + radialInnerShootingThreshold)
    (radialShootingA_scaling n z) homogeneousRealCoreCutoff homogeneousRealCoreCutoff_support
    (fun y hy => homogeneousRealCoreCutoff_one y hy.le)
    (fun y hy => homogeneousRealCoreCutoff_zero y (by linarith)) Q hQ hQzero f

end DefocusingNLS

end OAI
