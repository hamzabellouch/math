import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombLipschitz
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarRadial

namespace OAI

/-! The actual direct Coulomb interaction depends only on planar separation. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def liftPlanarIsometry (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) : Position ≃ₗᵢ[ℝ] Position :=
  positionSplitIsometry.trans
    ((LinearIsometryEquiv.withLpProdCongr 2 L (LinearIsometryEquiv.refl ℝ ℝ)).trans
      positionSplitIsometry.symm)

theorem liftPlanarIsometry_coordinates (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (x : Position) :
    positionSplitCoordinates (liftPlanarIsometry L x) =
      (L (positionSplitCoordinates x).1, (positionSplitCoordinates x).2) := by
  change WithLp.ofLp (positionSplitIsometry (positionSplitIsometry.symm
    ((LinearIsometryEquiv.withLpProdCongr 2 L (LinearIsometryEquiv.refl ℝ ℝ))
      (positionSplitIsometry x)))) = _
  rw [positionSplitIsometry.apply_symm_apply]
  rfl

theorem localizedDensity_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    localizedDensity freq (L u) (liftPlanarIsometry L x) = localizedDensity freq u x := by
  simp only [localizedDensity, continuumLocalizedMode, localizedMode,
    liftPlanarIsometry_coordinates, ← L.map_sub, normalizedPlanarMode_isometry]

theorem localizedDensity_potential_liftPlanarIsometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) (x : Position) :
    NeutralAtom.potentialOf (localizedDensity freq (L u)) (liftPlanarIsometry L x) =
      NeutralAtom.potentialOf (localizedDensity freq u) x := by
  unfold NeutralAtom.potentialOf
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun y => NeutralAtom.coulombKernel (liftPlanarIsometry L x - y) * localizedDensity freq (L u) y)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [localizedDensity_liftPlanarIsometry, ← (liftPlanarIsometry L).map_sub]
  simp only [NeutralAtom.coulombKernel, LinearIsometryEquiv.norm_map]

theorem localizedCoulombCoeff_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u v : PlanarPosition) :
    localizedCoulombCoeff freq (L u) (L v) = localizedCoulombCoeff freq u v := by
  unfold localizedCoulombCoeff
  rw [← MeasureTheory.integral_comp (liftPlanarIsometry L)
    (fun x => localizedDensity freq (L u) x * NeutralAtom.potentialOf (localizedDensity freq (L v)) x)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_liftPlanarIsometry, localizedDensity_potential_liftPlanarIsometry]

theorem localizedCoulombProfileAt_isometry (freq : ℝ)
    (L : PlanarPosition ≃ₗᵢ[ℝ] PlanarPosition) (u : PlanarPosition) :
    localizedCoulombProfileAt freq (L u) = localizedCoulombProfileAt freq u := by
  rw [localizedCoulombProfileAt_eq, localizedCoulombProfileAt_eq]
  simpa only [map_zero] using localizedCoulombCoeff_isometry freq L 0 u

theorem localizedCoulombProfileAt_norm (freq : ℝ) (u : PlanarPosition) :
    localizedCoulombProfileAt freq u = localizedCoulombProfile freq ‖u‖ := by
  have hn : ‖‖u‖ • planarAxis 0‖ = ‖u‖ := by
    rw [norm_smul, planarAxis_zero_norm, mul_one, Real.norm_of_nonneg (norm_nonneg u)]
  have h := localizedCoulombProfileAt_isometry freq
    ((ℝ ∙ (‖u‖ • planarAxis 0 - u))ᗮ.reflection) (‖u‖ • planarAxis 0)
  rw [Submodule.reflection_sub hn] at h
  exact h

theorem localizedCoulombCoeff_displacement (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfileAt freq (v - u) := by
  unfold localizedCoulombCoeff localizedCoulombProfileAt
  rw [← integral_add_right_eq_self
    (fun x => localizedDensity freq u x * NeutralAtom.potentialOf (localizedDensity freq v) x)
    (planarCenter u)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [localizedDensity_translate freq u, add_sub_cancel_right, localizedDensity_potential_translate freq v]
  congr 2
  rw [planarCenter_sub]
  abel

theorem localizedCoulombCoeff_distance (freq : ℝ) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v = localizedCoulombProfile freq ‖u - v‖ := by
  rw [localizedCoulombCoeff_displacement, localizedCoulombProfileAt_norm, norm_sub_rev]

end ContinuumCoulomb

end

end OAI
