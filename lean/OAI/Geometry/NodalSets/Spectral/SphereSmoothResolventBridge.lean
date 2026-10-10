import OAI.Geometry.NodalSets.Spectral.SphereVariationalResolvent

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section
local instance sphereSmoothResolventBridgeMeasurable : MeasurableSpace Base := borel Base
local instance sphereSmoothResolventBridgeBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereEnergyL2Linear_eq_zero_iff (d : SphereEnergyData) (u : SphereEnergySmooth d) :
    sphereEnergyL2Linear d u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    by_contra hn
    have hfun : (SphereEnergySmooth.toSmooth d u : Base → ℝ) ≠ 0 := by
      intro hf
      apply hn
      exact Subtype.ext hf
    have hp := sphereWeightedPairing_self_pos d.density (SphereEnergySmooth.toSmooth d u)
      d.continuous d.positive (SphereEnergySmooth.toSmooth d u).property.continuous hfun
    have he := sphereEnergyL2Linear_norm_sq d u
    rw [hu,norm_zero,zero_pow (by decide : 2 ≠ 0)] at he
    exact (ne_of_gt hp) he.symm
  · rintro rfl
    exact map_zero _

theorem sphere_smooth_intrinsic_eigen_to_resolvent (d : SphereEnergyData)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (u : SphereEnergySmooth d) (hu : u ≠ 0) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density (SphereEnergySmooth.toSmooth d u) p z =
      lam*(SphereEnergySmooth.toSmooth d u : Base → ℝ) ((extChartAt (𝓡 4) p).symm z)) :
    0 ≤ lam ∧ sphereEnergyL2Linear d u ≠ 0 ∧
      sphereL2Resolvent d (sphereEnergyL2Linear d u) = (lam+1)⁻¹ • sphereEnergyL2Linear d u := by
  have hn : sphereEnergyL2Map d (sphereEnergyToCompletion d u) ≠ 0 := by
    rw [sphereEnergyL2Map_coe]
    exact fun h ↦ hu ((sphereEnergyL2Linear_eq_zero_iff d u).mp h)
  have hw := sphere_smooth_intrinsic_eigen_to_variational d hr u lam he
  have hb := sphere_variational_eigenvalue_nonneg d lam (sphereEnergyToCompletion d u) hn hw
  have h := (sphere_variational_eigen_to_resolvent d lam (sphereEnergyToCompletion d u) hn hw).2
  rw [sphereEnergyL2Map_coe] at h hn
  exact ⟨hb,hn,h⟩

end
end Yau.Target

end OAI
