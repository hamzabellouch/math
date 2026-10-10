import OAI.Geometry.NodalSets.Charts.SphereIndexedFrameConsistency
import OAI.Geometry.NodalSets.Charts.SphereSmoothVariationalStrong

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory
open scoped ContDiff
noncomputable section
local instance sphereIndexedIntrinsicMeasurable : MeasurableSpace Base := borel Base
local instance sphereIndexedIntrinsicBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_smooth_resolvent_to_intrinsic (d : SphereEnergyData)
    (u : SphereEnergySmooth d) (mu : ℝ) (hmu : mu ≠ 0)
    (he : sphereL2Resolvent d (sphereEnergyL2Linear d u) = mu • sphereEnergyL2Linear d u) :
    ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density
      (SphereEnergySmooth.toSmooth d u) p z =
        (mu⁻¹-1) * (SphereEnergySmooth.toSmooth d u : Base → ℝ)
          ((extChartAt (𝓡 4) p).symm z) := by
  apply sphere_smooth_variational_to_intrinsic d u (mu⁻¹-1)
  intro v
  rw [sphereCompletedDirichlet,sphereEnergyL2Map_coe,
    sphere_resolvent_smooth_variational d mu hmu u he v]
  ring

theorem sphereIndexedEigenvalue_intrinsic_realization (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) (N : ℕ) :
    ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
      sphereWeightedPairing d.density u u = 1 ∧
      ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density u p z =
        sphereIndexedEigenvalue d N * u ((extChartAt (𝓡 4) p).symm z) := by
  obtain ⟨u,hu,hn,_,hw⟩ := sphereIndexedEigenvalue_smooth_realization d hrho N
  refine ⟨SphereEnergySmooth.toSmooth d u,(SphereEnergySmooth.toSmooth d u).property,?_,?_,
    sphere_smooth_variational_to_intrinsic d u _ hw⟩
  · intro hz
    exact hu (Subtype.ext hz)
  · rw [← sphereEnergyL2Linear_norm_sq,hn,one_pow]

theorem sphere_indexed_finite_intrinsic_frame (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) (N : ℕ) :
    ∃ u : Fin N → SphereEnergySmooth d,
      Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)) ∧
      ∀ i p z, -intrinsicWeightedChartOperator d.tensor d.density
        (SphereEnergySmooth.toSmooth d (u i)) p z =
          sphereIndexedEigenvalue d i.val * (SphereEnergySmooth.toSmooth d (u i) : Base → ℝ)
            ((extChartAt (𝓡 4) p).symm z) := by
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho N
  refine ⟨u,ho,?_⟩
  intro i
  rw [sphereIndexedEigenvalue_eq_frame_index d u mu ho (fun j ↦ (he j).1)
    (fun j ↦ (he j).2.2) hanti hmax i]
  exact sphere_smooth_resolvent_to_intrinsic d (u i) (mu i) (he i).1.ne' (he i).2.2

end
end Yau.Target

end OAI
