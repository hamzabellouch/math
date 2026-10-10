import OAI.Geometry.NodalSets.Spectral.FiniteEigenframeCaptureLemmas
import OAI.Geometry.NodalSets.Spectral.SphereIndexedRayleigh

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Yau.Analysis
open scoped ContDiff
noncomputable section
local instance sphereFrameConsistencyMeasurable : MeasurableSpace Base := borel Base
local instance sphereFrameConsistencyBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereIndexedEigenvalue_eq_frame_index (d : SphereEnergyData) {N : ℕ}
    (u : Fin N → SphereEnergySmooth d) (mu : Fin N → ℝ)
    (ho : Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)))
    (hmu : ∀ i, 0 < mu i)
    (he : ∀ i, sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i))
    (hanti : Antitone mu)
    (hmax : ∀ i x, (∀ j, j < i → inner ℝ (sphereEnergyL2Linear d (u j)) x = 0) →
      inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2) (i : Fin N) :
    sphereIndexedEigenvalue d i.val = (mu i)⁻¹-1 := by
  have hle : i.val+1 ≤ N := i.isLt
  let c := Fin.castLE hle
  have h := sphereIndexedEigenvalue_eq_frame d (fun j ↦ u (c j)) (fun j ↦ mu (c j))
    (ho.comp c (Fin.castLE_injective hle)) (fun j ↦ hmu (c j)) (fun j ↦ he (c j))
    (fun j k hjk ↦ hanti hjk)
    (finite_frame_maximum_restrict hle (sphereL2Resolvent d) _ mu hmax)
  exact h

theorem sphereIndexedEigenvalue_monotone (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) :
    Monotone (sphereIndexedEigenvalue d) := by
  intro k l hkl
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho (l+1)
  let i : Fin (l+1) := ⟨k,by omega⟩
  have hi := sphereIndexedEigenvalue_eq_frame_index d u mu ho (fun j ↦ (he j).1)
    (fun j ↦ (he j).2.2) hanti hmax i
  have hl := sphereIndexedEigenvalue_eq_frame d u mu ho (fun j ↦ (he j).1)
    (fun j ↦ (he j).2.2) hanti hmax
  change sphereIndexedEigenvalue d i.val ≤ sphereIndexedEigenvalue d l
  rw [hi,hl]
  exact sub_le_sub_right (inv_anti₀ (he (Fin.last l)).1 (hanti (Fin.le_last i))) 1

end
end Yau.Target

end OAI
