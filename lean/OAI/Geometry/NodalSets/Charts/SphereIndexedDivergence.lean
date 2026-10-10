import OAI.Geometry.NodalSets.Charts.SphereIndexedFrameConsistency
import OAI.Geometry.NodalSets.Spectral.CompactEigenframeCardBound

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Filter Yau.Analysis
open scoped ContDiff Topology
noncomputable section
local instance sphereIndexedDivergenceMeasurable : MeasurableSpace Base := borel Base
local instance sphereIndexedDivergenceBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereIndexedEigenvalue_tendsto_atTop (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) :
    Tendsto (sphereIndexedEigenvalue d) atTop atTop := by
  apply tendsto_atTop.mpr
  intro a
  let b := max a 0+1
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨K,hK⟩ := compact_eigenframe_card_bound (sphereL2Resolvent d)
    (sphereL2Resolvent_compact d) (b+1)⁻¹ (inv_pos.mpr (by linarith))
  filter_upwards [eventually_ge_atTop K] with N hN
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho (N+1)
  have heq := sphereIndexedEigenvalue_eq_frame d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax
  have hsmall : mu (Fin.last N) < (b+1)⁻¹ := by
    by_contra h
    have hlast : (b+1)⁻¹ ≤ mu (Fin.last N) := le_of_not_gt h
    have hcard := hK (N+1) (fun i ↦ sphereEnergyL2Linear d (u i)) mu ho
      (fun i ↦ (he i).2.2) (fun i ↦ hlast.trans (hanti (Fin.le_last i)))
    omega
  have hrecip : b+1 < (mu (Fin.last N))⁻¹ := by
    have h := inv_strictAnti₀ (he (Fin.last N)).1 hsmall
    simpa using h
  rw [heq]
  have hab : a < b := by dsimp [b]; linarith [le_max_left a 0]
  linarith

end
end Yau.Target

end OAI
