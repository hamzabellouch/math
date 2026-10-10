import OAI.Geometry.NodalSets.Charts.SphereIndexedDivergence
import OAI.Geometry.NodalSets.Spectral.FiniteEigenframeCaptureLemmas

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Filter Yau.Analysis
open scoped ContDiff Topology
noncomputable section
local instance sphereCoverageMeasurable : MeasurableSpace Base := borel Base
local instance sphereCoverageBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_resolvent_eigenvalue_index (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x)))
    (f : SphereWeightedL2 d) (hf : f ≠ 0) (a : ℝ) (hfa : sphereL2Resolvent d f=a • f) :
    ∃ N : ℕ, sphereIndexedEigenvalue d N = a⁻¹-1 := by
  have ha := (sphereL2Resolvent_eigenvalue_bounds d a f hf hfa).1
  obtain ⟨N,hN⟩ := ((sphereIndexedEigenvalue_tendsto_atTop d hrho).eventually
    (eventually_gt_atTop (a⁻¹-1))).exists
  obtain ⟨u,mu,ho,he,hanti,hmax⟩ := sphere_resolvent_finite_smooth_frame d hrho (N+1)
  have heq := sphereIndexedEigenvalue_eq_frame d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax
  rw [heq] at hN
  have hlt : mu (Fin.last N) < a := (inv_lt_inv₀ ha (he (Fin.last N)).1).mp (by linarith)
  obtain ⟨i,hi⟩ := finite_eigenframe_captures_above_last (sphereL2Resolvent d)
    (sphereL2Resolvent_symmetric d) (fun i ↦ sphereEnergyL2Linear d (u i)) mu
    (fun i ↦ (he i).2.2) hmax f hf a hfa hlt
  refine ⟨i.val,?_⟩
  rw [sphereIndexedEigenvalue_eq_frame_index d u mu ho (fun i ↦ (he i).1)
    (fun i ↦ (he i).2.2) hanti hmax i,hi]

theorem sphere_smooth_intrinsic_eigenvalue_index (d : SphereEnergyData)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (u : SphereEnergySmooth d) (hu : u ≠ 0) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator d.tensor d.density (SphereEnergySmooth.toSmooth d u) p z =
      lam*(SphereEnergySmooth.toSmooth d u : Base → ℝ) ((extChartAt (𝓡 4) p).symm z)) :
    ∃ N : ℕ, sphereIndexedEigenvalue d N=lam := by
  obtain ⟨hlam,hun,heu⟩ := sphere_smooth_intrinsic_eigen_to_resolvent d hr u hu lam he
  obtain ⟨N,hN⟩ := sphere_resolvent_eigenvalue_index d
    (fun p ↦ (hr.comp (sphereChartCoordMap_smooth p)).contDiff) _ hun (lam+1)⁻¹ heu
  exact ⟨N,by simpa using hN⟩

end
end Yau.Target

end OAI
