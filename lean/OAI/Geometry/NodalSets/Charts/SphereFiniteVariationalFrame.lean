import OAI.Geometry.NodalSets.Charts.SphereWeightedL2Infinite
import OAI.Geometry.NodalSets.Spectral.FiniteEigenframeMinMax
import OAI.Geometry.NodalSets.Spectral.SphereEigenGlobalNormalization

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Set Yau.Analysis
open scoped ContDiff
noncomputable section
local instance sphereFiniteFrameMeasurable : MeasurableSpace Base := borel Base
local instance sphereFiniteFrameBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_resolvent_finite_variational_frame (d : SphereEnergyData) (N : ℕ) :
    ∃ (e : Fin N → SphereWeightedL2 d) (mu : Fin N → ℝ),
      Orthonormal ℝ e ∧
      (∀ i, 0 < mu i ∧ mu i ≤ 1 ∧ sphereL2Resolvent d (e i) = mu i • e i) ∧
      Antitone mu ∧ ∀ i x,
        (∀ j, j < i → inner ℝ (e j) x = 0) →
        inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2 := by
  obtain ⟨e,mu,he,heig,hanti,hmax⟩ := compact_positive_finite_variational_eigenframe
    (sphereWeightedL2_infiniteDimensional d) (sphereL2Resolvent d)
    (sphereL2Resolvent_compact d) (sphereL2Resolvent_symmetric d)
    (sphereL2Resolvent_positive d) N
  exact ⟨e,mu,he,fun i ↦ ⟨(heig i).1,
    (sphereL2Resolvent_eigenvalue_bounds d (mu i) (e i) (he.ne_zero i) (heig i).2).2,
    (heig i).2⟩,hanti,hmax⟩

theorem sphere_resolvent_finite_smooth_frame (d : SphereEnergyData)
    (hrho : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d.density (sphereChartCoordMap p x))) (N : ℕ) :
    ∃ (u : Fin N → SphereEnergySmooth d) (mu : Fin N → ℝ),
      Orthonormal ℝ (fun i ↦ sphereEnergyL2Linear d (u i)) ∧
      (∀ i, 0 < mu i ∧ mu i ≤ 1 ∧
        sphereL2Resolvent d (sphereEnergyL2Linear d (u i)) = mu i • sphereEnergyL2Linear d (u i)) ∧
      Antitone mu ∧ ∀ i x,
        (∀ j, j < i → inner ℝ (sphereEnergyL2Linear d (u j)) x = 0) →
        inner ℝ (sphereL2Resolvent d x) x ≤ mu i * ‖x‖^2 := by
  classical
  obtain ⟨e,mu,he,heig,hanti,hmax⟩ := sphere_resolvent_finite_variational_frame d N
  have hex (i : Fin N) : ∃ u : SphereEnergySmooth d, sphereEnergyL2Linear d u = e i := by
    obtain ⟨v,hv,ha,-⟩ := sphere_eigen_global_normalized d hrho (mu i) (heig i).1.ne'
      (e i) (heig i).2.2 (he.norm_eq_one i)
    refine ⟨(⟨v,hv⟩ : sphereSmoothFunctions),?_⟩
    apply Lp.ext
    exact (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le)
      v hv.continuous).coeFn_toLp.trans ha
  choose u hu using hex
  refine ⟨u,mu,?_,?_,hanti,?_⟩
  · simpa only [hu] using he
  · simpa only [hu] using heig
  · simpa only [hu] using hmax

end
end Yau.Target

end OAI
