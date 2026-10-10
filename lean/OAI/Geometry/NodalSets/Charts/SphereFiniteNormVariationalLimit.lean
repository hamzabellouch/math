import OAI.Geometry.NodalSets.Charts.SphereFiniteNormMixedLimit
import OAI.Geometry.NodalSets.Spectral.SphereVariationalResolvent

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
local instance sphereVariationalLimitMeasurable : MeasurableSpace Base := borel Base
local instance sphereVariationalLimitBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_finite_norm_variational_limit
    (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm y = x)
    (d₀ : SphereEnergyData)
    (hd₀ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d₀.density)
    (b : ℕ → SphereEnergyData)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density)
    (u : ℕ → SphereEnergySmooth d₀) (z : SphereEnergyHilbert d₀)
    (hz : Tendsto (fun j ↦ sphereEnergyToCompletion d₀ (u j)) atTop (𝓝 z))
    (hcoeff : Tendsto (fun j ↦ sphereCoefficientDistance P 0
      d₀.tensor d₀.density (b j).tensor (b j).density) atTop (𝓝 0))
    (lam : ℕ → ℝ) (lam₀ : ℝ) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (he : ∀ j p y, -intrinsicWeightedChartOperator (b j).tensor (b j).density
      (SphereEnergySmooth.toSmooth d₀ (u j)) p y =
        lam j * (SphereEnergySmooth.toSmooth d₀ (u j) : Base → ℝ)
          ((extChartAt (𝓡 4) p).symm y)) :
    ∀ w : SphereEnergyHilbert d₀,
      sphereCompletedDirichlet d₀ z w =
        lam₀ * inner ℝ (sphereEnergyL2Map d₀ z) (sphereEnergyL2Map d₀ w) := by
  have htest (w : SphereEnergySmooth d₀) :
      sphereCompletedDirichlet d₀ z (sphereEnergyToCompletion d₀ w) =
        lam₀ * inner ℝ (sphereEnergyL2Map d₀ z)
          (sphereEnergyL2Map d₀ (sphereEnergyToCompletion d₀ w)) := by
    have hlim := sphere_finite_norm_mixed_limit P hcover d₀ hd₀ b hb u (fun _ ↦ w)
      z (sphereEnergyToCompletion d₀ w) hz tendsto_const_nhds hcoeff
    have hident : (fun j ↦ sphereDirichletForm (b j).tensor
        (SphereEnergySmooth.toSmooth d₀ (u j)) (SphereEnergySmooth.toSmooth d₀ w)) =
        (fun j ↦ lam j * sphereWeightedPairing (b j).density
          (SphereEnergySmooth.toSmooth d₀ (u j)) (SphereEnergySmooth.toSmooth d₀ w)) := by
      funext j
      rw [sphereDirichletForm_symm (b j).tensor (b j).symm]
      have h := (intrinsic_green_eigenfunction_test (b j).tensor (b j).smooth (b j).symm
        (b j).pos (b j).density (hb j) (b j).positive
        (SphereEnergySmooth.toSmooth d₀ w) (SphereEnergySmooth.toSmooth d₀ (u j))
        (SphereEnergySmooth.toSmooth d₀ w).property (SphereEnergySmooth.toSmooth d₀ (u j)).property
        (lam j) (he j)).2.2
      simpa only [sphereDirichletForm,sphereWeightedPairing_symm (b j).density
        (SphereEnergySmooth.toSmooth d₀ w) (SphereEnergySmooth.toSmooth d₀ (u j))] using h
    apply tendsto_nhds_unique hlim.1
    rw [hident]
    exact hlam.mul hlim.2
  intro w
  apply (sphereEnergyToCompletion_dense d₀).induction_on
    (p := fun w ↦ sphereCompletedDirichlet d₀ z w =
      lam₀ * inner ℝ (sphereEnergyL2Map d₀ z) (sphereEnergyL2Map d₀ w)) w
  · apply isClosed_eq
    · exact (continuous_const.inner continuous_id).sub
        (continuous_const.inner (sphereEnergyL2Map d₀).continuous)
    · fun_prop
  · exact htest

end
end Yau.Target

end OAI
