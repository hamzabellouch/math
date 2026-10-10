import OAI.Geometry.NodalSets.Charts.SphereFiniteNormVariationalLimit
import OAI.Geometry.NodalSets.Charts.SphereUniformEnergyRepresentative
import OAI.Geometry.NodalSets.Charts.SphereVariationalContinuousRegularity

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter Metric Yau.Geometry Yau.Analysis
open scoped ContDiff Topology
noncomputable section
local instance sphereC1IntrinsicMeasurable : MeasurableSpace Base := borel Base
local instance sphereC1IntrinsicBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_finite_norm_C1_intrinsic_limit
    (P : Finset Base) (r : ℝ) (hr : r ≤ 1)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ ball (0 : Yau.Jets.Coord) r,
      sphereChartCoordMap p y=x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (b : ℕ → SphereEnergyData)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density)
    (u : ℕ → SphereEnergySmooth d) (v : Base → ℝ) (hv : Continuous v) (hne : v ≠ 0)
    (ht : TendstoUniformly (fun j ↦ (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)) v atTop)
    (hjet : ∀ p ∈ P, ∀ i : Fin 4,
      TendstoUniformlyOn
        (fun j ↦ partialJet ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) [i])
        (partialJet (v ∘ sphereChartCoordMap p) [i]) atTop (ball 0 r))
    (hcoeff : Tendsto (fun j ↦ sphereCoefficientDistance P 0
      d.tensor d.density (b j).tensor (b j).density) atTop (𝓝 0))
    (lam : ℕ → ℝ) (lam₀ : ℝ) (hlam : Tendsto lam atTop (𝓝 lam₀))
    (he : ∀ j p y, -intrinsicWeightedChartOperator (b j).tensor (b j).density
      (SphereEnergySmooth.toSmooth d (u j)) p y =
        lam j * (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)
          ((extChartAt (𝓡 4) p).symm y)) :
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧
      ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        lam₀ * v ((extChartAt (𝓡 4) p).symm y) := by
  have hcore : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm y=x := by
    intro x
    obtain ⟨p,hp,y,hy,hyx⟩ := hcover x
    exact ⟨p,hp,seedCoordEquiv y,⟨y,(closedBall_subset_closedBall hr) (ball_subset_closedBall hy),rfl⟩,hyx⟩
  obtain ⟨z,hz,_,ha⟩ := sphere_C1_energy_limit_representative d P r hcover u v hv ht hjet
  exact sphere_variational_continuous_regularity d hd z lam₀ v hv hne ha
    (sphere_finite_norm_variational_limit P hcore d hd b hb u z hz hcoeff lam lam₀ hlam he)

end
end Yau.Target

end OAI
