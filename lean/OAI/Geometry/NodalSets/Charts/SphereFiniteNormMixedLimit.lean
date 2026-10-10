import OAI.Geometry.NodalSets.Charts.SphereFiniteNormQuadraticLimit
import OAI.Geometry.NodalSets.Charts.SphereFormPolarization

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section
local instance sphereMixedLimitMeasurable : MeasurableSpace Base := borel Base
local instance sphereMixedLimitBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_finite_norm_mixed_limit
    (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ y ∈ sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm y=x)
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (b : ℕ → SphereEnergyData)
    (hb : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (b j).density)
    (u v : ℕ → SphereEnergySmooth d) (z w : SphereEnergyHilbert d)
    (hz : Tendsto (fun j ↦ sphereEnergyToCompletion d (u j)) atTop (𝓝 z))
    (hw : Tendsto (fun j ↦ sphereEnergyToCompletion d (v j)) atTop (𝓝 w))
    (hcoeff : Tendsto (fun j ↦ sphereCoefficientDistance P 0
      d.tensor d.density (b j).tensor (b j).density) atTop (𝓝 0)) :
    Tendsto (fun j ↦ sphereDirichletForm (b j).tensor
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (v j)))
      atTop (𝓝 (sphereCompletedDirichlet d z w)) ∧
    Tendsto (fun j ↦ sphereWeightedPairing (b j).density
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (v j)))
      atTop (𝓝 (inner ℝ (sphereEnergyL2Map d z) (sphereEnergyL2Map d w))) := by
  have hsum : Tendsto (fun j ↦ sphereEnergyToCompletion d (u j+v j)) atTop (𝓝 (z+w)) := by
    simpa only [map_add] using hz.add hw
  have hU := sphere_finite_norm_quadratic_limit P hcover d hd b hb u z hz hcoeff
  have hV := sphere_finite_norm_quadratic_limit P hcover d hd b hb v w hw hcoeff
  have hS := sphere_finite_norm_quadratic_limit P hcover d hd b hb (fun j ↦ u j+v j) (z+w) hsum hcoeff
  have hD := ((hS.1.sub hU.1).sub hV.1).div_const 2
  have hW := ((hS.2.sub hU.2).sub hV.2).div_const 2
  have hpol := symmetric_additive_polarization (inner ℝ : SphereWeightedL2 d → SphereWeightedL2 d → ℝ)
    (fun u v ↦ real_inner_comm v u) (fun u v w ↦ inner_add_left u v w) (sphereEnergyL2Map d z) (sphereEnergyL2Map d w)
  constructor
  · rw [sphereCompletedDirichlet_polarization] at hD
    convert hD using 1
    funext j
    exact (sphereDirichletForm_polarization (b j)
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (v j))).symm
  · simp only [map_add,hpol] at hW
    convert hW using 1
    funext j
    exact (sphereWeightedPairing_polarization (b j)
      (SphereEnergySmooth.toSmooth d (u j)) (SphereEnergySmooth.toSmooth d (v j))).symm

end
end Yau.Target

end OAI
