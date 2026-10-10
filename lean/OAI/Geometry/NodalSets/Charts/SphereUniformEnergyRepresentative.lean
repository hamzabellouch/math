import OAI.Geometry.NodalSets.Charts.SphereC1EnergyConvergence
import OAI.Geometry.NodalSets.Charts.SphereEnergyL2Map
import OAI.Geometry.NodalSets.Charts.SphereUniformDensityPairingLimit

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Analysis MeasureTheory Filter Metric
open scoped ContDiff Topology
noncomputable section
local instance sphereUniformEnergyMeasurable : MeasurableSpace Base := borel Base
local instance sphereUniformEnergyBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_uniform_weighted_L2_convergence (d : SphereEnergyData)
    (w : ℕ → Base → ℝ) (v : Base → ℝ) (hw : ∀ j, Continuous (w j)) (hv : Continuous v)
    (ht : TendstoUniformly w v atTop) :
    Tendsto (fun j ↦ sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) (w j) (hw j))
      atTop (𝓝 (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv)) := by
  have hconst : TendstoUniformly (fun _j : ℕ ↦ v) v atTop := by
    intro s hs
    exact Eventually.of_forall (fun _ _ ↦ refl_mem_uniformity hs)
  have hrho : TendstoUniformly (fun _j : ℕ ↦ d.density) d.density atTop := by
    intro s hs
    exact Eventually.of_forall (fun _ _ ↦ refl_mem_uniformity hs)
  have hdiff : TendstoUniformly (fun j x ↦ w j x-v x) (fun _x ↦ (0:ℝ)) atTop := by
    have hh := ht.sub hconst
    change TendstoUniformly (fun j x ↦ w j x-v x) (fun x ↦ v x-v x) atTop at hh
    simpa only [sub_self] using hh
  have hp := sphereWeightedPairing_uniform_density_limit (fun _j : ℕ ↦ d.density) d.density
    (fun _ ↦ d.continuous) d.continuous hrho
    (fun j x ↦ w j x-v x) (fun j x ↦ w j x-v x) (fun _ ↦ 0) (fun _ ↦ 0)
    (fun j ↦ (hw j).sub hv) (fun j ↦ (hw j).sub hv) continuous_const continuous_const hdiff hdiff
  have hp0 : sphereWeightedPairing d.density (fun _ ↦ 0) (fun _ ↦ 0)=0 := by
    simp only [sphereWeightedPairing,mul_zero,integral_zero]
  rw [hp0] at hp
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [hp.eventually (gt_mem_nhds (sq_pos_of_pos heps))] with j hj
  have heq : sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le)
      (fun x ↦ w j x-v x) ((hw j).sub hv) =
      sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) (w j) (hw j)-
      sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv :=
    MemLp.toLp_sub (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le) (w j) (hw j))
      (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv)
  have hn := sphereWeightedToLp_norm_sq d.density d.continuous (fun x ↦ (d.positive x).le)
    (fun x ↦ w j x-v x) ((hw j).sub hv)
  rw [heq] at hn
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) (w j) (hw j)-
    sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv)]

theorem sphere_C1_energy_limit_representative (d : SphereEnergyData) (P : Finset Base) (r : ℝ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r, sphereChartCoordMap p z=x)
    (u : ℕ → SphereEnergySmooth d) (v : Base → ℝ) (hv : Continuous v)
    (ht : TendstoUniformly (fun j ↦ (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)) v atTop)
    (hjet : ∀ p ∈ P, ∀ i : Fin 4,
      TendstoUniformlyOn
        (fun j ↦ partialJet ((SphereEnergySmooth.toSmooth d (u j) : Base → ℝ) ∘ sphereChartCoordMap p) [i])
        (partialJet (v ∘ sphereChartCoordMap p) [i]) atTop (ball 0 r)) :
    ∃ z : SphereEnergyHilbert d, Tendsto (fun j ↦ sphereEnergyToCompletion d (u j)) atTop (𝓝 z) ∧
      sphereEnergyL2Map d z=sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv ∧
      v =ᵐ[sphereWeightedMeasure d.density] (sphereEnergyL2Map d z : Base → ℝ) := by
  obtain ⟨z,hz⟩ := sphere_C1_energy_completion_limit d P r hcover u v ht hjet
  have hmap := ((sphereEnergyL2Map d).continuous.tendsto z).comp hz
  change Tendsto (fun j ↦ sphereEnergyL2Map d (sphereEnergyToCompletion d (u j))) atTop (𝓝 (sphereEnergyL2Map d z)) at hmap
  simp only [sphereEnergyL2Map_coe] at hmap
  have hLp := sphere_uniform_weighted_L2_convergence d
    (fun j ↦ (SphereEnergySmooth.toSmooth d (u j) : Base → ℝ)) v
    (fun j ↦ (SphereEnergySmooth.toSmooth d (u j)).property.continuous) hv ht
  have heq : sphereEnergyL2Map d z=sphereWeightedToLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv :=
    tendsto_nhds_unique hmap hLp
  refine ⟨z,hz,heq,?_⟩
  rw [heq]
  exact (sphereWeighted_memLp d.density d.continuous (fun x ↦ (d.positive x).le) v hv).coeFn_toLp.symm

end
end Yau.Target

end OAI
