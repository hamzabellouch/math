import Mathlib.Topology.Sequences
import OAI.Geometry.NodalSets.Charts.SphereChartValueMap

namespace OAI

namespace Yau.Target
open Filter Set
open scoped Topology
noncomputable section

theorem sphere_chart_strong_approximation (d : SphereEnergyData) (z : SphereEnergyHilbert d) :
    ∃ u : ℕ → SphereEnergySmooth d,
      Tendsto (fun n ↦ sphereEnergyToCompletion d (u n)) atTop (𝓝 z) ∧
      ∀ p : Base,
        Tendsto (fun n ↦ sphereChartValueMap d p (sphereEnergyL2Linear d (u n))) atTop
          (𝓝 (sphereChartValueMap d p (sphereEnergyL2Map d z))) ∧
        ∀ i : Fin 4, Tendsto (fun n ↦ sphereChartDerivativeLinear d p i (u n)) atTop
          (𝓝 (sphereChartDerivativeMap d p i z)) := by
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp ((sphereEnergyToCompletion_dense d) z)
  choose u hu using hv
  have hlim' : Tendsto (fun n ↦ sphereEnergyToCompletion d (u n)) atTop (𝓝 z) := by
    simpa only [hu] using hlim
  refine ⟨u,hlim',?_⟩
  intro p
  constructor
  · have h := (sphereChartValueMap d p).continuous.continuousAt.tendsto.comp
      ((sphereEnergyL2Map d).continuous.continuousAt.tendsto.comp hlim')
    simpa only [Function.comp_def,sphereEnergyL2Map_coe] using h
  · intro i
    have h := (sphereChartDerivativeMap d p i).continuous.continuousAt.tendsto.comp hlim'
    simpa only [Function.comp_def,sphereChartDerivativeMap_coe] using h

end
end Yau.Target

end OAI
