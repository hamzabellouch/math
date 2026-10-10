import OAI.Geometry.NodalSets.Elliptic.CorrugationOldData
import OAI.Geometry.NodalSets.Persistence.LocalAdmissibilityPersistence

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem source_admissibility_neighborhood
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    {D U : Set Coord} (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hadm : ∀ x ∈ D, metricGradient g S x ≠ 0 ∧
      ∃ t : Coord, g x t t = 1 ∧ g x (metricGradient g S x) t = 0 ∧
        0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x) +
          (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x t t) :
    ∃ V : Set Coord, IsOpen V ∧ D ⊆ V ∧ V ⊆ U ∧
      ∀ x ∈ V, metricGradient g S x ≠ 0 ∧
        ∃ t : Coord, g x t t = 1 ∧ g x (metricGradient g S x) t = 0 ∧
          0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x) +
            (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x t t := by
  let A : Set Coord := {x | x ∈ U ∧ metricGradient g S x ≠ 0 ∧
    ∃ t : Coord, g x t t = 1 ∧ g x (metricGradient g S x) t = 0 ∧
      0 < sourceHessian g S x (metricGradient g S x) (metricGradient g S x) +
        (g x (metricGradient g S x) (metricGradient g S x)+4)*sourceHessian g S x t t}
  refine ⟨interior A,isOpen_interior,?_,fun x hx ↦ (interior_subset hx).1,
    fun x hx ↦ (interior_subset hx).2⟩
  intro x hx
  obtain ⟨hn,t,htu,hpt,hstr⟩ := hadm x hx
  have hgx := hg.contDiffAt (hU.mem_nhds (hDU hx))
  have hSx := hS.contDiffAt (hU.mem_nhds (hDU hx))
  have he := admissibility_eventually g (sourceHessian g S) (metricGradient g S) x
    hgx.continuousAt (localMetricHessian_continuousAt g S x hgx hSx (hp x (hDU hx)))
    (localMetricGradient_continuousAt g S x hgx.continuousAt hSx (hp x (hDU hx)))
    (hp x (hDU hx) _ hn) t hpt htu hstr
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hU.mem_nhds (hDU hx),he] with y hy ha
  obtain ⟨hn,u,hpu,hu,hs⟩ := ha
  exact ⟨hy,hn,u,hu,hpu,hs⟩

end
end Yau.Geometry

end OAI
