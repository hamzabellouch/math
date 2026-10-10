import OAI.Geometry.NodalSets.Waves.LocalWaveJets
import OAI.Geometry.NodalSets.Waves.WaveHessian

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter
open scoped Topology
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem source_phase_hessian (t : a.cover.Parameter × Fin 3) (u v : Coord) :
    sourceHessian g (fun z ↦ (a.beams.phase t z).re) (coverSourceCenter a.cover t.1) u v =
      sourceHessian g S (coverSourceCenter a.cover t.1) u v -
        sourceDirectionEta (g (coverSourceCenter a.cover t.1)) (sourceHessian g S (coverSourceCenter a.cover t.1))
          (metricGradient g S (coverSourceCenter a.cover t.1)) (a.cover.triple.q t.1 t.2) *
          g (coverSourceCenter a.cover t.1) u v := by
  have h := a.beams.phase_hessian a.smooth_G a.symmetric_G a.positive_G a.smooth_A
    (fun t ↦ a.nonzero_gradient _ (a.cover.center t).property) t u v
  obtain ⟨hG,_,_⟩ := a.germ _ (a.centers_E (a.cover.center t.1).property)
  have he := (sourceHessian_eventuallyEq hG
    (Filter.EventuallyEq.refl (𝓝 (coverSourceCenter a.cover t.1)) (fun z ↦ (a.beams.phase t z).re))).self_of_nhds
  change sourceHessian a.G (fun z ↦ (a.beams.phase t z).re) (coverSourceCenter a.cover t.1) =
    sourceHessian g (fun z ↦ (a.beams.phase t z).re) (coverSourceCenter a.cover t.1) at he
  rw [he,(a.center_identifications t.1).1,(a.center_identifications t.1).2.2.1,
    (a.center_identifications t.1).2.2.2] at h
  exact h

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
