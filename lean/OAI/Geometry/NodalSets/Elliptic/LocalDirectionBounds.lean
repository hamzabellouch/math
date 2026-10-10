import OAI.Geometry.NodalSets.Waves.LocalCompactWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem original_direction_bounds : ∃ cs > 0, ∃ ce > 0, ∃ Ce > 0,
    ∀ t : a.cover.Parameter,
      (∀ v, g (coverSourceCenter a.cover t) (metricGradient g S (coverSourceCenter a.cover t)) v = 0 →
        cs*‖v‖^2 ≤ transverseEnergy (g (coverSourceCenter a.cover t)) (a.cover.triple.q t) v) ∧
      ∀ j, ce ≤ sourceDirectionEta (g (coverSourceCenter a.cover t))
        (sourceHessian g S (coverSourceCenter a.cover t)) (metricGradient g S (coverSourceCenter a.cover t))
        (a.cover.triple.q t j) ∧
        sourceDirectionEta (g (coverSourceCenter a.cover t))
          (sourceHessian g S (coverSourceCenter a.cover t)) (metricGradient g S (coverSourceCenter a.cover t))
          (a.cover.triple.q t j) ≤ Ce := by
  let y := coverSourceCenter a.cover
  have hy := continuous_coverSourceCenter a.cover
  have hp := (metricGradient_continuous a.G a.smooth_G a.positive_G a.A a.smooth_A).comp hy
  have hH := (sourceHessian_continuous a.G a.smooth_G a.positive_G a.A a.smooth_A).comp hy
  have hn (t : a.cover.Parameter) : metricGradient a.G a.A (y t) ≠ 0 :=
    a.nonzero_gradient _ (a.cover.center t).property
  obtain ⟨cs,hcs,hspan⟩ := uniform_transverse_spanning (a.G ∘ y) (a.smooth_G.continuous.comp hy)
    (fun t ↦ a.positive_G _) (metricGradient a.G a.A ∘ y) hp hn
    a.cover.triple.q a.cover.triple.continuous_q a.cover.triple.independent a.cover.triple.perpendicular
  obtain ⟨ce,hce,Ce,hCe,heta⟩ := uniform_direction_strictness (a.G ∘ y) (sourceHessian a.G a.A ∘ y)
    (a.smooth_G.continuous.comp hy) hH (fun t ↦ a.positive_G _)
    (metricGradient a.G a.A ∘ y) hp hn a.cover.triple
  refine ⟨cs,hcs,ce,hce,Ce,hCe,?_⟩
  intro t
  obtain ⟨hge,_,hae⟩ := a.germ (y t) (a.centers_E (a.cover.center t).property)
  have hg0 := hge.self_of_nhds
  have hp0 := (metricGradient_eventuallyEq hge hae).self_of_nhds
  have hH0 := (sourceHessian_eventuallyEq hge hae).self_of_nhds
  have hspan' := hspan t
  have heta' := heta t
  dsimp only [Function.comp_def] at hspan' heta'
  rw [hg0,hp0] at hspan'
  rw [hg0,hp0,hH0] at heta'
  exact ⟨hspan',heta'⟩

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
