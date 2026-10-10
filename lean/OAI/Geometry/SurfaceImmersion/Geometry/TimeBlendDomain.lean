import OAI.Geometry.SurfaceImmersion.Geometry.SurfaceBlendExterior

namespace OAI

/-! An open domain for joining time charts using an exact scalar cutoff. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

def timeBlendDomain (c d : SurfaceTimeChart F) (l r : ℝ) : Set M :=
  (c.coord.source ∩ F ⁻¹' Iio l) ∪ (c.coord.source ∩ d.coord.source) ∪
    (d.coord.source ∩ F ⁻¹' Ioi r)

lemma timeBlendDomain_open (c d : SurfaceTimeChart F) (l r : ℝ)
    (hF : Continuous F) : IsOpen (timeBlendDomain c d l r) :=
  ((c.coord.open_source.inter (isOpen_Iio.preimage hF)).union
    (c.coord.open_source.inter d.coord.open_source)).union
      (d.coord.open_source.inter (isOpen_Ioi.preimage hF))

lemma timeBlendDomain_smooth (c d : SurfaceTimeChart F) {l r : ℝ} (hlr : l < r)
    (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F) :
    ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ (surfaceTimeBlend c d (timeCutoff l r))
      (timeBlendDomain c d l r) := by
  intro x hx
  rcases hx with (⟨hc,ht⟩ | ⟨hc,hd⟩) | ⟨hd,ht⟩
  · exact ((c.smooth.contMDiffAt (c.coord.open_source.mem_nhds hc)).congr_of_eventuallyEq
      (surfaceTimeBlend_left_germ c d hF.continuous hlr ht)).contMDiffWithinAt
  · exact ((surfaceTimeBlend_smooth c d (timeCutoff_smooth l r) hF).contMDiffAt
      ((c.coord.open_source.inter d.coord.open_source).mem_nhds ⟨hc,hd⟩)).contMDiffWithinAt
  · exact ((d.smooth.contMDiffAt (d.coord.open_source.mem_nhds hd)).congr_of_eventuallyEq
      (surfaceTimeBlend_right_germ c d hF.continuous hlr ht)).contMDiffWithinAt

lemma timeBlendDomain_time (c d : SurfaceTimeChart F) {l r : ℝ} (hlr : l < r)
    {x : M} (hx : x ∈ timeBlendDomain c d l r) :
    surfaceTimeBlend c d (timeCutoff l r) x 1 = F x := by
  rcases hx with (⟨hc,ht⟩ | ⟨hc,hd⟩) | ⟨hd,ht⟩
  · rw [surfaceTimeBlend_zero c d (timeCutoff_zero hlr ht.le)]
    exact c.time x hc
  · exact surfaceTimeBlend_time c d hc hd
  · rw [surfaceTimeBlend_one c d (timeCutoff_one hlr ht.le)]
    exact d.time x hd

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
