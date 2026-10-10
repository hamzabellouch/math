import OAI.Geometry.SurfaceImmersion.Atlas.TimeCoordinateBlend
import OAI.Geometry.SurfaceImmersion.Whitney.ArcTimeChartPartition

namespace OAI

/-! The actual blend of surface time charts is regular at every common
axis point where their transverse transition is positive. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] {F : M → ℝ}

def surfaceTimeBlend (c d : SurfaceTimeChart F) (χ : ℝ → ℝ) (x : M) : Base :=
  (1-χ (F x)) • c.coord x + χ (F x) • d.coord x

lemma surfaceTimeBlend_smooth (c d : SurfaceTimeChart F) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F) :
    ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ (surfaceTimeBlend c d χ)
      (c.coord.source ∩ d.coord.source) := by
  have hw := hχ.contMDiff.comp hF
  exact ((contMDiff_const.sub hw).contMDiffOn.smul (c.smooth.mono inter_subset_left)).add
    (hw.contMDiffOn.smul (d.smooth.mono inter_subset_right))

theorem surfaceTimeBlend_regular (c d : SurfaceTimeChart F) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    (x : M) (hxc : x ∈ c.coord.source) (hxd : x ∈ d.coord.source)
    (hagree : d.coord x = c.coord x)
    (hpos : 0 < fderiv ℝ (d.coord ∘ c.coord.symm) (c.coord x) ![1,0] 0)
    (hw : χ (F x) ∈ Icc (0:ℝ) 1) :
    Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) (surfaceTimeBlend c d χ) x) := by
  let H := surfaceTimeBlend c d χ
  let g : Base → Base := d.coord ∘ c.coord.symm
  let η : Base → ℝ := fun z => χ (z 1)
  have hci := c.inverse_smooth.contMDiffAt (c.coord.open_target.mem_nhds (c.coord.map_source hxc))
  have hds : ContMDiffAt planeModel 𝓘(ℝ,Base) ∞ d.coord (c.coord.symm (c.coord x)) :=
    (c.coord.left_inv hxc).symm ▸ d.smooth.contMDiffAt (d.coord.open_source.mem_nhds hxd)
  have hgd : DifferentiableAt ℝ g (c.coord x) := (hds.comp (c.coord x) hci).contDiffAt.differentiableAt (by simp)
  have hη : ContDiff ℝ ∞ η := hχ.comp (contDiff_apply ℝ ℝ (1:Fin 2))
  have hpoint : g (c.coord x) = c.coord x := by dsimp [g]; rw [c.coord.left_inv hxc,hagree]
  have hηweight : η (c.coord x) ∈ Icc (0:ℝ) 1 := by
    change χ (c.coord x 1) ∈ _
    rwa [c.time x hxc]
  have hB := timeCoordinateBlend_regular hgd (hη.differentiable (by simp) _)
    hpoint (time_coordinate_transition c.coord d.coord c.smooth c.inverse_smooth
      d.smooth d.inverse_smooth c.time d.time hxc hxd).2.1 hpos hηweight
  have heq : H ∘ c.coord.symm =ᶠ[𝓝 (c.coord x)] timeCoordinateBlend g η := by
    filter_upwards [c.coord.open_target.mem_nhds (c.coord.map_source hxc)] with z hz
    change (1-χ (F (c.coord.symm z))) • c.coord (c.coord.symm z) +
      χ (F (c.coord.symm z)) • d.coord (c.coord.symm z) = _
    rw [← c.time _ (c.coord.map_target hz),c.coord.right_inv hz]
    rfl
  have hHcx : Function.Bijective (fderiv ℝ (H ∘ c.coord.symm) (c.coord x)) := by
    rw [heq.fderiv_eq]
    exact hB
  have hH : ContMDiffAt planeModel 𝓘(ℝ,Base) ∞ H x :=
    (surfaceTimeBlend_smooth c d hχ hF).contMDiffAt
      ((c.coord.open_source.inter d.coord.open_source).mem_nhds ⟨hxc,hxd⟩)
  have hHc : ContMDiffAt 𝓘(ℝ,Base) 𝓘(ℝ,Base) ∞ (H ∘ c.coord.symm) (c.coord x) :=
    ((c.coord.left_inv hxc).symm ▸ hH).comp (c.coord x) hci
  have hrestore : H =ᶠ[𝓝 x] (H ∘ c.coord.symm) ∘ c.coord := by
    filter_upwards [c.coord.open_source.mem_nhds hxc] with y hy
    change H y = H (c.coord.symm (c.coord y))
    rw [c.coord.left_inv hy]
  have hcD : c.coord.MDifferentiable planeModel 𝓘(ℝ,Base) :=
    ⟨c.smooth.mdifferentiableOn (by simp),c.inverse_smooth.mdifferentiableOn (by simp)⟩
  change Function.Bijective (mfderiv planeModel 𝓘(ℝ,Base) H x)
  rw [hrestore.mfderiv_eq,mfderiv_comp x (hHc.mdifferentiableAt (by simp))
    (hcD.mdifferentiableAt hxc),mfderiv_eq_fderiv]
  exact hHcx.comp (hcD.mfderiv_bijective hxc)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
