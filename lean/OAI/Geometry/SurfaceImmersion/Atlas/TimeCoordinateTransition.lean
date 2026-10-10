import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceArcTimeCoordinates

namespace OAI

/-! Two actual charts using the same longitudinal function have a
nonzero transverse transition derivative and preserve the time differential. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem time_coordinate_transition (c d : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    (hds : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ d d.source)
    (hdi : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ d.symm d.target)
    {F : M → ℝ} (hcF : ∀ x ∈ c.source, c x 1 = F x)
    (hdF : ∀ x ∈ d.source, d x 1 = F x)
    {x : M} (hxc : x ∈ c.source) (hxd : x ∈ d.source) :
    let L := fderiv ℝ (d ∘ c.symm) (c x)
    Function.Bijective L ∧ (∀ v : Base, L v 1 = v 1) ∧ L ![1,0] 0 ≠ 0 := by
  let L := fderiv ℝ (d ∘ c.symm) (c x)
  have hct := c.map_source hxc
  have hcx := c.left_inv hxc
  have hc' := hci.contMDiffAt (c.open_target.mem_nhds hct)
  have hd' : ContMDiffAt planeModel 𝓘(ℝ,Base) ∞ d (c.symm (c x)) :=
    hcx.symm ▸ hds.contMDiffAt (d.open_source.mem_nhds hxd)
  have hcomp : ContDiffAt ℝ ∞ (d ∘ c.symm) (c x) := (hd'.comp (c x) hc').contDiffAt
  have hcDiff : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hdDiff : d.MDifferentiable planeModel 𝓘(ℝ,Base) :=
    ⟨hds.mdifferentiableOn (by simp),hdi.mdifferentiableOn (by simp)⟩
  have hL : Function.Bijective L := by
    dsimp [L]
    rw [← mfderiv_eq_fderiv,mfderiv_comp (c x) (hd'.mdifferentiableAt (by simp))
      (hc'.mdifferentiableAt (by simp))]
    exact (hdDiff.mfderiv_bijective (hcx.symm ▸ hxd)).comp (hcDiff.mfderiv_bijective hct)
  have hnear : ∀ᶠ y in 𝓝 (c x), y ∈ c.target ∧ c.symm y ∈ d.source := by
    filter_upwards [c.open_target.mem_nhds hct,
      c.symm.continuousAt hct |>.eventually (d.open_source.mem_nhds (hcx.symm ▸ hxd))] with y hy hz
    exact ⟨hy,hz⟩
  have he : (fun y : Base => d (c.symm y) 1) =ᶠ[𝓝 (c x)] fun y => y 1 := by
    filter_upwards [hnear] with y hy
    rw [hdF _ hy.2,← hcF _ (c.map_target hy.1),c.right_inv hy.1]
  have hproj := (ContinuousLinearMap.proj (1:Fin 2) : Base →L[ℝ] ℝ).hasFDerivAt.comp
    (c x) (hcomp.differentiableAt (by simp)).hasFDerivAt
  have hsecond : ∀ v : Base, L v 1 = v 1 := by
    intro v
    have heq := congrArg (fun A : Base →L[ℝ] ℝ => A v) (hproj.fderiv.symm.trans he.fderiv_eq)
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (1:Fin 2) (c x)).fderiv] at heq
    exact heq
  refine ⟨hL,hsecond,?_⟩
  intro hz
  have hz' : L (![1,0] : Base) = 0 := by
    ext i
    fin_cases i
    · exact hz
    · simpa using hsecond ![1,0]
  have hv := hL.1 (hz'.trans (map_zero L).symm)
  have hv0 := congrFun hv 0
  norm_num at hv0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
