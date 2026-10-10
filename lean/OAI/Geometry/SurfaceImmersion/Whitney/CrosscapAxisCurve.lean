import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapPairCoordinates

namespace OAI

/-! The kernel axis of an actual crosscap chart gives a smooth regular
source curve through the singular point, even though its image velocity vanishes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def crosscapAxis : ℝ →L[ℝ] Base :=
  ContinuousLinearMap.pi ![0,ContinuousLinearMap.id ℝ ℝ]

lemma crosscapAxis_apply (t : ℝ) : crosscapAxis t = ![0,t] := by
  ext i
  fin_cases i <;> rfl

lemma crosscapAxis_injective : Function.Injective crosscapAxis := by
  intro x y he
  simpa only [crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun he 1

lemma crosscapAxis_regular (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) crosscapAxis t) := by
  have hd : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ,Base) crosscapAxis t crosscapAxis :=
    crosscapAxis.hasFDerivAt.hasMFDerivAt
  exact hd.mfderiv.symm ▸ crosscapAxis_injective

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

def axisCurve (c : SurfaceCrosscapCoordinates f p) : ℝ → M := c.source.symm ∘ crosscapAxis

theorem axis_curve (c : SurfaceCrosscapCoordinates f p) :
    ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ c.axisCurve U ∧
      (∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) planeModel c.axisCurve t)) ∧
      c.axisCurve 0 = p ∧
      (∀ t ∈ U, c.axisCurve t ∈ c.source.source ∧ c.source (c.axisCurve t) = ![0,t]) := by
  let U := crosscapAxis ⁻¹' c.source.target
  have hU : IsOpen U := c.source.open_target.preimage crosscapAxis.continuous
  have h0 : (0:ℝ) ∈ U := by
    change crosscapAxis 0 ∈ c.source.target
    rw [map_zero,← c.source_center]
    exact c.source.map_source c.source_mem
  have hk : ContMDiff 𝓘(ℝ) 𝓘(ℝ,Base) ∞ crosscapAxis := crosscapAxis.contDiff.contMDiff
  have hs : ContMDiffOn 𝓘(ℝ) planeModel ∞ c.axisCurve U :=
    c.source_inverse_smooth.comp hk.contMDiffOn (fun _ ht => ht)
  have hdif : c.source.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨c.source_inverse_smooth.mdifferentiableOn (by simp),c.source_smooth.mdifferentiableOn (by simp)⟩
  refine ⟨U,hU,h0,hs,?_,?_,?_⟩
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ) planeModel (c.source.symm ∘ crosscapAxis) t)
    rw [mfderiv_comp t
      ((c.source_inverse_smooth.contMDiffAt (c.source.open_target.mem_nhds ht)).mdifferentiableAt (by simp))
      (hk.mdifferentiable (by simp) t)]
    exact (hdif.mfderiv_injective ht).comp (crosscapAxis_regular t)
  · change c.source.symm (crosscapAxis 0) = p
    rw [map_zero,← c.source_center,c.source.left_inv c.source_mem]
  · intro t ht
    exact ⟨c.source.map_target ht,(c.source.right_inv ht).trans (crosscapAxis_apply t)⟩

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
