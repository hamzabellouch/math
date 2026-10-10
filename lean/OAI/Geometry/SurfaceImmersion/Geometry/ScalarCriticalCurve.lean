import OAI.Geometry.SurfaceImmersion.Atlas.OneFiberChart
import OAI.Geometry.SurfaceImmersion.Geometry.LocalNullImage

namespace OAI

/-! Near a nonzero derivative, the zero set is a curve. The critical
values of a scalar function restricted to this curve are null. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem scalar_critical_curve_local_null {f g : Base → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (p : Base)
    (hdg : fderiv ℝ g p ≠ 0) :
    ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧
      volume (f '' ({x | fderiv ℝ f x = 0 ∧ g x = 0} ∩ U)) = 0 := by
  have hs : Function.Surjective (fderiv ℝ g p) :=
    surjective_of_nonzero_of_finrank_eq_one (by simp : Module.finrank ℝ ℝ = 1)
      (show (fderiv ℝ g p).toLinearMap ≠ 0 from fun h => hdg (by ext x; exact congrArg (fun L => L x) h))
  obtain ⟨e,hpe,he,hsm,hinv⟩ := one_fiber_submersion_chart (by simp [Base]) hg p hs
  let τ : ℝ → ℝ × ℝ := fun t => (0,t)
  have hτ : ContDiff ℝ ∞ τ := contDiff_const.prodMk contDiff_id
  let h : ℝ → ℝ := f ∘ e.symm ∘ τ
  let S : Set ℝ := {t | τ t ∈ e.target ∧ fderiv ℝ f (e.symm (τ t)) = 0}
  have hh (t : ℝ) (ht : t ∈ S) : HasFDerivAt h (0 : ℝ →L[ℝ] ℝ) t := by
    have hi : DifferentiableAt ℝ e.symm (τ t) :=
      (hinv.contDiffAt (e.open_target.mem_nhds ht.1)).differentiableAt (by simp)
    have hf0 : HasFDerivAt f (0 : Base →L[ℝ] ℝ) (e.symm (τ t)) := by
      simpa only [ht.2] using (hf.differentiable (by simp) (e.symm (τ t))).hasFDerivAt
    simpa only [ContinuousLinearMap.zero_comp] using
      hf0.comp t (hi.hasFDerivAt.comp t (hτ.differentiable (by simp) t).hasFDerivAt)
  have hn : volume (h '' S) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun _ => (0 : ℝ →L[ℝ] ℝ))
      (fun t ht => (hh t ht).hasFDerivWithinAt) (by simp)
  refine ⟨e.source,e.open_source,hpe,measure_mono_null ?_ hn⟩
  rintro y ⟨x,⟨hx,hxe⟩,rfl⟩
  have ht : τ ((e x).2) = e x := by
    apply Prod.ext
    · exact (he x |>.trans hx.2).symm
    · rfl
  refine ⟨(e x).2,?_,?_⟩
  · change τ ((e x).2) ∈ e.target ∧ fderiv ℝ f (e.symm (τ ((e x).2))) = 0
    rw [ht,e.left_inv hxe]
    exact ⟨e.map_source hxe,hx.1⟩
  · change f (e.symm (τ ((e x).2))) = f x
    rw [ht,e.left_inv hxe]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
