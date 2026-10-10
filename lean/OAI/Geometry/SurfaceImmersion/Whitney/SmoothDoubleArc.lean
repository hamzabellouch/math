import OAI.Geometry.SurfaceImmersion.Whitney.OrientedDoubleTransition

namespace OAI

/-! A compact smooth double arc retains the final chart germ. This is
precisely the data needed to continue it through the next chart of a finite cover. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

structure SmoothDoubleArc (f : M → ProjectionTarget 3) where
  arc : SmoothCompactArc (planeModel.prod planeModel) (M × M)
  lift : ℝ → surfaceDoublePairs f
  curve_eq : ∀ t, arc.curve t = (lift t).val
  tail : SmoothDoubleChart f
  sign : ℝ
  sign_eq : sign = 1 ∨ sign = -1
  parameter : ℝ ≃ₜ ℝ
  parameter_smooth : ContDiff ℝ ∞ parameter
  inverse_smooth : ContDiff ℝ ∞ parameter.symm
  parameter_mono : StrictMono parameter
  tail_germ : lift =ᶠ[𝓝 arc.finish] (fun t => tail.coord.symm (sign*parameter t))
  tail_target : sign*parameter arc.finish ∈ tail.coord.target

namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem smooth_double_arc (c : SmoothDoubleChart f) {γ : ℝ → surfaceDoublePairs f}
    {a b : ℝ} (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Icc a b)) (hsource : MapsTo γ (Icc a b) c.coord.source) :
    ∃ P : SmoothDoubleArc f,
      P.arc.curve '' Icc P.arc.start P.arc.finish = (fun t => (γ t).val) '' Icc a b ∧
      P.lift P.arc.start = γ a ∧ P.lift P.arc.finish = γ b := by
  obtain ⟨A,s,hs,hcurve,hstart,hfinish,himage,hleft,hright⟩ :=
    c.oriented_arc hab hγ hinj hsource
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have htarget : s*A.finish ∈ c.coord.target := by
    rw [hfinish,← mul_assoc,hss,one_mul]
    exact c.coord.map_source (hsource (right_mem_Icc.mpr hab.le))
  let P : SmoothDoubleArc f := ⟨A,(fun t => c.coord.symm (s*t)),
    (fun t => congrFun hcurve t),c,s,hs,Homeomorph.refl ℝ,
    contDiff_id,contDiff_id,strictMono_id,Filter.Eventually.of_forall (fun _ => rfl),htarget⟩
  refine ⟨P,himage,?_,?_⟩
  · apply Subtype.val_injective
    exact (P.curve_eq P.arc.start).symm.trans hleft
  · apply Subtype.val_injective
    exact (P.curve_eq P.arc.finish).symm.trans hright

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
