import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleArcAppend
import OAI.Geometry.SurfaceImmersion.Whitney.OrderedArcSeparation

namespace OAI

/-! The actual extension step for an embedded topological double arc:
append the next chart segment and retain the exact image and endpoints. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3}

theorem extend_smooth_double_arc {γ : ℝ → surfaceDoublePairs f} {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (hγ : ContinuousOn γ (Icc a c))
    (hi : InjOn γ (Icc a c)) (P : SmoothDoubleArc f)
    (hP : P.arc.curve '' Icc P.arc.start P.arc.finish = (fun t => (γ t).val) '' Icc a b)
    (hleft : P.lift P.arc.start = γ a) (hright : P.lift P.arc.finish = γ b)
    (d : SmoothDoubleChart f) (hd : MapsTo γ (Icc b c) d.coord.source) :
    ∃ R : SmoothDoubleArc f,
      R.arc.curve '' Icc R.arc.start R.arc.finish = (fun t => (γ t).val) '' Icc a c ∧
      R.lift R.arc.start = γ a ∧ R.lift R.arc.finish = γ c := by
  have hsub : Icc b c ⊆ Icc a c := Icc_subset_Icc hab.le le_rfl
  obtain ⟨Q,s,hs,hQ,hQs,hQf,hQi,hQl,hQr⟩ :=
    d.oriented_arc hbc (hγ.mono hsub) (hi.mono hsub) hd
  have hcross := ordered_arc_images_separated hab.le hbc.le
    (Subtype.val_injective.comp_injOn hi) P.arc Q hP hQi hQl
  have hss : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hsource : P.lift P.arc.finish ∈ d.coord.source := by
    rw [hright]
    exact hd (left_mem_Icc.mpr hbc.le)
  have hstart : Q.start = s*d.coord (P.lift P.arc.finish) := by rw [hright]; exact hQs
  have hfinish : s*Q.finish ∈ d.coord.target := by
    rw [hQf,← mul_assoc,hss,one_mul]
    exact d.coord.map_source (hd (right_mem_Icc.mpr hbc.le))
  obtain ⟨R,hRi,hRl,hRr⟩ := P.append_chart Q d hs (fun t => congrFun hQ t)
    hsource hstart hfinish hcross
  refine ⟨R,?_,hRl.trans hleft,?_⟩
  · rw [hRi,hP,hQi,← Set.image_union,Icc_union_Icc_eq_Icc hab.le hbc.le]
  · apply Subtype.val_injective
    rw [hRr]
    exact (congrFun hQ Q.finish).symm.trans hQr

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
