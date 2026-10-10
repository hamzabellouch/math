import OAI.Geometry.SurfaceImmersion.Whitney.AdvancingCornerParameters
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledGraphJoin
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcChartTransport

namespace OAI

/-! An advancing corner has an actual regular embedded surface rounding in
any prescribed open neighborhood, with the original branch germs at both ends. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

theorem advancing_corner_arc (C : RegularPathCornerChart γ t)
    (hl : StrictMono C.leftParameter) (hr : StrictMono C.rightParameter)
    {O : Set M} (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ (P : SmoothCompactArc planeModel M) (a b l r : ℝ),
      P.start = -2 ∧ P.finish = 2 ∧ 0 < b ∧
      C.lower < l ∧ l < t ∧ t < r ∧ r < C.upper ∧
      P.curve P.start = γ.extend l ∧ P.curve P.finish = γ.extend r ∧
      MapsTo P.curve (Icc P.start P.finish) O ∧
      (∀ s ∈ Icc P.start P.finish,
        P.curve s ∈ C.chart.source ∧ C.chart (P.curve s) =
          scaledGraphJoin C.leftGraph C.rightGraph a b s) ∧
      P.curve =ᶠ[𝓝 P.start]
        (fun s => γ.extend (C.leftParameter.symm (a+b*s))) ∧
      P.curve =ᶠ[𝓝 P.finish]
        (fun s => γ.extend (C.rightParameter.symm (a+b*s))) := by
  let V := C.chart.target ∩ C.chart.symm ⁻¹' O
  have hV : IsOpen V := C.chart.continuousOn_symm.isOpen_inter_preimage C.chart.open_target hO
  have htS := (C.left_chart t ⟨C.lower_lt.le,le_rfl⟩).1
  have htV : C.chart (γ.extend t) ∈ V :=
    ⟨C.chart.map_source htS,by simpa only [mem_preimage,C.chart.left_inv htS] using htO⟩
  let a := C.leftParameter t
  obtain ⟨b,hb,htraceL,htraceR,hblend⟩ := C.advancing_corner_parameters hl hr hV htV
  obtain ⟨Q,hQs,hQf,hQc,hQL,hQR⟩ := scaled_graph_join_arc C.left_smooth C.right_smooth a hb.ne'
  have hQV : MapsTo Q.curve (Icc Q.start Q.finish) V := by
    intro s hs
    rw [hQc,scaledGraphJoin_eq_blend]
    apply hblend s (by simpa only [hQs,hQf] using hs)
    exact centeredSmoothStep_bounds s
  obtain ⟨P,hPs,hPf,hPc,hcoord⟩ := smooth_arc_chart_transport Q C.chart
    C.chart_smooth C.inverse_smooth (fun s hs => (hQV hs).1)
  have hPs' : P.start = -2 := hPs.trans hQs
  have hPf' : P.finish = 2 := hPf.trans hQf
  obtain ⟨l,hlt,hel⟩ := htraceL
  obtain ⟨r,hrt,her⟩ := htraceR
  have hLn : ∀ᶠ s in 𝓝 P.start,
      a+b*s ∈ C.leftParameter '' Ioo C.lower t := by
    have he : a+b*P.start = a-2*b := by rw [hPs']; ring
    apply (show Continuous (fun s : ℝ => a+b*s) by fun_prop).continuousAt.preimage_mem_nhds
    rw [he]
    exact (C.leftParameter.isOpenMap _ isOpen_Ioo).mem_nhds ⟨l,hlt,hel⟩
  have hRn : ∀ᶠ s in 𝓝 P.finish,
      a+b*s ∈ C.rightParameter '' Ioo t C.upper := by
    have he : a+b*P.finish = a+2*b := by rw [hPf']; ring
    apply (show Continuous (fun s : ℝ => a+b*s) by fun_prop).continuousAt.preimage_mem_nhds
    rw [he]
    exact (C.rightParameter.isOpenMap _ isOpen_Ioo).mem_nhds ⟨r,hrt,her⟩
  have hPL : P.curve =ᶠ[𝓝 P.start]
      (fun s => γ.extend (C.leftParameter.symm (a+b*s))) := by
    have hQL' : Q.curve =ᶠ[𝓝 P.start] (fun s => ![a+b*s,C.leftGraph (a+b*s)]) := by
      simpa only [hPs] using hQL
    filter_upwards [hQL',hLn] with s hs hxs
    rw [hPc]
    change C.chart.symm (Q.curve s) = _
    rw [hs]
    exact (C.left_graph_realized (image_mono Ioo_subset_Icc_self hxs)).2
  have hPR : P.curve =ᶠ[𝓝 P.finish]
      (fun s => γ.extend (C.rightParameter.symm (a+b*s))) := by
    have hQR' : Q.curve =ᶠ[𝓝 P.finish] (fun s => ![a+b*s,C.rightGraph (a+b*s)]) := by
      simpa only [hPf] using hQR
    filter_upwards [hQR',hRn] with s hs hxs
    rw [hPc]
    change C.chart.symm (Q.curve s) = _
    rw [hs]
    exact (C.right_graph_realized (image_mono Ioo_subset_Icc_self hxs)).2
  refine ⟨P,a,b,l,r,hPs',hPf',hb,hlt.1,hlt.2,hrt.1,hrt.2,?_,?_,?_,?_,hPL,hPR⟩
  · have he : a+b*P.start = a-2*b := by rw [hPs']; ring
    rw [hPL.eq_of_nhds,he,← hel,C.leftParameter.symm_apply_apply]
  · have he : a+b*P.finish = a+2*b := by rw [hPf']; ring
    rw [hPR.eq_of_nhds,he,← her,C.rightParameter.symm_apply_apply]
  · intro s hs
    have hsQ : s ∈ Icc Q.start Q.finish := by simpa only [hPs,hPf] using hs
    rw [hPc]
    exact (hQV hsQ).2
  · intro s hs
    have hc := hcoord s (P.interval_subset hs)
    rw [hQc] at hc
    exact hc

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
