import OAI.Geometry.SurfaceImmersion.Whitney.ActualRelativeFrame
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapFramedRectangle
import OAI.Geometry.SurfaceImmersion.Whitney.NormalizedPairFilling

namespace OAI

/-! The compact formal differential is constructed from the actual map and
its crosscap strip. All exterior derivatives remain exact. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.formal_pair (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ (V : Set Base) (B : Base → Base →L[ℝ] ProjectionTarget 3) (K : Set Base),
      IsOpen V ∧ V ⊆ S.domain ∧
      (∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ V) ∧
      ContDiff ℝ ∞ B ∧ IsCompact K ∧ K ⊆ V ∧ tsupport (B-fderiv ℝ S.model) ⊆ K ∧
      (∀ x ∈ V, Function.Injective (B x)) ∧
      ∀ x ∈ V, Function.Injective (fderiv ℝ S.model x) ↔
        x ≠ crosscapAxis A.arc.start ∧ x ≠ crosscapAxis A.arc.finish := by
  obtain ⟨a,d,r,O,hd,hr,hO,hOD,hrect,hN,haxis,hzeros,hIp,hIq,_hvp,_hvq,hdn,hOF⟩ :=
    S.normalized_defect_rectangle_framed hf
  let N := axisNormalizedDefect d (normalDefect S.model a)
  have hAO : ∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ O := by
    intro t ht
    rw [crosscapAxis_apply]
    exact hrect 0 ⟨by linarith,by linarith⟩ t ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hK : IsCompact (crosscapAxis '' Icc A.arc.start A.arc.finish) :=
    isCompact_Icc.image crosscapAxis.continuous
  obtain ⟨W,hW,hKW,hWO,G,hG,hGW⟩ := CollarVelocity.compact_smooth_extension hK hO
    (by rintro x ⟨t,ht,rfl⟩; exact hAO t ht) hN
  have hAW : ∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ W :=
    fun t ht => hKW ⟨t,ht,rfl⟩
  have hDG : ∀ x ∈ W, fderiv ℝ G x = fderiv ℝ N x :=
    fun x hx => (hGW.eventuallyEq_of_mem (hW.mem_nhds hx)).fderiv_eq
  have hIpG : Function.Bijective (fderiv ℝ G (crosscapAxis A.arc.start)) := by
    rw [hDG _ (hAW _ (left_mem_Icc.mpr A.arc.start_lt_finish.le))]
    exact hIp
  have hIqG : Function.Bijective (fderiv ℝ G (crosscapAxis A.arc.finish)) := by
    rw [hDG _ (hAW _ (right_mem_Icc.mpr A.arc.start_lt_finish.le))]
    exact hIq
  obtain ⟨V,hV,hVW,hAV,hfill⟩ := normalized_pair_frame_filling hG A.arc.start_lt_finish
    (hW.preimage crosscapAxis.continuous) hAW
    (fun t ht => (hGW ht).trans (haxis t (hWO ht))) hIpG hIqG hW hAW
  have hVO : V ⊆ O := hVW.trans hWO
  obtain ⟨B,K,hB,hK,hKV,hBs,hBI⟩ := actual_relative_frame S.model_smooth a hd hV
    (hVO.trans hOF) (fun x hx => hdn x (hVO hx)) (hGW.mono hVW) hfill
  refine ⟨V,B,K,hV,hVO.trans hOD,hAV,hB,hK,hKV,hBs,hBI,?_⟩
  intro x hx
  have hF := hOF (hVO hx)
  have hbase := normalDefect_immersion_iff S.model a x (normalFrameDomain_nonzero hF)
    (normalFrameDomain_transverse hF)
  have he : N x = 0 ↔ normalDefect S.model a x = 0 := by
    change (planeComplexFrame (d (x 1))).inverse (normalDefect S.model a x) = 0 ↔ _
    constructor
    · intro he
      exact (planeComplexFrame_invertible (hdn x (hVO hx))).inverse.injective
        (he.trans (map_zero _).symm)
    · intro he
      rw [he,map_zero]
  exact hbase.trans ((not_congr he).symm.trans ((not_congr (hzeros x (hVO hx))).trans not_or))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
